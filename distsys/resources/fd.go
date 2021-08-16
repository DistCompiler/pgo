package resources

import (
	"errors"
	"fmt"
	"net"
	"net/rpc"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
)

const (
	failureDetectorTimeout      = 1 * time.Second
	failureDetectorPullInterval = 2 * time.Second
)

// type ArchetypeID distsys.TLAValue

type ArchetypeState int

const (
	uninitialized ArchetypeState = iota
	alive
	failed
	finished
	unknown
)

func (a ArchetypeState) String() string {
	switch a {
	case uninitialized:
		return "uninitialized"
	case alive:
		return "alive"
	case failed:
		return "failed"
	case finished:
		return "finished"
	case unknown:
		return "unknown"
	default:
		return "none"
	}
}

type Monitor struct {
	ListenAddr string

	lock   sync.RWMutex
	states map[distsys.TLAValue]ArchetypeState
}

func NewMonitor(listenAddr string) *Monitor {
	return &Monitor{
		ListenAddr: listenAddr,
		states:     make(map[distsys.TLAValue]ArchetypeState),
	}
}

func (m *Monitor) setState(archetypeID distsys.TLAValue, state ArchetypeState) {
	m.lock.Lock()
	m.states[archetypeID] = state
	m.lock.Unlock()
}

func (m *Monitor) getState(archetypeID distsys.TLAValue) (ArchetypeState, bool) {
	m.lock.RLock()
	state, ok := m.states[archetypeID]
	m.lock.RUnlock()
	return state, ok
}

type WrappedArchetypeFn func() error

func (m *Monitor) RunArchetype(archetypeID distsys.TLAValue, fn WrappedArchetypeFn) error {
	done := make(chan error)
	go func() {
		defer func() {
			if r := recover(); r != nil {
				m.setState(archetypeID, failed)
				done <- fmt.Errorf("archetype %d recovered from panic: %s", archetypeID, r)
			}
		}()

		m.setState(archetypeID, alive)
		err := fn()
		if err == nil {
			m.setState(archetypeID, finished)
		} else {
			m.setState(archetypeID, failed)
		}
		done <- err
	}()
	return <-done
}

func (m *Monitor) ListenAndServe() error {
	rpcServer := &MonitorRPCServer{m: m}
	err := rpc.Register(rpcServer)
	if err != nil {
		return err
	}

	listener, err := net.Listen("tcp", m.ListenAddr)
	if err != nil {
		return err
	}
	rpc.Accept(listener)
	return nil
}

type MonitorRPCServer struct {
	m *Monitor
}

func (rs *MonitorRPCServer) IsAlive(arg distsys.TLAValue, reply *ArchetypeState) error {
	state, ok := rs.m.getState(arg)
	if !ok {
		return errors.New("archetype not found")
	}
	*reply = state
	return nil
}

type FailureDetectorAddressMappingFn func(distsys.TLAValue) string

func FailureDetectorResourceMaker(addressMappingFn FailureDetectorAddressMappingFn, opts ...FailureDetectorOption) distsys.ArchetypeResourceMaker {
	return IncrementalArchetypeMapResourceMaker(func(index distsys.TLAValue) distsys.ArchetypeResourceMaker {
		monitorAddr := addressMappingFn(index)
		return singleFailureDetectorResourceMaker(index, monitorAddr, opts...)
	})
}

type singleFailureDetectorResource struct {
	distsys.ArchetypeResourceLeafMixin
	archetypeID distsys.TLAValue
	monitorAddr string

	timeout      time.Duration
	pullInterval time.Duration

	client *rpc.Client
	reDial bool

	lock  sync.RWMutex
	state ArchetypeState
}

type FailureDetectorOption func(fd *singleFailureDetectorResource)

func WithFailureDetectorTimeout(t time.Duration) FailureDetectorOption {
	return func(fd *singleFailureDetectorResource) {
		fd.timeout = t
	}
}

func WithFailureDetectorPullInterval(t time.Duration) FailureDetectorOption {
	return func(fd *singleFailureDetectorResource) {
		fd.pullInterval = t
	}
}

func singleFailureDetectorResourceMaker(archetypeID distsys.TLAValue, monitorAddr string, opts ...FailureDetectorOption) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		fd := &singleFailureDetectorResource{
			archetypeID:  archetypeID,
			monitorAddr:  monitorAddr,
			timeout:      failureDetectorTimeout,
			pullInterval: failureDetectorPullInterval,
			client:       nil,
			state:        uninitialized,
			reDial:       false,
		}
		for _, opt := range opts {
			opt(fd)
		}
		go fd.mainLoop()
		return fd
	})
}

func (res *singleFailureDetectorResource) getState() ArchetypeState {
	res.lock.RLock()
	defer res.lock.RUnlock()
	return res.state
}

func (res *singleFailureDetectorResource) setState(state ArchetypeState) {
	res.lock.Lock()
	res.state = state
	res.lock.Unlock()
}

func (res *singleFailureDetectorResource) ensureClient() error {
	// log.Println("client", res.client, "reDial", res.reDial)
	if res.client == nil || res.reDial {
		//log.Println("fd dialing", "archetype id", res.archetypeID)
		conn, err := net.DialTimeout("tcp", res.monitorAddr, res.timeout)
		if err != nil {
			return err
		}
		res.client = rpc.NewClient(conn)
		res.reDial = false
	}
	return nil
}

func (res *singleFailureDetectorResource) mainLoop() {
	ticker := time.NewTicker(res.pullInterval)
	for range ticker.C {
		// log.Println("tick")

		err := res.ensureClient()
		if err != nil {
			//log.Println("fd dial err", err, "archetype id", res.archetypeID)
			res.setState(failed)
			continue
		}

		var reply ArchetypeState
		call := res.client.Go("MonitorRPCServer.IsAlive", &res.archetypeID, &reply, nil)
		timeout := false
		select {
		case <-call.Done:
			err = call.Error
		case <-time.After(res.timeout):
			timeout = true
		}
		if timeout || err != nil {
			//log.Println("fd call err", err, "timeout", timeout, "archetype id", res.archetypeID)
			res.setState(failed)
			if err == rpc.ErrShutdown {
				res.reDial = true
			}
		} else {
			// log.Println("fd reply", reply, "archetype id", res.archetypeID)
			res.setState(reply)
		}

		// log.Println("fd state", res.getState(), "archetype id", res.archetypeID)
	}
}

func (res *singleFailureDetectorResource) Abort() chan struct{} {
	return nil
}

func (res *singleFailureDetectorResource) PreCommit() chan error {
	return nil
}

func (res *singleFailureDetectorResource) Commit() chan struct{} {
	return nil
}

func (res *singleFailureDetectorResource) ReadValue() (distsys.TLAValue, error) {
	state := res.getState()
	if state == uninitialized {
		time.Sleep(res.pullInterval)
		return distsys.TLAValue{}, distsys.ErrCriticalSectionAborted
	} else if state == alive {
		return distsys.TLA_FALSE, nil
	} else {
		return distsys.TLA_TRUE, nil
	}
}

func (res *singleFailureDetectorResource) WriteValue(value distsys.TLAValue) error {
	panic(fmt.Errorf("attempted to write value %v to a single failure detector resource", value))
}
