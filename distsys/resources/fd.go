package resources

import (
	"errors"
	"fmt"
	"log"
	"net"
	"net/rpc"
	"runtime/debug"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/tla"

	"github.com/UBC-NSS/pgo/distsys"
)

const (
	failureDetectorTimeout      = 1 * time.Second
	failureDetectorPullInterval = 2 * time.Second
)

// ArchetypeState is an enum that denotes an archetype running state.
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

// Monitor monitors the registered archetypes by wrapping them. Monitor provides
// the IsAlive API, which can be queried to find out whether a specific
// archetype is alive. At most one monitor should be defined in each OS process,
// and it catches all archetypes' goroutines errors and panics. In the case of
// an error or a panic for an archetype's goroutine, the Monitor returns false
// to IsAlive calls with that particular archetype. Monitor exposes IsAlive API
// as an RPC. If the whole OS process fails, consequent calls to IsAlive will
// time out, and this timeout behavior denotes failure of the queried archetype.
type Monitor struct {
	ListenAddr string

	listener net.Listener
	server   *rpc.Server

	done chan struct{}

	lock sync.RWMutex
	// TODO: tla.Value cannot be used as a map keys
	states *hashmap.HashMap[ArchetypeState]
}

// NewMonitor creates a new Monitor and returns a pointer to it.
func NewMonitor(listenAddr string) *Monitor {
	return &Monitor{
		ListenAddr: listenAddr,
		states:     hashmap.New[ArchetypeState](),
		done:       make(chan struct{}),
	}
}

func (m *Monitor) setState(archetypeID tla.Value, state ArchetypeState) {
	m.lock.Lock()
	m.states.Set(archetypeID, state)
	m.lock.Unlock()
}

func (m *Monitor) getState(archetypeID tla.Value) (ArchetypeState, bool) {
	m.lock.RLock()
	state, ok := m.states.Get(archetypeID)
	m.lock.RUnlock()
	return state, ok
}

// RunArchetype runs the given archetype inside the monitor. Wraps a call to ctx.RunDiscardingExits
func (m *Monitor) RunArchetype(ctx *distsys.MPCalContext) (err error) {
	archetypeID := ctx.IFace().Self()
	log.Printf("running archetype %v inside a monitor %s", archetypeID, m.ListenAddr)
	defer func() {
		if r := recover(); r != nil {
			m.setState(archetypeID, failed)
			err = fmt.Errorf("archetype %d recovered from panic: %s\n%s", archetypeID, r, debug.Stack())
		}
		if err != nil {
			log.Println(err)
		}
	}()

	m.setState(archetypeID, alive)
	err = ctx.Run()
	//log.Println("finished", archetypeID, err)
	if err == nil {
		m.setState(archetypeID, finished)
	} else {
		m.setState(archetypeID, failed)
	}
	return
}

// ListenAndServe starts the monitor's RPC server and serves the incoming
// connections. It blocks until an error occurs or the monitor closes.
func (m *Monitor) ListenAndServe() error {
	rpcRcvr := &MonitorRPCReceiver{m: m}
	m.server = rpc.NewServer()
	err := m.server.Register(rpcRcvr)
	if err != nil {
		return err
	}

	m.listener, err = net.Listen("tcp", m.ListenAddr)
	if err != nil {
		return err
	}
	log.Printf("Monitor: started listening on %s", m.ListenAddr)
	for {
		conn, err := m.listener.Accept()
		if err != nil {
			select {
			case <-m.done:
				return nil
			default:
				return err
			}
		}
		go m.server.ServeConn(conn)
	}
}

// Close stops the monitor's RPC servers. It doesn't do anything with the
// archetypes that the monitor is running.
func (m *Monitor) Close() error {
	var err error
	close(m.done)
	if m.listener != nil {
		err = m.listener.Close()
	}
	return err
}

type MonitorRPCReceiver struct {
	m *Monitor
}

func (rcvr *MonitorRPCReceiver) IsAlive(arg tla.Value, reply *ArchetypeState) error {
	state, ok := rcvr.m.getState(arg)
	if !ok {
		return errors.New("archetype not found")
	}
	*reply = state
	return nil
}

// FailureDetectorAddressMappingFn returns address of the monitor that is
// running the archetype with the given index.
type FailureDetectorAddressMappingFn func(tla.Value) string

type FailureDetector struct {
	*IncMap
}

var _ distsys.ArchetypeResource = &FailureDetector{}

// NewFailureDetector produces a distsys.ArchetypeResource for a
// collection of single failure detectors. Each single failure detector is
// responsible to detect that a particular archetype is alive or not. Actually
// the single failure detector with index i is equivalent to `fd[i]` in the
// MPCal spec. A single failure detector periodically calls the IsAlive RPC
// from archetype's monitor. In case of false response or timeout, it marks
// the archetype as failed. Optionally, it gives options to configure parameters
// such as timeouts.
// Read from a single failure detector returns true if it detects the archetype
// as failed. Otherwise, it returns false.
// FailureDetector refines the guarantees following mapping macro:
//
// mapping macro PracticalFD {
//    read {
//        if ($variable = FALSE) { \* process is alive
//            either { yield TRUE; } or { yield FALSE; }; \* no accuracy guarantee
//        } else {
//            yield $variable; \* (eventual) completeness
//        }
//    }
//    write { assert(FALSE); yield $value; }
// }
//
// It provides strong completeness but no accuracy guarantee. This failure
// detector can have both false positive (due to no accuracy) and false negative
// (due to [eventual] completeness) outputs.
func NewFailureDetector(addressMappingFn FailureDetectorAddressMappingFn, opts ...FailureDetectorOption) *FailureDetector {
	return &FailureDetector{
		NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
			monitorAddr := addressMappingFn(index)
			return NewSingleFailureDetector(index, monitorAddr, opts...)
		}),
	}
}

type SingleFailureDetector struct {
	distsys.ArchetypeResourceLeafMixin
	archetypeID tla.Value
	monitorAddr string

	timeout      time.Duration
	pullInterval time.Duration

	client *rpc.Client
	reDial bool
	ticker *time.Ticker

	lock  sync.RWMutex
	state ArchetypeState

	execLock sync.RWMutex
	started  bool
	closing  bool

	done chan struct{}
}

type FailureDetectorOption func(fd *SingleFailureDetector)

func WithFailureDetectorTimeout(t time.Duration) FailureDetectorOption {
	return func(fd *SingleFailureDetector) {
		fd.timeout = t
	}
}

func WithFailureDetectorPullInterval(t time.Duration) FailureDetectorOption {
	return func(fd *SingleFailureDetector) {
		fd.pullInterval = t
	}
}

func NewSingleFailureDetector(archetypeID tla.Value, monitorAddr string, opts ...FailureDetectorOption) *SingleFailureDetector {
	fd := &SingleFailureDetector{
		archetypeID:  archetypeID,
		monitorAddr:  monitorAddr,
		timeout:      failureDetectorTimeout,
		pullInterval: failureDetectorPullInterval,
		client:       nil,
		state:        uninitialized,
		reDial:       false,
		started:      false,
		closing:      false,
		done:         make(chan struct{}),
	}
	for _, opt := range opts {
		opt(fd)
	}
	go fd.mainLoop()
	return fd
}

func (res *SingleFailureDetector) getState() ArchetypeState {
	res.lock.RLock()
	defer res.lock.RUnlock()
	return res.state
}

func (res *SingleFailureDetector) setState(state ArchetypeState) {
	res.lock.Lock()
	res.state = state
	res.lock.Unlock()
}

func (res *SingleFailureDetector) ensureClient() error {
	if res.client == nil || res.reDial {
		conn, err := net.DialTimeout("tcp", res.monitorAddr, res.timeout)
		if err != nil {
			return err
		}
		res.client = rpc.NewClient(conn)
		res.reDial = false
	}
	return nil
}

func (res *SingleFailureDetector) mainLoop() {
	res.execLock.Lock()
	if res.closing {
		res.execLock.Unlock()
		return
	}
	res.started = true
	res.execLock.Unlock()

	res.ticker = time.NewTicker(res.pullInterval)
loop:
	for range res.ticker.C {
		select {
		case <-res.done:
			break loop
		default:
		}

		oldState := res.getState()

		err := res.ensureClient()
		if err != nil {
			res.setState(failed)
			if oldState != failed {
				log.Printf("fd change state: archetype = %v, old state = %v, "+
					"new state = %v. Due to dial error: %v", res.archetypeID, oldState, failed, err)
			}
			continue
		}

		var reply ArchetypeState
		call := res.client.Go("MonitorRPCReceiver.IsAlive", &res.archetypeID, &reply, nil)
		timeout := false
		select {
		case <-call.Done:
			err = call.Error
		case <-time.After(res.timeout):
			timeout = true
		}
		if err != nil {
			res.setState(failed)
			if oldState != failed {
				log.Printf("fd change state: archetype = %v, old state = %v, "+
					"new state = %v. Due to rpc call error: %v", res.archetypeID, oldState, failed, err)
			}
			if err == rpc.ErrShutdown {
				res.reDial = true
			}
		} else if timeout {
			res.setState(failed)
			if oldState != failed {
				log.Printf("fd change state: archetype = %v, old state = %v, "+
					"new state = %v. Due to rpc call timeout", res.archetypeID, oldState, failed)
			}
		} else {
			res.setState(reply)
			if oldState != reply {
				log.Printf("fd change state: archetype = %v, old state = %v, "+
					"new state = %v. Due to rpc call reply", res.archetypeID, oldState, reply)
			}
		}
	}
}

func (res *SingleFailureDetector) Abort() chan struct{} {
	return nil
}

func (res *SingleFailureDetector) PreCommit() chan error {
	return nil
}

func (res *SingleFailureDetector) Commit() chan struct{} {
	return nil
}

func (res *SingleFailureDetector) ReadValue() (tla.Value, error) {
	state := res.getState()
	if state == uninitialized {
		time.Sleep(res.pullInterval)
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	} else if state == alive {
		return tla.ModuleFALSE, nil
	} else {
		return tla.ModuleTRUE, nil
	}
}

func (res *SingleFailureDetector) WriteValue(value tla.Value) error {
	panic(fmt.Errorf("attempted to write value %v to a single failure detector resource", value))
}

func (res *SingleFailureDetector) Close() error {
	res.execLock.Lock()
	if res.closing {
		res.execLock.Unlock()
		return nil
	}

	res.closing = true
	if res.started {
		// wait for the main loop to finish
		res.done <- struct{}{}
	}
	res.execLock.Unlock()

	// have to stop the timer to free up the associated resources
	if res.ticker != nil {
		res.ticker.Stop()
	}
	var err error
	// it's safe to access res.client here since the main loop has finished
	if res.client != nil {
		err = res.client.Close()
	}
	return err
}
