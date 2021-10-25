package resources

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
	"net"
	"net/rpc"
	"sync"
	"time"
)

const (
	broadcastTimeout = 2 * time.Second
	broadcastInterval = 5 * time.Second
	connectionTimeout = 2 * time.Second
)

type GCounter struct {
	distsys.ArchetypeResourceLeafMixin
	id          tla.TLAValue
	listenAddr  string

	hasOldState bool
	oldState    map[int32]int32
	state       map[int32]int32
	stateMu     sync.RWMutex

	peerAddrs 	map[tla.TLAValue]string
	peers       map[tla.TLAValue]*rpc.Client
	peersMu		sync.RWMutex

	closeChan chan struct{}
}

var _ distsys.ArchetypeResource = &GCounter{}

type ReceiveValueArgs struct {
	Value map[int32]int32
}

type ReceiveValueResp struct {}

type GCounterAddressMappingFn func(value tla.TLAValue) string

// TODO: Persist local state to disk on Commit, reload in maker

func GCounterMaker(id tla.TLAValue, peers []tla.TLAValue, addressMappingFn GCounterAddressMappingFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		listenAddr := addressMappingFn(id)
		peerAddrs := make(map[tla.TLAValue]string, len(peers))
		for _, pid := range peers {
			peerAddrs[pid] = addressMappingFn(pid)
		}

		res := &GCounter{
			id:         id,
			listenAddr: addressMappingFn(id),

			state:      make(map[int32]int32),
			oldState: make(map[int32]int32),
			hasOldState: false,

			peerAddrs: peerAddrs,
			peers: make(map[tla.TLAValue]*rpc.Client),

			closeChan: make(chan struct{}),
		}

		rpcServer := rpc.NewServer()
		err := rpcServer.Register(res)
		if err != nil {
			panic(fmt.Errorf("could not register CRDT RPCs: %w", err))
		}
		listner, err := net.Listen("tcp", listenAddr)
		if err != nil {
			panic(fmt.Errorf("could not listen on address %s: %w", listenAddr, err))
		}
		log.Printf("Node %d started listening on %s", id.AsNumber(), listenAddr)

		go rpcServer.Accept(listner)
		go res.runBroadcasts(broadcastTimeout)

		return res
	})
}

func (res *GCounter) Abort() chan struct{} {
	if res.hasOldState {
		res.state = res.oldState
		res.hasOldState = false
	}
	return nil
}

func (res *GCounter) PreCommit() chan error {
	return nil
}

func (res *GCounter) Commit() chan struct{} {
	res.hasOldState = false
	return nil
}

func (res *GCounter) ReadValue() (tla.TLAValue, error) {
	res.stateMu.RLock()
	defer res.stateMu.RUnlock()
	var value int32 = 0
	for _, v := range res.state {
		value += v;
	}
	return tla.MakeTLANumber(value), nil
}

func (res *GCounter) WriteValue(value tla.TLAValue) error {
	res.stateMu.Lock()
	res.stateMu.Unlock()
	if !res.hasOldState {
		res.oldState = res.state
		res.hasOldState = true
	}
	res.state[res.id.AsNumber()] += value.AsNumber()
	return nil
}

func (res *GCounter) Close() error {
	res.stateMu.RLock()
	defer res.stateMu.RUnlock()

	res.closeChan <- struct{}{}

	var err error
	for id, client := range res.peers {
		if client != nil {
			err = client.Close()
			if err != nil {
				fmt.Errorf("could not close connection with node %s: %w\n", id, err)
			}
		}
	}

	log.Printf("node %s closing with state: %v\n", res.id, res.state)
	return nil
}

func (res *GCounter) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	log.Printf("node %d received value %v\n", res.id.AsNumber(), args.Value)
	res.stateMu.Lock()
	defer res.stateMu.Unlock()
	res.merge(args.Value)
	return nil
}

func (res *GCounter) merge(other map[int32]int32) {
	for id, val := range other {
		if v, ok := res.state[id]; !ok || v < val {
			res.state[id] = val
		}
	}
}

func (res *GCounter) tryConnectPeers() {
	for id, addr := range res.peerAddrs {
		if _, ok := res.peers[id]; !ok {
			conn, err := net.DialTimeout("tcp", addr, 5 * time.Second)
			if err == nil {
				res.peers[id] = rpc.NewClient(conn)
			}
		}
	}
}

func (res *GCounter) runBroadcasts(timeout time.Duration) {
	type callWithTimeout struct {
		call *rpc.Call
		timeoutChan <- chan time.Time
	}

	calls := make(map[tla.TLAValue]callWithTimeout, len(res.peers))
	for {
		select {
		case <- res.closeChan:
			log.Printf("node %d: terminating broadcasts\n", res.id.AsNumber())
			return
		default:
			time.Sleep(broadcastInterval)
			res.tryConnectPeers()
			args := ReceiveValueArgs{
				Value: res.oldState,
			}
			for id, client := range res.peers  {
				calls[id] = callWithTimeout {
					call: client.Go("GCounter.ReceiveValue", args, nil, nil),
					timeoutChan: time.After(timeout),
				}
			}

			for id, cwt := range calls {
				select {
					case <- cwt.call.Done:
					if cwt.call.Error != nil {
						fmt.Errorf("node %d: could not broadcast to node %d:%w\n", res.id.AsNumber(), id.AsNumber(), cwt.call.Error)
					}
					case <- cwt.timeoutChan:
						fmt.Errorf("node %d: broadcast to node %d timed out\n", res.id.AsNumber(), id.AsNumber())
				}
			}
		}
	}
}
