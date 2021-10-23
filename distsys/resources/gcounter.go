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

type GCounterResource struct {
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

	broadcastInt int32 // seconds

	closeChan chan struct{}
	doneChan chan struct{}
}

var _ distsys.ArchetypeResource = &GCounterResource{}

type ReceiveValueArgs struct {
	Value map[int32]int32
}

type ReceiveValueResp struct {}

type GCounterAddressMappingFn func(value tla.TLAValue) string

// TODO: Persist local state to disk on Commit, reload in maker

func GCounterResourceMaker(id tla.TLAValue, peers []tla.TLAValue, addressMappingFn GCounterAddressMappingFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		listenAddr := addressMappingFn(id)
		peerAddrs := make(map[tla.TLAValue]string, len(peers))
		for _, pid := range peers {
			peerAddrs[pid] = addressMappingFn(pid)
		}

		res := &GCounterResource{
			id:         id,
			listenAddr: addressMappingFn(id),

			state:      make(map[int32]int32),
			oldState: make(map[int32]int32),
			hasOldState: false,

			peerAddrs: peerAddrs,
			peers: make(map[tla.TLAValue]*rpc.Client),

			broadcastInt: 5,

			doneChan: make(chan struct{}),
			closeChan: make(chan struct{}),
		}

		rpcServer := rpc.NewServer()
		err := rpcServer.Register(res)
		if err != nil {
			fmt.Errorf("could not register CRDT RPCs: %w", err)
		}
		listner, err := net.Listen("tcp", listenAddr)
		if err != nil {
			fmt.Errorf("could not listen on address %s: %w", listenAddr, err)
		}
		log.Printf("Node %d started listening on %s", id.AsNumber(), listenAddr)

		go rpcServer.Accept(listner)
		go res.runBroadcasts()

		return res
	})
}

func (res *GCounterResource) Abort() chan struct{} {
	if res.hasOldState {
		res.state = res.oldState
		res.hasOldState = false
	}
	return nil
}

func (res *GCounterResource) PreCommit() chan error {
	return nil;
}

func (res *GCounterResource) Commit() chan struct{} {
	res.hasOldState = false
	return nil
}

func (res *GCounterResource) ReadValue() (tla.TLAValue, error) {
	res.stateMu.RLock()
	defer res.stateMu.RUnlock()
	var value int32 = 0
	for _, v := range res.state {
		value += v;
	}
	return tla.MakeTLANumber(value), nil
}

func (res *GCounterResource) WriteValue(value tla.TLAValue) error {
	res.stateMu.Lock()
	res.stateMu.Unlock()
	if !res.hasOldState {
		res.oldState = res.state
		res.hasOldState = true
	}
	res.state[res.id.AsNumber()] += value.AsNumber()
	return nil
}

func (res *GCounterResource) Close() error {
	// TODO: clean locks, close channels, connections
	res.stateMu.RLock()
	defer res.stateMu.RUnlock()

	res.closeChan <- struct{}{}
	<- res.doneChan

	var err error
	for id, client := range res.peers {
		err = client.Close()
		if err != nil {
			fmt.Errorf("could not close connection with node %s: %w\n", id, err)
		}
	}

	log.Printf("node %s closing with state: %v\n", res.id, res.state)
	return nil
}

func (res *GCounterResource) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	log.Printf("node %d received value %v\n", res.id.AsNumber(), args.Value)
	res.stateMu.Lock()
	defer res.stateMu.Unlock()
	res.merge(args.Value)
	return nil
}

func (res *GCounterResource) merge(other map[int32]int32) {
	for id, val := range other {
		if v, ok := res.state[id]; !ok || v < val {
			res.state[id] = val
		}
	}
}

func (res *GCounterResource) tryConnectPeers() {
	for id, addr := range res.peerAddrs {
		if _, ok := res.peers[id]; !ok {
			client, err := rpc.Dial("tcp", addr)
			if err == nil {
				res.peers[id] = client
			}
		}
	}
}

func (res *GCounterResource) runBroadcasts() {
	calls := make(map[tla.TLAValue]*rpc.Call, len(res.peers))
	for {
		select {
		case <- res.closeChan:
			log.Printf("node %d: terminating broadcasts\n", res.id.AsNumber())
			res.doneChan <- struct{}{}
			return
		default:
			time.Sleep(time.Duration(res.broadcastInt) * time.Second)
			res.tryConnectPeers()
			args := ReceiveValueArgs{
				Value: res.oldState,
			}
			for id, client := range res.peers  {
				calls[id] = client.Go("GCounterResource.ReceiveValue", args, nil, nil)
			}

			for id, call := range calls {
				<- call.Done
				if call.Error != nil {
					fmt.Errorf("node %d could not broadcast to node %d:%w\n", res.id.AsNumber(), id.AsNumber(), call.Error)
					delete(res.peers, id)
				}
			}
		}
	}
}
