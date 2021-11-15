package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"log"
	"net"
	"net/rpc"
	"sync"
	"time"
)

const (
	broadcastTimeout  = 2 * time.Second
	broadcastInterval = 5 * time.Second
	connectionTimeout = 2 * time.Second
)

type mergeFn func(other crdtValue)

type crdt struct {
	distsys.ArchetypeResourceLeafMixin
	id tla.TLAValue
	listenAddr string

	stateMu     sync.RWMutex
	oldValue crdtValue
	value crdtValue
	hasOldValue bool
	mergeQueue []crdtValue

	inCSMu            sync.RWMutex
	inCriticalSection bool

	peerAddrs *immutable.Map
	peers   *immutable.Map

	closeChan chan struct{}
}

var _ distsys.ArchetypeResource = &crdt{}

type crdtValue interface {
	Read() tla.TLAValue
	Write(id tla.TLAValue, value tla.TLAValue) crdtValue
	Merge(other crdtValue) crdtValue
	String() string
}

// CRDTAddressMappingFn is a map from each node's id sharing the CRDT state to its address
type CRDTAddressMappingFn func(id tla.TLAValue) string

// CRDTInitFn creates and initializes a particular crdtValue
type CRDTInitFn func() crdtValue

// CRDTMaker returns an archetype resource implementing the behaviour of a CRDT.
// Given the list of peer ids, it starts broadcasting local CRDT state to all its peers every broadcastInterval.
// It also starts accepting incoming RPC calls from peers to receive and merge CRDT states.
// Note that local state is currently not persisted. TODO: Persist local state on Commit, reload on restart
func CRDTMaker(id tla.TLAValue, peers []tla.TLAValue, addressMappingFn CRDTAddressMappingFn, crdtInitFn CRDTInitFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		listenAddr := addressMappingFn(id)
		b := immutable.NewMapBuilder(tla.TLAValueHasher{})
		for _, pid := range peers {
			b.Set(pid, addressMappingFn(pid))
		}

		crdt := &crdt{
			id:                         id,
			listenAddr:                 addressMappingFn(id),
			value:                      crdtInitFn(),
			peerAddrs:                  b.Map(),
			peers:                      immutable.NewMap(tla.TLAValueHasher{}),
			closeChan:                  make(chan struct{}),
		}

		rpcServer := rpc.NewServer()
		err := rpcServer.Register(&CRDTRPCReceiver{crdt: crdt})
		if err != nil {
			log.Panicf("node %s: could not register CRDT RPCs: %v", id, err)
		}
		listener, err := net.Listen("tcp", listenAddr)
		if err != nil {
			log.Panicf("node %s: could not listen on address %s: %v", id, listenAddr, err)
		}
		log.Printf("node %s: started listening on %s", id, listenAddr)

		go rpcServer.Accept(listener)
		go crdt.runBroadcasts(broadcastTimeout)

		return crdt
	})
}

func (res *crdt) Abort() chan struct{} {
	res.exitCSAndMerge()

	res.stateMu.Lock()
	if res.hasOldValue {
		res.value = res.oldValue
		res.hasOldValue = false
	}
	res.stateMu.Unlock()
	return nil
}

func (res *crdt) PreCommit() chan error {
	return nil
}

func (res *crdt) Commit() chan struct{} {
	res.exitCSAndMerge()

	res.stateMu.Lock()
	res.hasOldValue = false
	res.stateMu.Unlock()
	return nil
}

func (res *crdt) ReadValue() (tla.TLAValue, error) {
	res.enterCS()

	res.stateMu.RLock()
	defer res.stateMu.RUnlock()

	return res.value.Read(), nil
}

func (res *crdt) WriteValue(value tla.TLAValue) error {
	res.enterCS()

	res.stateMu.Lock()
	defer res.stateMu.Unlock()

	state := res
	if !state.hasOldValue {
		state.oldValue = res.value
		state.hasOldValue = true
	}
	state.value = state.value.Write(res.id, value)

	return nil
}

func (res *crdt) Close() error {
	res.closeChan <- struct{}{}

	res.stateMu.RLock()
	defer res.stateMu.RUnlock()

	var err error
	it := res.peers.Iterator()
	for !it.Done() {
		id, client := it.Next()
		if client != nil {
			err = client.(*rpc.Client).Close()
			if err != nil {
				log.Printf("node %s: could not close connection with node %s: %v\n", res.id, id, err)
			}
		}
	}

	log.Printf("node %s: closing with state: %s\n", res.id, res.value)
	return nil
}

// tryConnectPeers tries to connect to peer nodes with timeout. If dialing
// succeeds, retains the client for later RPC.
func (res *crdt) tryConnectPeers() {
	it := res.peerAddrs.Iterator()
	for !it.Done() {
		id, addr := it.Next()
		if _, ok := res.peers.Get(id); !ok {
			conn, err := net.DialTimeout("tcp", addr.(string), connectionTimeout)
			if err == nil {
				res.peers = res.peers.Set(id.(tla.TLAValue), rpc.NewClient(conn))
			}
		}
	}
}

// runBroadcasts starts broadcasting to peer nodes of commited state value.
// On every broadcastInterval, the method checks if resource is currently
// holds uncommited state. If it does, it skips braodcast.  If resource state
// is committed, it calls ReceiveValue RPC on each peer with timeout.
func (res *crdt) runBroadcasts(timeout time.Duration) {
	type callWithTimeout struct {
		call        *rpc.Call
		timeoutChan <-chan time.Time
	}

	for {
		select {
		case <-res.closeChan:
			log.Printf("node %s: terminating broadcasts\n", res.id)
			return
		default:
			time.Sleep(broadcastInterval)
			res.tryConnectPeers()

			res.stateMu.RLock()

			// wait until the value stablizes
			if res.hasOldValue {
				continue
			}

			args := ReceiveValueArgs{
				Value: res.value,
			}

			b := immutable.NewMapBuilder(tla.TLAValueHasher{})
			it := res.peers.Iterator()
			for !it.Done() {
				id, client := it.Next()
				b.Set(id, callWithTimeout{
					call:        client.(*rpc.Client).Go("CRDTRPCReceiver.ReceiveValue", args, nil, nil),
					timeoutChan: time.After(timeout),
				})
			}
			res.stateMu.RUnlock()

			calls := b.Map()
			it = calls.Iterator()
			for !it.Done() {
				id, cwt := it.Next()
				call := cwt.(callWithTimeout).call
				select {
				case <-call.Done:
					if call.Error != nil {
						log.Printf("node %s: could not broadcast to node %s:%v\n", res.id, id, call.Error)
					}
				case <-cwt.(callWithTimeout).timeoutChan:
					log.Printf("node %s: broadcast to node %s timed out\n", res.id, id)
				}
			}
		}
	}
}

// enterCS brings the resource into critical section
func (res *crdt) enterCS() {
	res.inCSMu.Lock()
	res.inCriticalSection = true
	res.inCSMu.Unlock()
}

// exitCSAndMerge exits critical section and merges all queued updates.
func (res *crdt) exitCSAndMerge() {
	res.stateMu.Lock()
	for _, other := range res.mergeQueue {
		res.value.Merge(other)
	}
	res.mergeQueue = nil
	res.stateMu.Unlock()

	res.inCSMu.Lock()
	res.inCriticalSection = false
	res.inCSMu.Unlock()
}

type CRDTRPCReceiver struct {
	crdt *crdt
}

type ReceiveValueArgs struct {
	Value crdtValue
}

type ReceiveValueResp struct{}

// ReceiveValue receives state from other peer node, and calls the merge function.
// If the resource is currently in critical section, its local value cannot change.
// So it queues up the updates to be merged after exiting critical section.
func (rcvr *CRDTRPCReceiver) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	res := rcvr.crdt
	log.Printf("node %s: received value %s\n", res.id, args.Value)

	res.inCSMu.RLock()
	res.stateMu.Lock()
	if !res.inCriticalSection {
		res.value = res.value.Merge(args.Value)
	} else {
		res.mergeQueue = append(res.mergeQueue, args.Value)
		log.Printf("node %s: in CS, queuing merge %v\n", res.id, res.mergeQueue)
	}
	res.stateMu.Unlock()
	res.inCSMu.RUnlock()
	return nil
}