package resources

import (
	"fmt"
	"log"
	"net"
	"net/rpc"
	"sync"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/hashmap"
	"github.com/DistCompiler/pgo/distsys/tla"
)

type crdtConfig struct {
	broadcastInterval time.Duration
	sendTimeout       time.Duration
	dialTimeout       time.Duration
}

var defaultCRDTConfig = crdtConfig{
	broadcastInterval: 50 * time.Millisecond,
	sendTimeout:       2 * time.Second,
	dialTimeout:       2 * time.Second,
}

type crdt struct {
	distsys.ArchetypeResourceLeafMixin
	id       tla.Value
	listener net.Listener

	stateLock   sync.RWMutex
	oldValue    CRDTValue
	value       CRDTValue
	hasOldValue bool

	mergeValues        chan CRDTValue
	needBroadcastCount int
	needBroadcastLock  sync.Mutex

	peerIds   []tla.Value
	peerAddrs *hashmap.HashMap[string]
	conns     *hashmap.HashMap[*rpc.Client]

	config crdtConfig

	closeChan     chan struct{}
	broadcastDone chan struct{}
}

var _ distsys.ArchetypeResource = &crdt{}

type CRDTValue interface {
	Init() CRDTValue
	Read() tla.Value
	Write(id tla.Value, value tla.Value) CRDTValue
	Merge(other CRDTValue) CRDTValue
}

// CRDTAddressMappingFn is a map from each node's id sharing the CRDT state to its address
type CRDTAddressMappingFn func(id tla.Value) string

type CRDTOption func(c *crdt)

func WithCRDTBroadcastInterval(d time.Duration) CRDTOption {
	return func(c *crdt) {
		c.config.broadcastInterval = d
	}
}

func WithCRDTSendTimeout(d time.Duration) CRDTOption {
	return func(c *crdt) {
		c.config.sendTimeout = d
	}
}

func WithCRDTDialTimeout(d time.Duration) CRDTOption {
	return func(c *crdt) {
		c.config.dialTimeout = d
	}
}

// NewCRDT returns an archetype resource implementing the behaviour of a CRDT.
// Given the list of peer ids, it starts broadcasting local CRDT state to all
// its peers every broadcastInterval. It also starts accepting incoming RPC
// calls from peers to receive and merge CRDT states. Note that local state is
// currently not persisted.
func NewCRDT(id tla.Value, peerIds []tla.Value, addressMappingFn CRDTAddressMappingFn,
	crdtValue CRDTValue, opts ...CRDTOption) distsys.ArchetypeResource {
	listenAddr := addressMappingFn(id)
	peerAddrs := hashmap.New[string]()
	for _, pid := range peerIds {
		peerAddrs.Set(pid, addressMappingFn(pid))
	}

	crdt := &crdt{
		id:                 id,
		value:              crdtValue.Init(),
		peerIds:            peerIds,
		peerAddrs:          peerAddrs,
		conns:              hashmap.New[*rpc.Client](),
		closeChan:          make(chan struct{}),
		broadcastDone:      make(chan struct{}),
		mergeValues:        make(chan CRDTValue, 100),
		needBroadcastCount: 0,
		config:             defaultCRDTConfig,
	}

	for _, opt := range opts {
		opt(crdt)
	}

	rpcServer := rpc.NewServer()
	err := rpcServer.Register(&CRDTRPCReceiver{crdt: crdt})
	if err != nil {
		log.Fatalf("node %s: could not register CRDT RPCs: %v", id, err)
	}
	listener, err := net.Listen("tcp", listenAddr)
	if err != nil {
		log.Fatalf("node %s: could not listen on address %s: %v", id, listenAddr, err)
	}
	log.Printf("node %s: started listening on %s", id, listenAddr)
	crdt.listener = listener

	go rpcServer.Accept(listener)
	go crdt.runBroadcasts()
	go crdt.merger()

	return crdt
}

func (res *crdt) Abort(distsys.ArchetypeInterface) chan struct{} {
	res.stateLock.Lock()
	defer res.stateLock.Unlock()
	if res.hasOldValue {
		res.value = res.oldValue
		res.hasOldValue = false
	}
	return nil
}

func (res *crdt) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *crdt) Commit(distsys.ArchetypeInterface) chan struct{} {
	res.stateLock.Lock()
	res.hasOldValue = false
	res.stateLock.Unlock()
	return nil
}

func (res *crdt) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	res.stateLock.RLock()
	defer res.stateLock.RUnlock()

	return res.value.Read(), nil
}

func (res *crdt) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	res.stateLock.Lock()
	defer res.stateLock.Unlock()

	if !res.hasOldValue {
		res.oldValue = res.value
		res.hasOldValue = true
	}
	res.value = res.value.Write(res.id, value)

	res.needBroadcastLock.Lock()
	defer res.needBroadcastLock.Unlock()
	res.needBroadcastCount = len(res.peerIds)

	return nil
}

func (res *crdt) Close() error {
	close(res.closeChan)
	<-res.broadcastDone
	res.stateLock.RLock()
	defer res.stateLock.RUnlock()

	var err error
	for _, id := range res.conns.Keys() {
		client, _ := res.conns.Get(id)
		if client != nil {
			err = client.Close()
			if err != nil {
				return fmt.Errorf("node %s: could not close connection with node %s: %v", res.id, id, err)
			}
		}
	}
	err = res.listener.Close()
	if err != nil {
		return fmt.Errorf("node %s: could not close lister: %v", res.id, err)
	}

	log.Printf("node %s: closing with state: %s\n", res.id, res.value)
	return nil
}

// tryConnectPeers tries to connect to peer nodes with timeout. If dialing
// succeeds, retains the client for later RPC.
func (res *crdt) tryConnectPeers() {
	for _, id := range res.peerIds {
		if id.Equal(res.id) {
			continue
		}

		if _, ok := res.conns.Get(id); !ok {
			addr, _ := res.peerAddrs.Get(id)
			conn, err := net.DialTimeout("tcp", addr, res.config.dialTimeout)
			if err == nil {
				res.conns.Set(id, rpc.NewClient(conn))
			} else {
				log.Printf("node %s: failed to reach %s: %v", res.id, id, err)
			}
		}
	}
}

// runBroadcasts starts broadcasting to peer nodes of commited state value.
// On every broadcastInterval, the method checks if resource is currently
// holds uncommited state. If it does, it skips braodcast.  If resource state
// is committed, it calls ReceiveValue RPC on each peer with timeout.
func (res *crdt) runBroadcasts() {
	ticker := time.NewTicker(res.config.broadcastInterval)
	defer ticker.Stop()

	for range ticker.C {
		select {
		case <-res.closeChan:
			log.Printf("node %s: terminating broadcasts", res.id)
			res.broadcastDone <- struct{}{}
			return
		default:
			res.broadcast()
		}
	}
}

func (res *crdt) prepMerge(rcvd CRDTValue) {
	if rcvd != nil {
		res.mergeValues <- rcvd
	}
}

func (res *crdt) getStableValue() CRDTValue {
	res.stateLock.RLock()
	defer res.stateLock.RUnlock()

	if res.hasOldValue {
		return res.oldValue
	}
	return res.value
}

func (res *crdt) broadcast() {
	// start := time.Now()
	// defer func() {
	// 	elapsed := time.Since(start)
	// 	log.Printf("broadcast took %v", elapsed)
	// }()

	type callWithTimeout struct {
		call        *rpc.Call
		timeoutChan <-chan time.Time
	}

	if !func() bool {
		res.needBroadcastLock.Lock()
		defer res.needBroadcastLock.Unlock()
		return res.needBroadcastCount > 0
	}() {
		return
	}

	res.tryConnectPeers()

	args := ReceiveValueArgs{Value: res.getStableValue()}

	calls := hashmap.New[callWithTimeout]()
	for _, id := range res.peerIds {
		if client, ok := res.conns.Get(id); ok {
			var reply ReceiveValueResp
			calls.Set(id, callWithTimeout{
				call:        client.Go("CRDTRPCReceiver.ReceiveValue", args, &reply, nil),
				timeoutChan: time.After(res.config.sendTimeout),
			})
		}
	}

	for _, id := range calls.Keys() {
		cwt, _ := calls.Get(id)
		call := cwt.call
		select {
		case <-call.Done:
			if call.Error != nil {
				log.Printf("node %s: could not broadcast to node %s:%v\n", res.id, id, call.Error)
			} else {
				func() {
					res.needBroadcastLock.Lock()
					defer res.needBroadcastLock.Unlock()
					res.needBroadcastCount = max(res.needBroadcastCount-1, 0)
				}()
				log.Printf("node %s: broadcasted to node %s: %v\n", res.id, id, call.Reply.(*ReceiveValueResp).Value)
				res.prepMerge(call.Reply.(*ReceiveValueResp).Value)
			}
		case <-cwt.timeoutChan:
			log.Printf("node %s: broadcast to node %s timed out\n", res.id, id)
		}
	}
}

func (res *crdt) merger() {
	for {
		select {
		case mergeVal := <-res.mergeValues:
			func() {
				res.stateLock.Lock()
				defer res.stateLock.Unlock()
				res.value = res.value.Merge(mergeVal)
			}()
		case <-res.closeChan:
			return
		}
	}
}

type CRDTRPCReceiver struct {
	crdt *crdt
}

type ReceiveValueArgs struct {
	Value CRDTValue
}

type ReceiveValueResp struct {
	Value CRDTValue
}

// ReceiveValue receives state from other peer node, and calls the merge function.
// If the resource is currently in critical section, its local value cannot change.
// So it queues up the updates to be merged after exiting critical section.
func (rcvr *CRDTRPCReceiver) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	res := rcvr.crdt
	log.Printf("node %s: received value %s\n", res.id, args.Value)

	if args.Value != nil {
		res.prepMerge(args.Value)
	}
	*reply = ReceiveValueResp{Value: res.getStableValue()}
	return nil
}
