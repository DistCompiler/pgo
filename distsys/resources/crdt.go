package resources

import (
	"fmt"
	"log"
	"net"
	"net/rpc"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type crdtConfig struct {
	broadcastInterval time.Duration
	broadcastSize     int
	sendTimeout       time.Duration
	dialTimeout       time.Duration
}

var defaultCRDTConfig = crdtConfig{
	broadcastInterval: 50 * time.Millisecond,
	broadcastSize:     3,
	sendTimeout:       2 * time.Second,
	dialTimeout:       2 * time.Second,
}

type crdt struct {
	distsys.ArchetypeResourceLeafMixin
	id         tla.TLAValue
	listenAddr string
	listener   net.Listener

	stateMu     sync.RWMutex
	oldValue    CRDTValue
	value       CRDTValue
	hasOldValue bool

	inCSMu            sync.RWMutex
	inCriticalSection bool
	mergeVal          CRDTValue

	peerIds   []tla.TLAValue
	peerAddrs *hashmap.HashMap[string]
	conns     *hashmap.HashMap[*rpc.Client]

	config crdtConfig

	closeChan chan struct{}
}

var _ distsys.ArchetypeResource = &crdt{}

type CRDTValue interface {
	Init() CRDTValue
	Read() tla.TLAValue
	Write(id tla.TLAValue, value tla.TLAValue) CRDTValue
	Merge(other CRDTValue) CRDTValue
}

// CRDTAddressMappingFn is a map from each node's id sharing the CRDT state to its address
type CRDTAddressMappingFn func(id tla.TLAValue) string

type CRDTOption func(c *crdt)

func WithCRDTBroadcastInterval(d time.Duration) CRDTOption {
	return func(c *crdt) {
		c.config.broadcastInterval = d
	}
}

func WithCRDTBroadcastSize(s int) CRDTOption {
	return func(c *crdt) {
		c.config.broadcastSize = s
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
func NewCRDT(id tla.TLAValue, peerIds []tla.TLAValue, addressMappingFn CRDTAddressMappingFn,
	crdtValue CRDTValue, opts ...CRDTOption) distsys.ArchetypeResource {
	listenAddr := addressMappingFn(id)
	peerAddrs := hashmap.New[string]()
	for _, pid := range peerIds {
		peerAddrs.Set(pid, addressMappingFn(pid))
	}

	crdt := &crdt{
		id:        id,
		value:     crdtValue.Init(),
		peerIds:   peerIds,
		peerAddrs: peerAddrs,
		conns:     hashmap.New[*rpc.Client](),
		closeChan: make(chan struct{}),
		mergeVal:  nil,
		config:    defaultCRDTConfig,
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

	return crdt
}

func (res *crdt) Abort() chan struct{} {
	res.stateMu.Lock()
	if res.hasOldValue {
		res.value = res.oldValue
		res.hasOldValue = false
	}
	res.stateMu.Unlock()

	res.exitCSAndMerge()
	return nil
}

func (res *crdt) PreCommit() chan error {
	return nil
}

func (res *crdt) Commit() chan struct{} {
	res.stateMu.Lock()
	res.hasOldValue = false
	res.stateMu.Unlock()

	res.exitCSAndMerge()
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

	if !res.hasOldValue {
		res.oldValue = res.value
		res.hasOldValue = true
	}
	res.value = res.value.Write(res.id, value)

	return nil
}

func (res *crdt) Close() error {
	res.closeChan <- struct{}{}

	res.stateMu.RLock()
	defer res.stateMu.RUnlock()

	var err error
	for _, id := range res.conns.Keys {
		client, _ := res.conns.Get(id)
		if client != nil {
			err = client.Close()
			if err != nil {
				return fmt.Errorf("node %s: could not close connection with node %s: %v\n", res.id, id, err)
			}
		}
	}
	err = res.listener.Close()
	if err != nil {
		return fmt.Errorf("node %s: could not close lister: %v\n", res.id, err)
	}

	log.Printf("node %s: closing with state: %s\n", res.id, res.value)
	return nil
}

// tryConnectPeers tries to connect to peer nodes with timeout. If dialing
// succeeds, retains the client for later RPC.
func (res *crdt) tryConnectPeers(selected []tla.TLAValue) {
	for _, id := range selected {
		addr, _ := res.peerAddrs.Get(id)
		if _, ok := res.conns.Get(id); !ok {
			conn, err := net.DialTimeout("tcp", addr, res.config.dialTimeout)
			if err == nil {
				res.conns.Set(id, rpc.NewClient(conn))
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
			log.Printf("node %s: terminating broadcasts\n", res.id)
			return
		default:
			res.broadcast()
		}
	}
}

func (res *crdt) tryMerge(rcvd CRDTValue) {
	defer res.inCSMu.Unlock()
	res.inCSMu.Lock()

	if !res.inCriticalSection {
		res.stateMu.Lock()
		res.value = res.value.Merge(rcvd)
		res.stateMu.Unlock()
	} else if res.mergeVal == nil {
		res.mergeVal = rcvd
		// log.Printf("node %s: in CS, queuing merge %v\n", res.id, res.mergeVal)
	} else {
		res.mergeVal = res.mergeVal.Merge(rcvd)
		// log.Printf("node %s: in CS, queuing merge %v\n", res.id, res.mergeVal)
	}
}

func (res *crdt) getStableValue() CRDTValue {
	defer res.stateMu.RUnlock()
	res.stateMu.RLock()

	if res.hasOldValue {
		return res.oldValue
	}
	return res.value
}

func (res *crdt) selectRandomPeers() []tla.TLAValue {
	var selected []tla.TLAValue
	for i := 0; len(selected) < res.config.broadcastSize; i++ {
		pid := res.peerIds[i]
		if !pid.Equal(res.id) {
			selected = append(selected, pid)
		}
	}
	return selected
}

func (res *crdt) broadcast() {
	type callWithTimeout struct {
		call        *rpc.Call
		timeoutChan <-chan time.Time
	}

	selected := res.selectRandomPeers()
	res.tryConnectPeers(selected)

	args := ReceiveValueArgs{Value: res.getStableValue()}

	calls := hashmap.New[callWithTimeout]()
	for _, id := range selected {
		if client, ok := res.conns.Get(id); ok {
			var reply ReceiveValueResp
			calls.Set(id, callWithTimeout{
				call:        client.Go("CRDTRPCReceiver.ReceiveValue", args, &reply, nil),
				timeoutChan: time.After(res.config.sendTimeout),
			})
		}
	}

	for _, id := range calls.Keys {
		cwt, _ := calls.Get(id)
		call := cwt.call
		select {
		case <-call.Done:
			if call.Error != nil {
				log.Printf("node %s: could not broadcast to node %s:%v\n", res.id, id, call.Error)
			} else {
				res.tryMerge(call.Reply.(*ReceiveValueResp).Value)
			}
		case <-cwt.timeoutChan:
			log.Printf("node %s: broadcast to node %s timed out\n", res.id, id)
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
	res.inCSMu.Lock()
	if res.mergeVal != nil {
		res.stateMu.Lock()
		res.value = res.mergeVal.Merge(res.value)
		res.mergeVal = nil
		res.stateMu.Unlock()
	}
	res.inCriticalSection = false
	res.inCSMu.Unlock()
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
	// log.Printf("node %s: received value %s\n", res.id, args.Value)

	res.tryMerge(args.Value)
	*reply = ReceiveValueResp{Value: res.getStableValue()}
	return nil
}
