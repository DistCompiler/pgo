package resources

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"log"
	"net"
	"net/rpc"
	"os"
	"sync"
	"time"
)

const (
	broadcastTimeout  = 2 * time.Second
	connectionTimeout = 2 * time.Second
)

type mergeFn func(other crdtValue)

type crdt struct {
	distsys.ArchetypeResourceLeafMixin
	id         tla.TLAValue
	listenAddr string
	listener   net.Listener

	stateMu     sync.RWMutex
	oldValue    crdtValue
	value       crdtValue
	hasOldValue bool

	inCSMu            sync.RWMutex
	inCriticalSection bool
	mergeVal          crdtValue

	peerAddrs *immutable.Map
	peers     *immutable.Map

	closeChan chan struct{}

	logger valueLogger
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
func CRDTMaker(id tla.TLAValue, peers []tla.TLAValue, addressMappingFn CRDTAddressMappingFn, broadcastInterval time.Duration, crdtInitFn CRDTInitFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		listenAddr := addressMappingFn(id)
		b := immutable.NewMapBuilder(tla.TLAValueHasher{})
		for _, pid := range peers {
			b.Set(pid, addressMappingFn(pid))
		}

		crdt := &crdt{
			id:        id,
			value:     crdtInitFn(),
			peerAddrs: b.Map(),
			peers:     immutable.NewMap(tla.TLAValueHasher{}),
			closeChan: make(chan struct{}),
			mergeVal:  nil,

			logger: valueLogger{filename: fmt.Sprintf("%s.txt", id)},
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
		crdt.listener = listener

		crdt.logger.init()

		go rpcServer.Accept(listener)
		go crdt.runBroadcasts(broadcastInterval)

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
	err = res.listener.Close()
	if err != nil {
		log.Printf("node %s: could not close lister: %v\n", res.id, err)
	}

	res.logger.close()

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
func (res *crdt) runBroadcasts(broadcastInterval time.Duration) {

	// a node should broadcast at least once
	var once sync.Once
	once.Do(res.broadcast)

	for {
		select {
		case <-res.closeChan:
			log.Printf("node %s: terminating broadcasts\n", res.id)
			return
		default:
			time.Sleep(broadcastInterval)
			res.broadcast()
		}
	}
}

func (res *crdt) broadcast() {
	type callWithTimeout struct {
		call        *rpc.Call
		timeoutChan <-chan time.Time
	}

	res.tryConnectPeers()

	res.stateMu.RLock()
	defer res.stateMu.RUnlock()

	res.logger.log(res.id, res.value)

	// wait until the value stablizes
	if res.hasOldValue {
		return
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
			timeoutChan: time.After(broadcastTimeout),
		})
	}

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
	Value crdtValue
}

type ReceiveValueResp struct{}

// ReceiveValue receives state from other peer node, and calls the merge function.
// If the resource is currently in critical section, its local value cannot change.
// So it queues up the updates to be merged after exiting critical section.
func (rcvr *CRDTRPCReceiver) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	res := rcvr.crdt
	log.Printf("node %s: received value %s\n", res.id, args.Value)

	// faster pre-flight check if merge is needed
	res.stateMu.RLock()
	mergedVal := res.value.Merge(args.Value)
	if mergedVal.String() == res.value.String() {
		log.Printf("node %s: discarding merge %v\n", res.id, args.Value)
		res.stateMu.RUnlock()
		return nil
	}
	res.stateMu.RUnlock()

	res.inCSMu.Lock()
	if !res.inCriticalSection {
		res.stateMu.Lock()
		res.value = res.value.Merge(args.Value)
		res.stateMu.Unlock()
	} else if res.mergeVal == nil {
		res.mergeVal = args.Value
		log.Printf("node %s: in CS, queuing merge %v\n", res.id, res.mergeVal)
	} else {
		res.mergeVal = res.mergeVal.Merge(args.Value)
		log.Printf("node %s: in CS, queuing merge %v\n", res.id, res.mergeVal)
	}
	res.inCSMu.Unlock()
	return nil
}

type valueLogger struct {
	filename string
	file *os.File
	start time.Time
}

func (l *valueLogger) log(id tla.TLAValue, val crdtValue) {
	elapsed := time.Since(l.start)
	content := fmt.Sprintf("%d:%s:%v\n", elapsed.Milliseconds(), id, val.Read())
	if _, err := l.file.Write([]byte(content)); err != nil {
		log.Fatalf("failed to log value: %v\n", err)
	}
}

func (l *valueLogger) init() {
	if _, err := os.Stat("logs"); os.IsNotExist(err) {
		err = os.Mkdir("logs", os.ModePerm)
	}
	file, err := os.OpenFile(fmt.Sprintf("logs/%s", l.filename), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		log.Fatalf("failed to init logger: %v\n", err)
	}
	l.file = file
	l.start = time.Now()
}

func (l *valueLogger) close() {
 	if err := l.file.Close(); err != nil {
 		log.Fatalf("failed to close logger: %v\n", err)
	}
	l.file = nil
}