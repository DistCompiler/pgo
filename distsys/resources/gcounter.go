package resources

import (
	"bytes"
	"encoding/gob"
	"errors"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"io"
	"log"
	"net"
	"net/rpc"
	"strings"
	"sync"
	"time"
)

const (
	broadcastTimeout  = 2 * time.Second
	broadcastInterval = 5 * time.Second
	connectionTimeout = 2 * time.Second
)

type GCounter struct {
	distsys.ArchetypeResourceLeafMixin
	id         tla.TLAValue
	listenAddr string

	state *GCounterState

	peerAddrs *immutable.Map

	peersMu sync.RWMutex
	peers   *immutable.Map

	closeChan chan struct{}
}

var _ distsys.ArchetypeResource = &GCounter{}

type GCounterState struct {
	stateMu     sync.RWMutex
	oldValue    counters
	value       counters
	hasOldValue bool
}

type counters struct {
	*immutable.Map
}

func (c counters) String() string {
	it := c.Iterator()
	b := strings.Builder{}
	b.WriteString("map[")
	first := true
	for !it.Done() {
		if first {
			first = false
		} else {
			b.WriteString(" ")
		}
		k, v := it.Next()
		b.WriteString(k.(tla.TLAValue).String())
		b.WriteString(":")
		b.WriteString(fmt.Sprint(v))
	}
	b.WriteString("]")
	return b.String()
}

type GCounterAddressMappingFn func(value tla.TLAValue) string

/*
GCounterMaker returns a GCounter archetype resource implementing the behaviour of a shared grow-only counter.
Given the list of peer ids, it starts broadcasting local counters to all its peers every broadcastInterval.
It also starts accepting incoming RPC calls from peers to receive and merge counter states.
Note that local counter state is currently not persisted. TODO: Persist local state on Commit, reload on restart
*/
func GCounterMaker(id tla.TLAValue, peers []tla.TLAValue, addressMappingFn GCounterAddressMappingFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		listenAddr := addressMappingFn(id)
		b := immutable.NewMapBuilder(tla.TLAValueHasher{})
		for _, pid := range peers {
			b.Set(pid, addressMappingFn(pid))
		}

		res := &GCounter{
			id:         id,
			listenAddr: addressMappingFn(id),
			state: &GCounterState{
				oldValue:    counters{immutable.NewMap(tla.TLAValueHasher{})},
				value:       counters{immutable.NewMap(tla.TLAValueHasher{})},
				hasOldValue: false,
				stateMu:     sync.RWMutex{},
			},
			peerAddrs: b.Map(),
			peers:     immutable.NewMap(tla.TLAValueHasher{}),
			closeChan: make(chan struct{}),
		}

		rpcServer := rpc.NewServer()
		err := rpcServer.Register(&GCounterRPCReceiver{gcounter: res})
		if err != nil {
			log.Panicf("node %s: could not register CRDT RPCs: %w", id, err)
		}
		listner, err := net.Listen("tcp", listenAddr)
		if err != nil {
			log.Panicf("node %s: could not listen on address %s: %w", id, listenAddr, err)
		}
		log.Printf("node %s: started listening on %s", id, listenAddr)

		go rpcServer.Accept(listner)
		go res.runBroadcasts(broadcastTimeout)

		return res
	})
}

func (res *GCounter) Abort() chan struct{} {
	res.state.stateMu.Lock()
	defer res.state.stateMu.Unlock()

	s := res.state
	if s.hasOldValue {
		s.value = s.oldValue
		s.hasOldValue = false
	}
	return nil
}

func (res *GCounter) PreCommit() chan error {
	return nil
}

func (res *GCounter) Commit() chan struct{} {
	res.state.stateMu.Lock()
	res.state.hasOldValue = false
	res.state.stateMu.Unlock()
	return nil
}

func (res *GCounter) ReadValue() (tla.TLAValue, error) {
	res.state.stateMu.RLock()
	defer res.state.stateMu.RUnlock()

	var value int32 = 0
	it := res.state.value.Iterator()
	for !it.Done() {
		_, v := it.Next()
		value += v.(int32)
	}
	return tla.MakeTLANumber(value), nil
}

func (res *GCounter) WriteValue(value tla.TLAValue) error {
	res.state.stateMu.Lock()
	defer res.state.stateMu.Unlock()

	state := res.state
	if !value.IsNumber() {
		return distsys.ErrCriticalSectionAborted
	}
	if !state.hasOldValue {
		state.oldValue = res.state.value
		state.hasOldValue = true
	}
	state.value = counters{state.value.Set(res.id, value.AsNumber())}

	return nil
}

func (res *GCounter) Close() error {
	res.closeChan <- struct{}{}

	res.state.stateMu.RLock()
	res.peersMu.RLock()
	defer res.state.stateMu.RUnlock()
	defer res.peersMu.RUnlock()

	var err error
	it := res.peers.Iterator()
	for !it.Done() {
		id, client := it.Next()
		if client != nil {
			err = client.(*rpc.Client).Close()
			if err != nil {
				log.Printf("node %s: could not close connection with node %s: %w\n", res.id, id, err)
			}
		}
	}

	log.Printf("node %s: closing with state: %s\n", res.id, res.state.value.String())
	return nil
}

/*
Merges current state value with other by taking the greater of each node's partial counts.
Assumes lock for state are preheld.
*/
func (res *GCounter) merge(other counters) {
	it := other.Iterator()
	state := res.state
	for !it.Done() {
		id, val := it.Next()
		if v, ok := state.value.Get(id); !ok || v.(int32) > val.(int32) {
			state.value = counters{state.value.Set(id, val)}
		}
	}
}

/*
Tries to connect to peer nodes with timeout. If dialing suceeds, retains the client for later RPC.
*/
func (res *GCounter) tryConnectPeers() {
	res.peersMu.Lock()
	defer res.peersMu.Unlock()

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

/*
Starts broadcasting to peer nodes of commited state value.
On every broadcastInterval, the method checks if resource is currently holds uncommited state. If it does, it skips braodcast.
If resource state is committed, it calls ReceiveValue RPC on each peer with timeout.
*/
func (res *GCounter) runBroadcasts(timeout time.Duration) {
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

			res.state.stateMu.RLock()

			// wait until the value stablizes
			if res.state.hasOldValue {
				continue
			}

			args := ReceiveValueArgs{
				Value: res.state.value,
			}

			b := immutable.NewMapBuilder(tla.TLAValueHasher{})
			it := res.peers.Iterator()
			for !it.Done() {
				id, client := it.Next()
				b.Set(id, callWithTimeout{
					call:        client.(*rpc.Client).Go("GCounterRPCReceiver.ReceiveValue", args, nil, nil),
					timeoutChan: time.After(timeout),
				})
			}
			res.state.stateMu.RUnlock()

			calls := b.Map()
			it = calls.Iterator()
			for !it.Done() {
				id, cwt := it.Next()
				call := cwt.(callWithTimeout).call
				select {
				case <-call.Done:
					if call.Error != nil {
						log.Printf("node %s: could not broadcast to node %s:%w\n", res.id, id, call.Error)
					}
				case <-cwt.(callWithTimeout).timeoutChan:
					log.Printf("node %s: broadcast to node %s timed out\n", res.id, id)
				}
			}
		}
	}
}

type GCounterRPCReceiver struct {
	gcounter *GCounter
}

type ReceiveValueArgs struct {
	Value counters
}

type KeyVal struct {
	K tla.TLAValue
	V int32
}

func (arg ReceiveValueArgs) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	it := arg.Value.Iterator()
	for !it.Done() {
		k, v := it.Next()
		pair := KeyVal{K: k.(tla.TLAValue), V: v.(int32)}
		err := encoder.Encode(&pair)
		if err != nil {
			return nil, err
		}
	}
	return buf.Bytes(), nil
}

func (arg *ReceiveValueArgs) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	b := immutable.NewMapBuilder(tla.TLAValueHasher{})
	for {
		var pair KeyVal
		err := decoder.Decode(&pair)
		if err != nil {
			if errors.Is(err, io.EOF) {
				arg.Value = counters{b.Map()}
				return nil
			} else {
				return err
			}
		}
		b.Set(pair.K, pair.V)
	}
}

type ReceiveValueResp struct{}

/*
Receives state from other peer node, and calls the merge function.
*/
func (rcvr *GCounterRPCReceiver) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	res := rcvr.gcounter
	log.Printf("node %s: received value %s\n", res.id, args.Value.String())
	res.state.stateMu.Lock()
	defer res.state.stateMu.Unlock()
	res.merge(args.Value)
	return nil
}

func init() {
	gob.Register(ReceiveValueArgs{counters{}})
}
