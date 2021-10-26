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

	hasOldState bool
	oldStateMu  sync.RWMutex
	oldState    *immutable.Map
	state       *immutable.Map
	stateMu     sync.RWMutex

	peerAddrs map[tla.TLAValue]string
	peers     map[tla.TLAValue]*rpc.Client
	peersMu   sync.RWMutex

	closeChan chan struct{}
}

var _ distsys.ArchetypeResource = &GCounter{}

type ReceiveValueArgs struct {
	Value *immutable.Map
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
				arg.Value = b.Map()
				return nil
			} else {
				return err
			}
		}
		b.Set(pair.K, pair.V)
	}
}

type ReceiveValueResp struct{}

type GCounterAddressMappingFn func(value tla.TLAValue) string

func init() {
	gob.Register(ReceiveValueArgs{&immutable.Map{}})
}

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

			state:       immutable.NewMap(tla.TLAValueHasher{}),
			oldState:    immutable.NewMap(tla.TLAValueHasher{}),
			hasOldState: false,

			peerAddrs: peerAddrs,
			peers:     make(map[tla.TLAValue]*rpc.Client),

			closeChan: make(chan struct{}),
		}

		rpcServer := rpc.NewServer()
		err := rpcServer.Register(res)
		if err != nil {
			panic(fmt.Errorf("node %s: could not register CRDT RPCs: %w", id.String(), err))
		}
		listner, err := net.Listen("tcp", listenAddr)
		if err != nil {
			panic(fmt.Errorf("node %s: could not listen on address %s: %w", id.String(), listenAddr, err))
		}
		log.Printf("node %s: started listening on %s", id.String(), listenAddr)

		go rpcServer.Accept(listner)
		go res.runBroadcasts(broadcastTimeout)

		return res
	})
}

func (res *GCounter) Abort() chan struct{} {
	res.stateMu.Lock()
	res.oldStateMu.RLock()
	defer res.stateMu.Unlock()
	defer res.oldStateMu.RUnlock()

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
	it := res.state.Iterator()
	for !it.Done() {
		_, v := it.Next()
		value += v.(int32)
	}
	return tla.MakeTLANumber(value), nil
}

func (res *GCounter) WriteValue(value tla.TLAValue) error {
	res.stateMu.Lock()
	res.oldStateMu.Lock()
	defer res.stateMu.Unlock()
	defer res.oldStateMu.Unlock()

	if !value.IsNumber() {
		return distsys.ErrCriticalSectionAborted
	}
	if !res.hasOldState {
		res.oldState = res.state
		res.hasOldState = true
	}
	res.state = res.state.Set(res.id, value.AsNumber())

	return nil
}

func (res *GCounter) Close() error {
	res.closeChan <- struct{}{}

	res.stateMu.RLock()
	res.peersMu.RLock()
	defer res.stateMu.RUnlock()
	defer res.peersMu.RUnlock()

	var err error
	for id, client := range res.peers {
		if client != nil {
			err = client.Close()
			if err != nil {
				fmt.Errorf("node %s: could not close connection with node %s: %w\n", res.id.String(), id.String(), err)
			}
		}
	}

	log.Printf("node %s: closing with state: %s\n", res.id, toString(res.state))
	return nil
}

func (res *GCounter) ReceiveValue(args ReceiveValueArgs, reply *ReceiveValueResp) error {
	log.Printf("node %s: received value %s\n", res.id.String(), toString(args.Value))
	res.stateMu.Lock()
	defer res.stateMu.Unlock()
	res.merge(args.Value)
	return nil
}

func (res *GCounter) merge(other *immutable.Map) {
	it := other.Iterator()
	for !it.Done() {
		id, val := it.Next()
		if v, ok := res.state.Get(id); !ok || v.(int32) > val.(int32) {
			res.state = res.state.Set(id, val)
		}
	}
}

func (res *GCounter) tryConnectPeers() {
	res.peersMu.Lock()
	defer res.peersMu.Unlock()

	for id, addr := range res.peerAddrs {
		if _, ok := res.peers[id]; !ok {
			conn, err := net.DialTimeout("tcp", addr, connectionTimeout)
			if err == nil {
				res.peers[id] = rpc.NewClient(conn)
			}
		}
	}
}

func (res *GCounter) runBroadcasts(timeout time.Duration) {
	type callWithTimeout struct {
		call        *rpc.Call
		timeoutChan <-chan time.Time
	}

	calls := make(map[tla.TLAValue]callWithTimeout, len(res.peers))
	for {
		select {
		case <-res.closeChan:
			log.Printf("node %s: terminating broadcasts\n", res.id.String())
			return
		default:
			time.Sleep(broadcastInterval)
			res.tryConnectPeers()

			if res.hasOldState {
				continue
			}

			res.stateMu.RLock()
			args := ReceiveValueArgs{
				Value: res.state,
			}

			for id, client := range res.peers {
				calls[id] = callWithTimeout{
					call:        client.Go("GCounter.ReceiveValue", args, nil, nil),
					timeoutChan: time.After(timeout),
				}
			}
			res.stateMu.RUnlock()

			for id, cwt := range calls {
				select {
				case <-cwt.call.Done:
					if cwt.call.Error != nil {
						fmt.Errorf("node %s: could not broadcast to node %s:%w\n", res.id.String(), id.String(), cwt.call.Error)
					}
				case <-cwt.timeoutChan:
					fmt.Errorf("node %s: broadcast to node %s timed out\n", res.id.String(), id.String())
				}
			}
		}
	}
}

func toString(imap *immutable.Map) string {
	it := imap.Iterator()
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
