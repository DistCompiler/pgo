package main

import (
	"consensus_kv"
	"fmt"
	"log"
	"net"
	"net/rpc"
	"os"
	"paxos"
	"strconv"
	"strings"
	"sync"
	"time"

	"pgo/distsys"
)

const (
	COMMUNICATION_BUFFER_SIZE = 1000 // buffer size of mailbox or local channel
	CONNECTION_TIMEOUT        = 1000 // time out RPC calls after 1s

	HEARTBEAT_FREQUENCY   = 2 // seconds
	CHECK_HEARTBEAT_EVERY = 1 // seconds

	LEADER_TIMEOUT = 4 // seconds (consider leader to fail if we don't hear from it in LEADER_TIMEOUT)
)

var configuration map[string]string
var aliases map[string]string
var id string
var self int
var connections *distsys.Connections
var barrier *distsys.SyncBarrier
var err error
var address *net.TCPAddr

var mailboxes distsys.ArchetypeResourceCollection

// model variables
var leaderFailure distsys.ArchetypeResourceCollection
var electionInProgress distsys.ArchetypeResourceCollection
var iAmTheLeader distsys.ArchetypeResourceCollection
var decided distsys.ArchetypeResourceCollection
var sleeper distsys.ArchetypeResource
var lastSeen distsys.ArchetypeResource
var timeoutChecker distsys.ArchetypeResource
var heartbeatFrequency distsys.ArchetypeResource
var monitorFrequency distsys.ArchetypeResource
var valueStream distsys.ArchetypeResourceCollection
var upstream *distsys.LocalChannelResource
var consensusChan distsys.ArchetypeResourceCollection
var database *distsys.ArchetypeResourceMap
var requests *distsys.LocalChannelResource

var timestampsLock sync.Mutex
var lastSeenTimestamps []time.Time

func init() {
	if len(os.Args) != 3 {
		fmt.Printf("Usage: %s (process-identifier) (ip-addr)\n", os.Args[0])
	}

	// sanity check
	if paxos.NUM_NODES != consensus_kv.NUM_NODES {
		fatal(fmt.Sprintf("Error: paxos.NUM_NODES = %d, consensus_kv.NUM_NODES = %d", paxos.NUM_NODES, consensus_kv.NUM_NODES))
	}

	// process identifier needs to be in 0..NUM_NODES-1
	self, err = strconv.Atoi(os.Args[1])
	if err != nil || self < 0 || self >= paxos.NUM_NODES {
		fatal(fmt.Sprintf("Invalid process identifier: %v\n", os.Args[1]))
	}

	// validate IP address where server should listen for requests
	if address, err = net.ResolveTCPAddr("tcp", os.Args[2]); err != nil {
		fatal(fmt.Sprintf("Invalid address: %s\n", os.Args[2]))
	}

	id = fmt.Sprintf("Node(%d)", self)
	configuration = map[string]string{
		"Node(0)": "127.0.0.1:2222",
		"Node(1)": "127.0.0.1:3333",
		"Node(2)": "127.0.0.1:4444",
	}

	aliases = map[string]string{
		"Proposer(0)":  "127.0.0.1:2222",
		"Acceptor(3)":  "127.0.0.1:2222",
		"Learner(6)":   "127.0.0.1:2222",
		"Heartbeat(9)": "127.0.0.1:2222",

		"Proposer(1)":   "127.0.0.1:3333",
		"Acceptor(4)":   "127.0.0.1:3333",
		"Learner(7)":    "127.0.0.1:3333",
		"Heartbeat(10)": "127.0.0.1:3333",

		"Proposer(2)":   "127.0.0.1:4444",
		"Acceptor(5)":   "127.0.0.1:4444",
		"Learner(8)":    "127.0.0.1:4444",
		"Heartbeat(11)": "127.0.0.1:4444",
	}

	if _, ok := configuration[id]; !ok {
		fmt.Fprintf(os.Stderr, "Unknown process: %s\n", id)
		os.Exit(1)
	}

	runtimeAddress := configuration[id]
	coordinator := configuration["Node(0)"]
	connections = distsys.NewConnections(runtimeAddress)
	barrier = distsys.NewSyncBarrier(configuration, connections, runtimeAddress, coordinator)

	lastSeenTimestamps = make([]time.Time, paxos.NUM_NODES)

	distsys.RegisterResource(&TimestampTracker{})
	distsys.RegisterResource(&TimeoutChecker{})

	leaderFailure = distsys.NewSingletonCollection(distsys.NewLocalChannel("leaderFailure", COMMUNICATION_BUFFER_SIZE))
	electionInProgress = distsys.NewSingletonCollection(distsys.NewLocallySharedResource("electionInProgress", true))
	iAmTheLeader = distsys.NewSingletonCollection(distsys.NewLocallySharedResource("iAmTheLeader", false))
	decided = distsys.NewSingletonCollection(distsys.NewLocalChannel("decided", COMMUNICATION_BUFFER_SIZE))
	sleeper = distsys.NewSleepResource("sleeper", time.Second)
	lastSeen = NewTimestampTracker("lastSeen", lastSeenTimestamps, &timestampsLock)
	timeoutChecker = NewTimeoutChecker("timeoutChecker", lastSeenTimestamps, &timestampsLock)
	heartbeatFrequency = distsys.NewImmutableResource(HEARTBEAT_FREQUENCY)
	monitorFrequency = distsys.NewImmutableResource(CHECK_HEARTBEAT_EVERY)
	valueStream = distsys.NewSingletonCollection(distsys.NewLocalChannel("valueStream", COMMUNICATION_BUFFER_SIZE))
	upstream = distsys.NewLocalChannel("upstream", COMMUNICATION_BUFFER_SIZE)
	consensusChan = distsys.NewSingletonCollection(distsys.NewLocalChannel("consensusChan", COMMUNICATION_BUFFER_SIZE))
	database = distsys.NewArchetypeResourceMap()
	requests = distsys.NewLocalChannel("requests", COMMUNICATION_BUFFER_SIZE)
}

func fatal(msg string) {
	fmt.Fprintf(os.Stderr, fmt.Sprintf("%s\n", msg))
	os.Exit(1)
}

func makeMailboxRef(name string) *distsys.Mailbox {
	roles := []string{
		fmt.Sprintf("Proposer(%d)", self),
		fmt.Sprintf("Acceptor(%d)", self+paxos.NUM_NODES),
		fmt.Sprintf("Learner(%d)", self+2*paxos.NUM_NODES),
		fmt.Sprintf("Heartbeat(%d)", self+3*paxos.NUM_NODES),
	}

	mbox, err := distsys.MailboxRef(name, 0, connections, aliases, roles, COMMUNICATION_BUFFER_SIZE, CONNECTION_TIMEOUT)
	if err != nil {
		panic(err)
	}

	return mbox
}

func waitBarrier() {
	if err := barrier.WaitPeers(); err != nil {
		fatal(fmt.Sprintf("Error: %v\n", err))
	}
}

//////////////////////////////////////////////
// Timestamp tracking as Archetype Resource //
//////////////////////////////////////////////
type DirtyEntry struct {
	index     int
	timestamp time.Time
}

type TimestampTracker struct {
	name        string
	lastSeen    []time.Time
	writeBuffer *DirtyEntry
	lock        *sync.Mutex
}

func NewTimestampTracker(name string, lastSeen []time.Time, lock *sync.Mutex) *TimestampTracker {
	return &TimestampTracker{
		lastSeen: lastSeen,
		lock:     lock,
		name:     name,
	}
}

func (tt *TimestampTracker) Acquire(_ distsys.ResourceAccess) error {
	tt.lock.Lock()
	return nil
}

// Should never be read
func (tt *TimestampTracker) Read() (interface{}, error) {
	panic("Forbidden operation: reading from timestamp tracking")
}

// updates timestamp associated with the message received (a TLA+ record)
func (tt *TimestampTracker) Write(value interface{}) error {
	msg := value.(map[string]interface{})
	leaderId := msg["leader"].(int)

	tt.writeBuffer = &DirtyEntry{leaderId, time.Now()}
	return nil
}

// update timestamp if we registered a heartbeat
func (tt *TimestampTracker) Release() error {
	defer tt.lock.Unlock()

	if tt.writeBuffer != nil {
		tt.lastSeen[tt.writeBuffer.index] = tt.writeBuffer.timestamp
	}

	return nil
}

// we still want to know about a received heartbeat even if aborting
// the transaction (for some other reason) to avoid starting an
// unnecessary election
func (tt *TimestampTracker) Abort() error {
	return tt.Release()
}

// Lexicographical comparison of names
func (tt *TimestampTracker) Less(other distsys.ArchetypeResource) bool {
	otherResource := other.(*TimestampTracker)
	return strings.Compare(tt.name, otherResource.name) < 0
}

////////////////////////////////////////////
// Timeout checking as Archetype Resource //
////////////////////////////////////////////

type TimeoutChecker struct {
	name     string
	lastSeen []time.Time
	lock     *sync.Mutex
}

func NewTimeoutChecker(name string, lastSeen []time.Time, lock *sync.Mutex) *TimeoutChecker {
	return &TimeoutChecker{
		name:     name,
		lastSeen: lastSeen,
		lock:     lock,
	}
}

func (tc *TimeoutChecker) Acquire(_ distsys.ResourceAccess) error {
	tc.lock.Lock()
	return nil
}

// Checks if the leader timed out
func (tc *TimeoutChecker) Read() (interface{}, error) {
	// we do not know who the leader is: best effort attempt: assume
	// leader is the node whom we heard from last
	var maxTime time.Time
	for _, timeSeen := range tc.lastSeen {
		if maxTime.IsZero() || maxTime.Before(timeSeen) {
			maxTime = timeSeen
		}
	}

	var leaderLastSeen float64
	if !maxTime.IsZero() {
		leaderLastSeen = time.Since(maxTime).Seconds()
	}

	return leaderLastSeen > LEADER_TIMEOUT, nil
}

// should never be written
func (tc *TimeoutChecker) Write(value interface{}) error {
	panic("Forbidden operation: writing to timeout checker")
}

func (tc *TimeoutChecker) Release() error {
	defer tc.lock.Unlock()
	return nil
}

func (tc *TimeoutChecker) Abort() error {
	return tc.Release()
}

// Lexicographical comparison of names
func (tc *TimeoutChecker) Less(other distsys.ArchetypeResource) bool {
	otherResource := other.(*TimeoutChecker)
	return strings.Compare(tc.name, otherResource.name) < 0
}

func setupMailboxes() {
	numNodes := 3 * paxos.NUM_NODES

	// one mailbox per role + separate mailbox for the heartbeat
	// monitor that runs on the proposers
	numMailboxes := numNodes + paxos.NUM_NODES
	connections := make([]distsys.ArchetypeResource, numMailboxes)

	for i := 0; i < paxos.NUM_NODES; i++ {
		connections[i] = makeMailboxRef(fmt.Sprintf("Proposer(%d)", i))
	}

	for i := paxos.NUM_NODES; i < 2*paxos.NUM_NODES; i++ {
		connections[i] = makeMailboxRef(fmt.Sprintf("Acceptor(%d)", i))
	}

	for i := 2 * paxos.NUM_NODES; i < 3*paxos.NUM_NODES; i++ {
		connections[i] = makeMailboxRef(fmt.Sprintf("Learner(%d)", i))
	}

	for i := 3 * paxos.NUM_NODES; i < 4*paxos.NUM_NODES; i++ {
		connections[i] = makeMailboxRef(fmt.Sprintf("Heartbeat(%d)", i))
	}

	mailboxes = distsys.ArchetypeResourceSlice(connections)
}

func backgroundWrapper(name string, fn func() error) {
	go func() {
		err := fn()
		if err != nil {
			panic(fmt.Sprintf("%s: %v", name, err))
		}
	}()
}

func initBackgroundRoutines() {
	// set up proposer
	backgroundWrapper("Proposer", func() error {
		return paxos.AProposer(self, mailboxes, valueStream, leaderFailure, electionInProgress, iAmTheLeader)
	})

	// set up acceptor
	acceptorSelf := self + paxos.NUM_NODES
	backgroundWrapper("Acceptor", func() error {
		return paxos.AAcceptor(acceptorSelf, mailboxes)
	})

	// set up learner
	learnerSelf := acceptorSelf + paxos.NUM_NODES
	backgroundWrapper("Learner", func() error {
		return paxos.ALearner(learnerSelf, mailboxes, decided)
	})

	// set up hearbeat
	heartbeatSelf := learnerSelf + paxos.NUM_NODES
	backgroundWrapper("HeartbeatAction", func() error {
		return paxos.HeartbeatAction(heartbeatSelf, mailboxes, lastSeen, sleeper, electionInProgress, iAmTheLeader, heartbeatFrequency)
	})

	// set up leader monitor
	monitorSelf := heartbeatSelf + paxos.NUM_NODES
	backgroundWrapper("LeaderStatusMonitor", func() error {
		return paxos.LeaderStatusMonitor(monitorSelf, timeoutChecker, leaderFailure, electionInProgress, iAmTheLeader, sleeper, monitorFrequency)
	})

	// set up request manager
	kvRequestsSelf := heartbeatSelf + paxos.NUM_NODES
	backgroundWrapper("KeyValueRequests", func() error {
		return consensus_kv.KeyValueRequests(kvRequestsSelf, requests, upstream, iAmTheLeader, valueStream, consensusChan)
	})

	// set up consensus layer
	kvConsensusSelf := kvRequestsSelf + paxos.NUM_NODES
	backgroundWrapper("KeyValuePaxosManager", func() error {
		return consensus_kv.KeyValuePaxosManager(kvConsensusSelf, consensusChan, decided, database)
	})
}

// Key-Value RPC request/response
type KVService struct {
	tcpAddress    *net.TCPAddr
	requestStream *distsys.LocalChannelResource
	learnedStream *distsys.LocalChannelResource
}

func NewKVService(addr *net.TCPAddr, requestStream *distsys.LocalChannelResource, learnedStream *distsys.LocalChannelResource) *KVService {
	return &KVService{
		tcpAddress:    addr,
		requestStream: requestStream,
		learnedStream: learnedStream,
	}
}

func (kv *KVService) Get(get map[string]string, response *map[string]string) error {
	log.Printf("Get(%s)", get["key"])

	req := map[string]interface{}{
		"type": consensus_kv.GET_MSG(),
		"key":  get["key"],
	}

	kv.requestStream.Send(req)
	resp := kv.learnedStream.Receive().(map[string]interface{})
	(*response)["type"] = resp["type"].(string)

	var val string
	var ok bool
	if val, ok = resp["result"].(string); !ok {
		(*response)["result"] = ""
	} else {
		(*response)["result"] = val
	}

	return nil
}

func (kv *KVService) Put(put map[string]string, response *map[string]string) error {
	log.Printf("Put(%s, %s)", put["key"], put["value"])

	req := map[string]interface{}{
		"type":  consensus_kv.PUT_MSG(),
		"key":   put["key"],
		"value": put["value"],
	}

	kv.requestStream.Send(req)
	resp := kv.learnedStream.Receive().(map[string]interface{})
	(*response)["type"] = resp["type"].(string)

	return nil
}

func startServer() {
	listener, err := net.ListenTCP("tcp", address)
	if err != nil {
		panic(err.Error())
	}

	kvService := NewKVService(address, requests, upstream)
	rpc.Register(kvService)

	rpc.Accept(listener)
}

func main() {
	setupMailboxes()

	// wait for all processes to come online
	waitBarrier()

	// set up clients
	initBackgroundRoutines()

	// wait for a leader to be elected
	for {
		time.Sleep(200 * time.Millisecond)

		// LocallySharedResources do not return errors on Read()
		val, _ := electionInProgress.Get(0).Read()

		// if election is not in progress, break
		if !val.(bool) {
			break
		}
	}

	leader, _ := iAmTheLeader.Get(0).Read()
	if leader.(bool) {
		log.Printf("Leader Process")
	}

	log.Printf("Starting server at %s\n", os.Args[2])

	// start RPC server -- blocks
	startServer()
}
