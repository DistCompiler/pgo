package resources

import (
	"errors"
	"fmt"
	"log"
	"math"
	"math/rand"
	"net"
	"net/rpc"
	"os"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// NewTwoPC is the function that enables creation of 2PC
// resources.
func NewTwoPC(
	value tla.Value,
	address string,
	replicas []ReplicaHandle,
	archetypeID tla.Value,
	onCreate func(*TwoPCReceiver),
) distsys.ArchetypeResource {
	resource := TwoPCArchetypeResource{
		value:                value,
		oldValue:             value,
		criticalSectionState: notInCriticalSection,
		twoPCState:           initial,
		replicas:             replicas,
		archetypeID:          archetypeID,
		logLevel:             getLogLevelFromEnv(),
		timers:               make(map[string]time.Time),
		version:              0,
		senderTimes:          make(map[tla.Value]int64),
	}
	receiver := makeTwoPCReceiver(&resource, address)
	resource.receiver = &receiver
	if onCreate != nil {
		onCreate(&receiver)
	}
	receiver.listenAndServe()
	// go resource.fetchStateFromReplicas()
	if timersEnabled {
		go func() {
			for {
				time.Sleep(time.Second)
				checkTimers(&resource)
			}
		}()
	}
	return &resource
}

// TwoPCRequestType is the type of 2PC message to a remote node.
type TwoPCRequestType int

const (
	PreCommit TwoPCRequestType = iota
	Commit
	Abort
	// Fetch the most recent state from the majority of replicas
	GetState
)

type rwtype int

const (
	read rwtype = iota
	write
)

type logLevel int

const traceLevel = 4
const debugLevel = 3
const infoLevel = 2
const warnLevel = 1
const offLevel = 0

const defaultLogLevel = offLevel

func getLogLevelFromEnv() logLevel {
	switch os.Getenv("PGO_TWOPC_LOG") {
	case "info":
		return infoLevel
	case "trace":
		return traceLevel
	case "debug":
		return debugLevel
	case "warn":
		return warnLevel
	case "off":
		return offLevel
	case "":
		return defaultLogLevel
	default:
		panic(fmt.Sprint("Unknown log level: {}", os.Getenv("PGO_TWOPC_LOG")))
	}
}

func (requestType TwoPCRequestType) String() string {
	switch requestType {
	case PreCommit:
		return "PreCommit"
	case Commit:
		return "Commit"
	case Abort:
		return "Abort"
	case GetState:
		return "GetState"
	}
	panic("Unknown requestType")
}

// timersEnabled is a flag toggling time collection data. This is useful for debugging.
const timersEnabled = false

const rpcTimeout = 5 * time.Second

const dialTimeout = 3 * time.Second

// exponentialBackoffFactor determines the wait time (lower this to decrease wait time)
const exponentialBackoffFactor = 2

// TwoPCRequest is the message for a 2PC request, typically sent over an RPC
// interface.
type TwoPCRequest struct {
	RequestType TwoPCRequestType
	Value       tla.Value
	Sender      tla.Value
	Version     int
	SenderTime  int64
}

// TwoPCRequest is the corresponding response to a 2PC request, also sent via
// the RPC interface.
type TwoPCResponse struct {
	Accept  bool
	Version int
	Value   tla.Value
}

// TwoPCState defines the state of this resource with respect to the 2PC
// synchronization with remote nodes.
type TwoPCState int

const (
	acceptedPreCommit TwoPCState = iota
	initial
)

func (state TwoPCState) String() string {
	switch state {
	case initial:
		return "initial"
	case acceptedPreCommit:
		return "acceptedPreCommit"
	}
	return "unknown"
}

// CriticalSectionState defines the state of this resource with respect to the
// local critical section.
type CriticalSectionState int

const (
	inUninterruptedCriticalSection CriticalSectionState = iota
	acceptedNewValueInCriticalSection
	notInCriticalSection
	inPreCommit
	hasPreCommitted
	failedPreCommit
)

func (state CriticalSectionState) canAcceptPreCommit() bool {
	return state == inUninterruptedCriticalSection ||
		state == notInCriticalSection ||
		state == failedPreCommit ||
		state == acceptedNewValueInCriticalSection
}

func (state CriticalSectionState) String() string {
	switch state {
	case failedPreCommit:
		return "failedPreCommit"
	case inUninterruptedCriticalSection:
		return "inUninterruptedCriticalSection"
	case acceptedNewValueInCriticalSection:
		return "acceptedNewValueInCriticalSection"
	case notInCriticalSection:
		return "notInCriticalSection"
	case inPreCommit:
		return "inPreCommit"
	case hasPreCommitted:
		return "hasPreCommitted"
	}
	return "unknown"
}

// TwoPCReceiver defines the RPC receiver for 2PC communication. The associated
// functions for this struct are exposed via the RPC interface.
type TwoPCReceiver struct {
	ListenAddr  string
	twopc       *TwoPCArchetypeResource
	listener    net.Listener
	closed      bool
	activeConns []net.Conn
}

func makeTwoPCReceiver(twopc *TwoPCArchetypeResource, ListenAddr string) TwoPCReceiver {
	return TwoPCReceiver{
		ListenAddr:  ListenAddr,
		twopc:       twopc,
		activeConns: []net.Conn{},
	}
}

// Receive is the generic handler for receiving a 2PC request from another node.
func (rcvr *TwoPCReceiver) Receive(arg TwoPCRequest, reply *TwoPCResponse) error {
	if rcvr.closed {
		rcvr.log(warnLevel, "Receive called after the listener was closed!")
	}
	rcvr.log(debugLevel, "[RPC Receive Start %s]", arg)
	twopc := rcvr.twopc
	twopc.enterMutex("CheckSenderTime", write)

	// It's safe to accept old messages from a replica without processing them,
	// since it has already moved on and won't process the response anyways.
	if twopc.senderTimes[arg.Sender] > arg.SenderTime {
		twopc.log(infoLevel, "Ignore old message %s", arg)
		*reply = makeAccept()
		twopc.leaveMutex("CheckSenderTime", write)
		return nil
	} else {
		twopc.senderTimes[arg.Sender] = arg.SenderTime
		twopc.leaveMutex("CheckSenderTime", write)
	}

	err := twopc.receiveInternal(arg, reply)
	rcvr.log(debugLevel, "[RPC Receive End %s] Error: %s", arg, err)
	return err
}

func (res *TwoPCReceiver) log(level logLevel, format string, args ...interface{}) {
	res.twopc.inMutex("log", read, func() {
		res.twopc.log(level, format, args...)
	})
}

// NOTE: This cannot be made as a method of TwoPCReceiver because it
//       is not an RPC call
func CloseTwoPCReceiver(res *TwoPCReceiver) error {
	res.log(infoLevel, "Closing")
	twopc := res.twopc
	twopc.enterMutex("CloseTwoPCReceiver", read)
	defer twopc.leaveMutex("CloseTwoPCReceiver", read)
	err := res.listener.Close()
	for _, conn := range res.activeConns {
		conn.Close()
	}
	twopc.log(infoLevel, "Closed connections")
	return err
}

func GetVersion(res *TwoPCReceiver) int {
	res.twopc.enterMutex("GetVersion", read)
	defer res.twopc.leaveMutex("GetVersion", read)
	return res.twopc.version
}

// ReplicaHandle defines the interface for connecting with 2PC replicas. It is
// functionally the same as the RPC interface.
type ReplicaHandle interface {
	Send(request TwoPCRequest, reply *TwoPCResponse) chan error
	Close() error
}

// LocalReplicaHandle is a structure for interacting with a replica operating in
// the same process (although likely running in a seperate goroutine). This is
// probably only useful for testing.
type LocalReplicaHandle struct {
	receiver *TwoPCArchetypeResource
}

func (handle LocalReplicaHandle) Close() error {
	return nil
}

// Send instructs the local replica to process a 2PC message.
func (handle LocalReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	errorChannel := make(chan error, 1)
	err := handle.receiver.receiveInternal(request, reply)
	errorChannel <- err
	return errorChannel
}

// RPCReplicaHandle is a structure for a reference to a remote 2PC replica.
type RPCReplicaHandle struct {
	address string // Client address

	mutex  sync.RWMutex // Mutex for client initialization
	client *rpc.Client  // RPC Client. Initialized during the first RPC request.

	logLevel    logLevel // Verbosity of logging
	archetypeID tla.Value
}

// MakeRPCReplicaHandle creates a replica handle for the 2PC node available at
// the given address.
func MakeRPCReplicaHandle(address string, archetypeID tla.Value) RPCReplicaHandle {
	return RPCReplicaHandle{
		address:     address,
		logLevel:    getLogLevelFromEnv(),
		archetypeID: archetypeID,
	}
}

func (handle *RPCReplicaHandle) String() string {
	return fmt.Sprintf("%s[connected: %t]", handle.address, handle.client != nil)
}

func (res *RPCReplicaHandle) log(level logLevel, format string, args ...interface{}) {
	if res.logLevel >= level {
		log.Printf(format+"\n", args...)
	}
}

func (handle *RPCReplicaHandle) initClient(recreate bool) (*rpc.Client, error) {
	handle.mutex.Lock()
	defer handle.mutex.Unlock()
	if handle.client == nil || recreate {
		client, err := makeClient(handle.address)
		if err != nil {
			return nil, err
		}
		handle.client = client
		return client, nil
	}
	return handle.client, nil
}

func (handle *RPCReplicaHandle) Close() error {
	handle.mutex.RLock()
	if handle.client != nil {
		return handle.client.Close()
	}
	handle.mutex.RUnlock()
	return nil
}

// Send sends a 2PC request to a remote replica. This function will initiate the
// RPC client for the handle if it has not been initiated yet.
func (handle *RPCReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	handle.log(traceLevel, "RPC call initiated with request %s\n", request)
	assert(reply != nil, "reply was not initialized correctly")
	errorChannel := make(chan error, 1)

	client, err := handle.initClient(false)
	if err != nil {
		handle.log(warnLevel, "Error during client initialization: %s", err)
		errorChannel <- err
		return errorChannel
	}
	handle.log(traceLevel, "Client initialized for request %s\n", request)

	timeout := false
	call := client.Go("TwoPCReceiver.Receive", &request, &reply, nil)
	select {
	case <-call.Done:
	case <-time.After(rpcTimeout):
		timeout = true
	}

	if timeout {
		handle.log(warnLevel, "RPC timeout for %s", request)
		errorChannel <- errors.New("RPC timeout")
	} else if call.Error == rpc.ErrShutdown {
		handle.log(warnLevel, "RPC call encountered ErrShutDown during request %s\n", request)
		// Restart the client now, returning the original error
		// If the restart failed, the next call to `Send` will return the error
		handle.initClient(true)
		errorChannel <- call.Error
	} else if call.Error != nil {
		handle.log(warnLevel, "RPC call encountered an error for request %s: %s\n", request, call.Error)
		errorChannel <- call.Error
	} else {
		handle.log(traceLevel, "RPC call %s completed successfully\n", request)
		errorChannel <- nil
	}

	return errorChannel
}

func GetTwoPCVersion(rpcRcvr *TwoPCReceiver) int {
	return rpcRcvr.twopc.version
}

// listenAndServe initializes the RPC server for listening to incoming 2PC messages
// from remote nodes.
func (rpcRcvr *TwoPCReceiver) listenAndServe() error {
	server := rpc.NewServer()
	err := server.Register(rpcRcvr)
	if err != nil {
		return err
	}

	listener, err := net.Listen("tcp", rpcRcvr.ListenAddr)
	if err != nil {
		return err
	}
	rpcRcvr.listener = listener
	rpcRcvr.log(infoLevel, "Monitor: started listening on %s", rpcRcvr.ListenAddr)
	go func() {
		for {
			conn, err := listener.Accept()
			rpcRcvr.log(infoLevel, "Accept new connection")
			if err != nil {
				rpcRcvr.log(warnLevel, "Failure in listener.Accept(): %s", err)
				return
			}
			rpcRcvr.activeConns = append(rpcRcvr.activeConns, conn)
			go server.ServeConn(conn)
		}
	}()
	return nil
}

func makeClient(address string) (*rpc.Client, error) {
	d := net.Dialer{Timeout: dialTimeout}
	conn, err := d.Dial("tcp", address)
	if err != nil {
		return nil, err
	}
	return rpc.NewClient(conn), nil
}

// TwoPCArchetypeResource is a struct that contains all the necessary data
// structures for the 2PC resource to operate as a local resource and
// communicate with remote 2PC nodes.
type TwoPCArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin

	mutex sync.RWMutex
	// Current value, and value before entering the critical section respectively
	value, oldValue tla.Value
	// State relating to the local critical section
	criticalSectionState CriticalSectionState
	// The PreCommit message that has been accepted
	acceptedPreCommit TwoPCRequest
	// State relating to 2PC replication
	twoPCState TwoPCState
	// Current version (# of accepted commits)
	version int
	// Number of 2PC requests that have not yet received a response
	numInFlightRequests int
	// Channel to wait for all current requests to complete
	allRequestsComplete (chan interface{})
	// The number consecutive precommit failures (for backoff)
	precommitAttempts int
	// The receiver associated with this resource
	receiver *TwoPCReceiver
	// Whether or not Close() has been called on this resource
	closed bool
	// A map of "last-received" times for messages from other nodes.
	senderTimes map[tla.Value]int64

	// Replicas for 2PC
	replicas []ReplicaHandle

	archetypeID tla.Value

	// Logging verbosity
	logLevel logLevel

	// Initial time of in-progress operations, used for debugging only
	timerMutex sync.RWMutex
	timers     map[string]time.Time
}

func (res *TwoPCArchetypeResource) startTiming(key string) {
	if timersEnabled {
		res.timerMutex.Lock()
		res.timers[key] = time.Now()
		res.timerMutex.Unlock()
	}
}

func (res *TwoPCArchetypeResource) stopTiming(key string) {
	if timersEnabled {
		res.timerMutex.Lock()
		delete(res.timers, key)
		res.timerMutex.Unlock()
	}
}

func (res *TwoPCArchetypeResource) time(key string, f func()) {
	res.startTiming(key)
	f()
	res.stopTiming(key)
}

func (res *TwoPCArchetypeResource) enterMutex(name string, typ rwtype) {
	if typ == read {
		res.mutex.RLock()
	} else {
		res.mutex.Lock()
	}
	res.startTiming(fmt.Sprintf("lock-%s", name))
}

func (res *TwoPCArchetypeResource) leaveMutex(name string, typ rwtype) {
	res.stopTiming(fmt.Sprintf("lock-%s", name))
	if typ == read {
		res.mutex.RUnlock()
	} else {
		res.mutex.Unlock()
	}
}

func (res *TwoPCArchetypeResource) inMutex(name string, typ rwtype, action func()) {
	res.enterMutex(name, typ)
	action()
	res.leaveMutex(name, typ)
}

func (res *TwoPCArchetypeResource) escapeMutex(name string, typ rwtype, action func()) {
	res.leaveMutex(name, typ)
	res.time(fmt.Sprintf("escapeMutex-%s-action", name), action)
	res.enterMutex(name, typ)
}

func checkTimers(res *TwoPCArchetypeResource) {
	res.timerMutex.RLock()
	for key, start := range res.timers {
		duration := time.Now().Sub(start)
		if duration > 3*time.Second {
			res.log(warnLevel, "Timer %s: %s", key, duration)
		}
	}
	res.timerMutex.RUnlock()
}

func (res *TwoPCArchetypeResource) rollback() {
	res.enterMutex("rollback", read)
	request := res.makeAbort()
	res.leaveMutex("rollback", read)
	res.broadcastAbortOrCommit(request)
}

// Abort aborts the current critical section state. If this node has already
// completed a 2PC precommit, then it should rollback the PreCommit.
func (res *TwoPCArchetypeResource) Abort() chan struct{} {
	res.inMutex("abort", write, func() {
		res.log(traceLevel, "Abort requested in state %s", res.stateSummary())
		res.value = res.oldValue
		if res.criticalSectionState == hasPreCommitted {
			res.log(traceLevel, "Rollback replicas due to Abort()")
			res.escapeMutex("abort", write, res.rollback)
		}
		res.criticalSectionState = notInCriticalSection
	})
	return nil
}

type sendFunc func(int, ReplicaHandle, func() bool) bool

func (res *TwoPCArchetypeResource) broadcast(name string, f sendFunc) bool {
	res.inMutex("increaseNumInFlightRequests", write, func() {
		res.numInFlightRequests += len(res.replicas)
	})
	var required int
	if len(res.replicas)%2 == 0 {
		required = len(res.replicas) / 2
	} else {
		required = len(res.replicas)/2 + 1
	}
	var remaining = len(res.replicas)
	responses := make(chan bool, len(res.replicas))

	done := false
	var doneMutex sync.RWMutex

	isDone := func() bool {
		doneMutex.RLock()
		defer doneMutex.RUnlock()
		return done
	}

	for i, r := range res.replicas {
		ii := i
		rr := r
		timingKey := fmt.Sprintf("%s_broadcast_%s_%d", res.archetypeID, name, ii)
		go func() {
			res.time(timingKey, func() {
				responses <- f(ii, rr, isDone)
			})
			res.inMutex("decreaseNumInFlightRequests", write, func() {
				res.numInFlightRequests -= 1
				if res.numInFlightRequests == 0 && res.allRequestsComplete != nil {
					res.allRequestsComplete <- true
				}
			})
		}()
	}

	for required > 0 && remaining >= required {
		timingKey := fmt.Sprintf("%s_%s wait response %d/%d/%d", res.archetypeID, name, required, remaining, len(res.replicas))
		res.startTiming(timingKey)
		response := <-responses
		res.stopTiming(timingKey)
		if response {
			required -= 1
		}
		remaining -= 1
	}
	doneMutex.Lock()
	done = true
	doneMutex.Unlock()

	return required == 0
}

// PreCommit attempts to perform a PreCommit on the local critical sectionLocal.
// This triggers the 2PC PreCommit on all relicas. If a majority of replicas
// accept the PreCommit, then this operation succeeds.
//
// This operation also performs exponential backoff: if the previous precommit failed,
// then this will wait a while before performing the PreCommit operation.
func (res *TwoPCArchetypeResource) PreCommit() chan error {
	sleepTime := time.Duration(0)
	res.enterMutex("CalculateBackoff", read)
	initialVersion := res.version
	if res.precommitAttempts > 0 {
		s := rand.NewSource(int64(res.archetypeID.Hash()) + time.Now().UnixNano())

		// We base this constant on the "Square approximation" of the birthday problem
		// https://en.wikipedia.org/wiki/Birthday_problem#Square_approximation
		// i.e in this case we have m = n^2
		// Setting `exponentialBackoffFactor` to 2 ensures there is a rougly 50%
		// chance that two replicas will happen to choose to retry at the same
		// time
		constant := exponentialBackoffFactor * float64(len(res.replicas)*len(res.replicas))

		exponent := math.Pow(2, float64(res.precommitAttempts)) - 1
		maxToWait := int(math.Max(constant*exponent, 1))
		sleepTime = time.Duration(rand.New(s).Intn(maxToWait)) * time.Millisecond
	}
	res.leaveMutex("CalculateBackoff", read)
	channel := make(chan error, 1)
	go func() {
		time.Sleep(sleepTime)
		res.enterMutex("CheckPrecommitInterrupted", read)
		if res.version != initialVersion || res.twoPCState == acceptedPreCommit {
			res.log(infoLevel, "Accepted a PreCommit or Commit while sleeping, abort CS")
			channel <- distsys.ErrCriticalSectionAborted
			res.leaveMutex("CheckPrecommitInterrupted", read)
			return
		}
		res.leaveMutex("CheckPrecommitInterrupted", read)
		res.time("PreCommit", func() {
			channel <- res.doPreCommit()
		})
	}()
	return channel
}

// doPreCommit implements the actual preCommit logic. PreCommit calls this function
// after possibly waiting due to exponential backoff
func (res *TwoPCArchetypeResource) doPreCommit() error {
	res.enterMutex("PreCommit", write)
	res.log(traceLevel, "[Enter PreCommit] Value: %s", res.value)

	if res.shouldAbortPreCommit() {
		res.log(traceLevel,
			"[Exit PreCommit] PreCommit for %s aborted locally. %s",
			res.value,
			res.stateSummary(),
		)
		res.leaveMutex("PreCommit", write)
		return distsys.ErrCriticalSectionAborted
	}
	res.log(traceLevel, "[Enter PreCommit] Value: %s", res.value)
	res.criticalSectionState = inPreCommit
	request := res.makePreCommit()
	res.leaveMutex("PreCommit", write)

	res.startTiming("PreCommit-Broadcast")
	success := res.broadcast("PreCommit", func(i int, r ReplicaHandle, isDone func() bool) bool {
		var reply TwoPCResponse
		timingKey := fmt.Sprintf("SendPreCommit-%d", i)
		res.log(infoLevel, "Send PreCommit to replica %d", i)
		res.startTiming(timingKey)
		errChannel := r.Send(request, &reply)
		err := <-errChannel
		res.stopTiming(timingKey)
		res.enterMutex(fmt.Sprintf("HandlePreCommitResponse-%d", i), write)
		defer res.leaveMutex(fmt.Sprintf("HandlePreCommitResponse-%d", i), write)
		if err != nil {
			res.log(warnLevel, "Encountered error when sending PreCommit message: %s", err)
			return false
		} else if !reply.Accept {
			res.log(debugLevel, "Replica %s rejected the PreCommit", r)
			if reply.Version > res.version {
				res.acceptNewValue(reply.Value, reply.Version)
			}
			return false
		} else {
			return true
		}
	})
	res.stopTiming("PreCommit-Broadcast")

	res.enterMutex("PreCommitComplete", write)
	if !success || res.criticalSectionState == acceptedNewValueInCriticalSection {
		res.leaveMutex("PreCommitComplete", write)
		res.rollback()
		res.inMutex("PreCommitFail", write, func() {
			res.criticalSectionState = failedPreCommit
			res.precommitAttempts += 1
			res.log(traceLevel, "[Exit PreCommit] rollback %s", res.value)
		})
		return distsys.ErrCriticalSectionAborted
	} else {
		assert(
			res.criticalSectionState == inPreCommit,
			fmt.Sprintf(
				"%s: Critical Section Changed to %s during PreCommit!",
				res.archetypeID,
				res.criticalSectionState,
			),
		)
		res.precommitAttempts = 0
		res.criticalSectionState = hasPreCommitted
		res.log(infoLevel, "[Exit PreCommit] Succeeded for %s", res.value)
		res.leaveMutex("PreCommitComplete", write)
		return nil
	}
}

func (res *TwoPCArchetypeResource) isClosed() bool {
	res.enterMutex("isClosed", read)
	defer res.leaveMutex("isClosed", read)
	return res.closed
}

// Commit unconditionally commits the local critical section, also performing
// the 2PC commit at this time. This is safe because PreCommit has already
// succeeded, thus all Replicas have already accepted the PreCommit and are able
// to accept the Commit() message.
func (res *TwoPCArchetypeResource) Commit() chan struct{} {
	res.startTiming("Commit")
	defer res.stopTiming("Commit")
	assert(!res.closed, "Commit() was called after the resource was already closed.")
	assert(
		res.criticalSectionState == hasPreCommitted,
		fmt.Sprintf("%s: Commit() called from CS State %s", res.archetypeID, res.criticalSectionState),
	)
	assert(res.twoPCState != acceptedPreCommit, "Commit() called, but we have already accepted a PreCommit!")

	originalVersion := res.version
	originalValue := res.value
	request := res.makeCommit()

	res.broadcastAbortOrCommit(request)

	res.inMutex("FinishCommit", write, func() {
		// Subtle edge case: It's possible that between the time this node has sent the `commit`
		// messages to a majority and received the response, another node has already successfully
		// sent a pre-commit to a distinct majority (not including this node), and has subsequently sent
		// a commit message to this node (which it must accept).
		//
		// In this case, we don't need to update the value here. Note that any
		// intermediate reads / writes would not see the new committed value
		// until the critical section has completed here.
		if res.version == originalVersion {
			res.oldValue = res.value
			res.version += 1
		}
		res.criticalSectionState = notInCriticalSection
		res.log(infoLevel, "Commit(%s) complete", originalValue)
	})
	return nil
}

// ReadValue reads the current value, potential aborting the local critical section
func (res *TwoPCArchetypeResource) ReadValue() (tla.Value, error) {
	res.enterMutex("ReadValue", read)
	defer res.leaveMutex("ReadValue", read)
	if res.criticalSectionPermanentlyFailed() {
		res.log(traceLevel, "ReadValue() not allowed: the critical section has permanently failed")
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	}
	if res.criticalSectionState == notInCriticalSection {
		res.log(traceLevel, "Entering critical section due to ReadValue()")
		res.criticalSectionState = inUninterruptedCriticalSection
	}
	return res.value, nil
}

// WriteValue writes the given value, potential aborting the local critical state
func (res *TwoPCArchetypeResource) WriteValue(value tla.Value) error {
	res.enterMutex("WriteValue", write)
	defer res.leaveMutex("WriteValue", write)
	if res.criticalSectionPermanentlyFailed() {
		res.log(traceLevel, "WriteValue() not allowed: the critical section has permanently failed")
		return distsys.ErrCriticalSectionAborted
	}
	res.value = value
	if res.criticalSectionState == notInCriticalSection {
		res.log(traceLevel, "Entering critical section due to WriteValue()")
		res.criticalSectionState = inUninterruptedCriticalSection
	}
	return nil
}

// Close cleanly shuts down this 2PC instance.
// NOTE: For now, we keep the listener running
func (res *TwoPCArchetypeResource) Close() error {
	res.enterMutex("close", write)
	defer res.leaveMutex("close", write)
	res.closed = true
	assert(res.criticalSectionState != inPreCommit, "Close() called in state inPreCommit")
	assert(res.criticalSectionState != hasPreCommitted, "Close() called in state hasPreCommitted")
	if res.numInFlightRequests > 0 {
		res.allRequestsComplete = make(chan interface{}, 1)
		res.escapeMutex("close", write,
			func() {
				<-res.allRequestsComplete
			},
		)
	}
	res.log(infoLevel, "Closed 2PC Instance")
	for _, handle := range res.replicas {
		handle.Close()
	}
	return nil
}

func (res *TwoPCArchetypeResource) inCriticalSection() bool {
	return res.criticalSectionState != notInCriticalSection
}

// criticalSectionPermanentlyFailed returns true iff this node has accepted a
// 2PC commit while inside a critical section. In that case, the current
// critical section must abort to maintain serializability.
func (res *TwoPCArchetypeResource) criticalSectionPermanentlyFailed() bool {
	return res.criticalSectionState == acceptedNewValueInCriticalSection ||
		res.criticalSectionState == failedPreCommit
}

func (res *TwoPCArchetypeResource) shouldAbortPreCommit() bool {
	return res.criticalSectionPermanentlyFailed() ||
		res.twoPCState == acceptedPreCommit
}

// SetReplicas updates the replicas used for 2PC replication. This function is
// only for testing; things will likely break if this is called during 2PC
// operation.
func (res *TwoPCArchetypeResource) SetReplicas(replicas []ReplicaHandle) {
	res.replicas = replicas
}

func (res *TwoPCArchetypeResource) stateSummary() string {
	if res.twoPCState == acceptedPreCommit {
		return fmt.Sprintf(
			"CS State: %s, accepted precommit from %s",
			res.criticalSectionState,
			res.acceptedPreCommit.Sender,
		)
	} else {
		return fmt.Sprintf(
			"CS State: %s, 2PC State initial",
			res.criticalSectionState,
		)
	}

}

// TwoPC Related Functions

// receiveInternal is the handler for receiving a 2PC message.
// PreCommit: Accept iff we have not yet accepted a PreCommit nor instantiated
//            our own PreCommit. If we accepted, and we are currently inside a
//            critical section, any local actions will fail until we abort.
//
// Commit: Unconditionally accept a commmit. If we are currently inside a
//         critical section, the critical section *must* fail.
//
// Abort: Throw out the PreCommit data. If the critical section hasn't failed
//        permanenently (i.e. by already having accepted a commit), then actions
//        are now allowed.
func (twopc *TwoPCArchetypeResource) receiveInternal(arg TwoPCRequest, reply *TwoPCResponse) error {
	twopc.enterMutex("receiveInternal", write)
	defer twopc.leaveMutex("receiveInternal", write)
	twopc.log(
		traceLevel,
		"Received 2PC message %s. %s",
		arg,
		twopc.stateSummary(),
	)
	if arg.RequestType == GetState {
		*reply = TwoPCResponse{Value: twopc.oldValue, Version: twopc.version}
		return nil
	}

	if arg.Version > twopc.version+1 {
		twopc.log(
			infoLevel,
			"%s message (version %d) from %s is higher than expected %d",
			arg.RequestType,
			arg.Version, arg.Sender, twopc.version+1)
	} else if arg.Version < twopc.version+1 {
		twopc.log(
			infoLevel,
			"%s message (version %d) from %s is lower than expected %d",
			arg.RequestType,
			arg.Version, arg.Sender, twopc.version+1)
		*reply = twopc.makeReject(true)
		return nil
	}
	switch arg.RequestType {
	case PreCommit:
		*reply = twopc.makeReject(false)
		if twopc.twoPCState == acceptedPreCommit &&
			twopc.acceptedPreCommit.Version == arg.Version &&
			twopc.acceptedPreCommit.Sender == arg.Sender &&
			twopc.acceptedPreCommit.Value == arg.Value {
			*reply = makeAccept()
		} else if twopc.criticalSectionState.canAcceptPreCommit() && (twopc.twoPCState == initial ||
			twopc.acceptedPreCommit.Version < arg.Version ||
			(twopc.acceptedPreCommit.Version == arg.Version &&
				twopc.acceptedPreCommit.Sender == arg.Sender)) {
			twopc.setTwoPCState(acceptedPreCommit)
			twopc.log(debugLevel, "Accepted PreCommit message %s.", arg.Value)
			*reply = makeAccept()
			twopc.acceptedPreCommit = arg
			twopc.log(
				debugLevel,
				"After accepting PreCommit: CS State: %s, 2PC State: %s.",
				twopc.twoPCState,
				twopc.criticalSectionState,
			)
		}
	case Commit:
		twopc.log(infoLevel, "Accepted Commit %s", arg)
		twopc.acceptNewValue(arg.Value, arg.Version)
		*reply = makeAccept()
	case Abort:
		*reply = makeAccept()
		if arg.Sender != twopc.acceptedPreCommit.Sender {
			twopc.log(
				debugLevel,
				"Received Abort message from proposer %s, but the PreCommit was from %s",
				arg.Sender,
				twopc.acceptedPreCommit.Sender,
			)
		} else if twopc.twoPCState != acceptedPreCommit {
			twopc.log(
				debugLevel,
				"Received 'Abort' message, but was in state %s",
				twopc.twoPCState,
			)
		} else {
			twopc.setTwoPCState(initial)
		}
	}
	return nil
}

func (res *TwoPCArchetypeResource) broadcastAbortOrCommit(request TwoPCRequest) {
	originalVersion := res.version

	res.broadcast(request.RequestType.String(), func(i int, r ReplicaHandle, isDone func() bool) bool {

		shouldRetry := func() bool {
			res.enterMutex("ShouldRetry", read)
			defer res.leaveMutex("ShouldRetry", read)
			return res.version == originalVersion
		}

		for shouldRetry() {
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			err := <-call
			if err != nil {
				res.log(warnLevel, "Error during %s RPC to %i: %s (will retry)", request.RequestType, i, err)
				time.Sleep(1 * time.Second)
			} else {
				if !reply.Accept {
					assert(
						reply.Version > originalVersion,
						fmt.Sprintf(
							"Our %s was rejected by another node with the same version",
							request.RequestType,
						),
					)
					res.inMutex("RejectedAbortOrCommit", write, func() {
						if reply.Version > res.version {
							res.acceptNewValue(reply.Value, reply.Version)
						}
					})
				}
				break
			}
		}
		return true
	})
}

func (res *TwoPCArchetypeResource) log(level logLevel, format string, args ...interface{}) {
	if res.logLevel >= level {
		printfArgs := append([]interface{}{res.archetypeID, res.version}, args...)
		log.Printf("%s(%d): "+format+"\n", printfArgs...)
	}
}

func (res *TwoPCArchetypeResource) fetchStateFromReplicas() {
	getStateRequest := TwoPCRequest{
		RequestType: GetState,
		Sender:      res.archetypeID,
	}
	go res.broadcast("Fetch", func(i int, r ReplicaHandle, isDone func() bool) bool {
		var response TwoPCResponse
		r.Send(getStateRequest, &response)
		res.inMutex("fetchState", write, func() {
			if response.Version > res.version {
				res.acceptNewValue(response.Value, response.Version)
			}
		})
		return true
	})
}

func (res *TwoPCArchetypeResource) setTwoPCState(newState TwoPCState) {
	res.log(traceLevel, "Update twoPC state: %s -> %s", res.twoPCState, newState)
	res.twoPCState = newState
}

func (res *TwoPCArchetypeResource) acceptNewValue(value tla.Value, version int) {
	assert(version > res.version, "New version is not greater than current version")
	res.log(infoLevel, "Accept new value: %s %d", value, version)
	res.version = version
	res.value = value
	res.oldValue = value
	res.precommitAttempts = 0 // progress has been made, reset the counter
	if res.twoPCState == acceptedPreCommit && res.acceptedPreCommit.Version <= version {
		res.setTwoPCState(initial)
	}
	if res.inCriticalSection() {
		res.criticalSectionState = acceptedNewValueInCriticalSection
	}
}

func (res *TwoPCArchetypeResource) makeCommit() TwoPCRequest {
	return TwoPCRequest{
		RequestType: Commit,
		Value:       res.value,
		Sender:      res.archetypeID,
		Version:     res.version + 1,
		SenderTime:  time.Now().UnixNano(),
	}
}

func (res *TwoPCArchetypeResource) makeAbort() TwoPCRequest {
	return TwoPCRequest{
		RequestType: Abort,
		Sender:      res.archetypeID,
		Version:     res.version + 1,
		SenderTime:  time.Now().UnixNano(),
	}
}

func (res *TwoPCArchetypeResource) makePreCommit() TwoPCRequest {
	return TwoPCRequest{
		RequestType: PreCommit,
		Value:       res.value,
		Sender:      res.archetypeID,
		Version:     res.version + 1,
		SenderTime:  time.Now().UnixNano(),
	}
}

func (res *TwoPCArchetypeResource) makeReject(includeCurrentValue bool) TwoPCResponse {
	return TwoPCResponse{
		Accept:  false,
		Version: res.version,
		Value:   res.oldValue,
	}
}

func makeAccept() TwoPCResponse {
	return TwoPCResponse{
		Accept: true,
	}
}

func assert(condition bool, message string) {
	if !condition {
		panic(message)
	}
}
