package resources

import (
	"math"
	"errors"
	"fmt"
	"math/rand"
	"net"
	"net/rpc"
	"sync"
	"time"
	"log"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// TwoPCRequestType is the type of 2PC message to a remote node; i.e either
// "PreCommit", "Commit", or "Abort"
type TwoPCRequestType int

const timersEnabled = true

const (
	PreCommit TwoPCRequestType = iota
	Commit
	Abort
	GetState
)

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

// TwoPCRequest is the message for a 2PC request, typically sent over an RPC
// interface.
type TwoPCRequest struct {
	RequestType TwoPCRequestType
	Value       tla.TLAValue
	Sender      tla.TLAValue
	Version     int
}

// TwoPCRequest is the corresponding response to a 2PC request, also sent via
// the RPC interface.
type TwoPCResponse struct {
	Accept      bool
	Version     int
	Value       tla.TLAValue
}

// TwoPCReceiver defines the RPC receiver for 2PC communication. The associated
// functions for this struct are exposed via the RPC interface.
type TwoPCReceiver struct {
	ListenAddr string
	done       chan struct{}
	twopc      *TwoPCArchetypeResource
	listener   net.Listener
}

func makeTwoPCReceiver(twopc *TwoPCArchetypeResource, ListenAddr string) TwoPCReceiver {
	return TwoPCReceiver{
		ListenAddr: ListenAddr,
		twopc:      twopc,
		done:       make(chan struct{}),
	}
}

// ReplicaHandle defines the interface for connecting with 2PC replicas. It is
// functionally the same as the RPC interface.
type ReplicaHandle interface {
	Send(request TwoPCRequest, reply *TwoPCResponse) chan error
	getArchetypeID() tla.TLAValue
}

// LocalReplicaHandle is a structure for interacting with a replica operating in
// the same process (although likely running in a seperate goroutine). This is
// probably only useful for testing.
type LocalReplicaHandle struct {
	receiver *TwoPCArchetypeResource
}

func (handle LocalReplicaHandle) getArchetypeID() tla.TLAValue {
	return handle.receiver.archetypeID
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
	address     string      // Client address

	mutex       sync.Mutex  // Mutex for client initialization
	client      *rpc.Client // RPC Client. Initialized during the first RPC request.

	debug       bool        // Whether or not to display debug output
	archetypeID tla.TLAValue
}

func (handle *RPCReplicaHandle) String() string {
	return fmt.Sprintf("%s[connected: %t]", handle.address, handle.client != nil)
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

// Send sends a 2PC request to a remote replica. This function will initiate the
// RPC client for the handle if it has not been initiated yet.
func (handle *RPCReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	handle.log("RPC call initiated with request %s\n", request)
	assert(reply != nil, "reply was not initialized correctly")
	errorChannel := make(chan error, 1)

	client, err := handle.initClient(false)
	if err != nil {
		handle.log("Error during client initialization: %s", err)
		errorChannel <- err
		return errorChannel
	}
	handle.log("Client initialized for request %s\n", request)

	timeout := false
	call := client.Go("TwoPCReceiver.Receive", &request, &reply, nil)
	select {
	case <-call.Done:
	case <-time.After(3 * time.Second):
		timeout = true
	}

	if timeout {
		handle.warn("RPC timeout for %s", request)
		errorChannel <- errors.New("RPC timeout")
	} else if call.Error == rpc.ErrShutdown {
		handle.warn("RPC call encountered ErrShutDown during request %s\n", request)
		handle.initClient(true)
		errorChannel <- call.Error
	} else if call.Error != nil {
		handle.warn("RPC call encountered an error for request %s: %s\n", request, call.Error)
		errorChannel <- call.Error
	} else {
		handle.log("RPC call %s completed successfully\n", request)
		errorChannel <- nil
	}

	return errorChannel
}

func (handle *RPCReplicaHandle) getArchetypeID() tla.TLAValue {
	return handle.archetypeID
}

func GetTwoPCVersion(rpcRcvr *TwoPCReceiver) int {
	return rpcRcvr.twopc.version
}

func SimulateTwoPCFailure(rpcRcvr *TwoPCReceiver) {
	rpcRcvr.twopc.enterMutexNamed("SimulateFailure")

	// Don't attempt to simulate failure if acting as the coordinator, or if it's already been closed
	if rpcRcvr.twopc.closeRequested || rpcRcvr.twopc.criticalSectionState == hasPreCommitted || rpcRcvr.twopc.criticalSectionState == inPreCommit {
		rpcRcvr.twopc.leaveMutexNamed("SimulateFailure")
		return
	}
	rpcRcvr.listener.Close()

	rpcRcvr.twopc.version = 1
	rpcRcvr.twopc.criticalSectionState = notInCriticalSection
	rpcRcvr.twopc.numInFlightRequests = 0
	rpcRcvr.twopc.precommitAttempts = 0
	rpcRcvr.twopc.twoPCState = initial
	rpcRcvr.twopc.oldValue = tla.MakeTLANumber(0)
	rpcRcvr.twopc.value = tla.MakeTLANumber(0)
	rpcRcvr.twopc.allRequestsComplete = nil
	rpcRcvr.twopc.leaveMutexNamed("SimulateFailure")

	time.Sleep(1 * time.Second)
	go rpcRcvr.listenAndServe(nil)
	go rpcRcvr.twopc.fetchStateFromReplicas()
}

func CloseTwoPCReceiver(rpcRcvr *TwoPCReceiver) {
	rpcRcvr.listener.Close()
}

// listenAndServe initializes the RPC server for listening to incoming 2PC messages
// from remote nodes.
func (rpcRcvr *TwoPCReceiver) listenAndServe(done chan *TwoPCArchetypeResource) error {
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
	rpcRcvr.log("Monitor: started listening on %s", rpcRcvr.ListenAddr)
	if done != nil {
		done <- rpcRcvr.twopc
	}
	for {
		conn, err := listener.Accept()
		if err != nil {
			rpcRcvr.log("Failure in listener.Accept(): %s", err)
			select {
			case <-rpcRcvr.done:
				return nil
			default:
				return err
			}
		}
		go server.ServeConn(conn)
	}
	return nil
}

// MakeRPCReplicaHandle creates a replica handle for the 2PC node available at
// the given address.
func MakeRPCReplicaHandle(address string, archetypeID tla.TLAValue) RPCReplicaHandle {
	return RPCReplicaHandle{
		address:     address,
		debug:       false,
		archetypeID: archetypeID,
	}
}

func makeClient(address string) (*rpc.Client, error) {
	d := net.Dialer{Timeout: 3 * time.Second}
	conn, err := d.Dial("tcp", address)
	if err != nil {
		time.Sleep(time.Second)
		conn, err = d.Dial("tcp", address)
		if err != nil {
			return nil, err
		}
	}
	return rpc.NewClient(conn), nil
}

// TwoPCArchetypeResource is a struct that contains all the necessary data
// structures for the 2PC resource to operate as a local resource and
// communicate with remote 2PC nodes.
type TwoPCArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin

	mutex sync.Mutex
	// Current value, and value before entering the critical section respectively
	value, oldValue tla.TLAValue
	// State relating to the local critical section
	criticalSectionState CriticalSectionState
	// The PreCommit message that has been accepted
	acceptedPreCommit TwoPCRequest
	// State relating to 2PC replication
	twoPCState TwoPCState
	// Current version (# of 2PC messages sent)
	version int
	// Number of current requests in-flight
	numInFlightRequests int
	// Channel to wait for all current requests to complete
	allRequestsComplete (chan interface{})
	// The number consecutive precommit failures (for backoff)
	precommitAttempts int
	// Whether or not a close request has already been issued (most likely only useful for testing)
	closeRequested bool

	// Replicas for 2PC
	replicas []ReplicaHandle

	archetypeID tla.TLAValue

	// Whether or not to enable debugging
	debug bool

	// Initial time of in-progress operations, used for debugging only
	timerMutex sync.Mutex
	timers map[string]time.Time

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

func (res *TwoPCArchetypeResource) startTiming(key string) {
	if timersEnabled {
		res.timerMutex.Lock()
		// res.log("Timing Start: %s", key)
		res.timers[key] = time.Now()
		res.timerMutex.Unlock()
	}
}

func (res *TwoPCArchetypeResource) stopTiming(key string) {
	if timersEnabled {
		res.timerMutex.Lock()
		// res.log("Timing Stop: %s", key)
		delete(res.timers, key)
		res.timerMutex.Unlock()
	}
}

func (res *TwoPCArchetypeResource) enterMutex() {
	res.mutex.Lock()
	res.startTiming("lock")
}

func (res *TwoPCArchetypeResource) leaveMutex() {
	res.stopTiming("lock")
	res.mutex.Unlock()
}

func (res *TwoPCArchetypeResource) enterMutexNamed(name string) {
	res.mutex.Lock()
	res.startTiming(fmt.Sprintf("lock-%s", name))
}

func (res *TwoPCArchetypeResource) leaveMutexNamed(name string) {
	res.stopTiming(fmt.Sprintf("lock-%s", name))
	res.mutex.Unlock()
}

func (res *TwoPCArchetypeResource) outsideMutex(action func()) {
	res.leaveMutex()
	action()
	res.enterMutex()
}

func (res *TwoPCArchetypeResource) inMutex(action func()) {
	res.enterMutex()
	action()
	res.leaveMutex()
}

func (res *TwoPCArchetypeResource) inMutexNamed(name string, action func()) {
	res.enterMutexNamed(name)
	action()
	res.leaveMutexNamed(name)
}

func checkTimers(res *TwoPCArchetypeResource) {
	res.timerMutex.Lock()
	for key, start := range res.timers {
		duration := time.Now().Sub(start)
		if duration > 3 * time.Second {
			res.warn("Timer %s: %s", key, duration)
		}
	}
	res.timerMutex.Unlock()
}

func (res *TwoPCArchetypeResource) rollback() {
	res.enterMutexNamed("rollback")
	request := res.makeAbort()
	res.leaveMutexNamed("rollback")
	done := false
	var mutex sync.Mutex
	res.sendToMajority("Abort", func(i int, r ReplicaHandle) bool {
		for {
			mutex.Lock()
			if done {
				mutex.Unlock()
				break
			}
			mutex.Unlock()
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			err := <-call
			if err != nil {
				res.log("Error during abort RPC to %i: %s", i, err)
			} else if !reply.Accept {
				res.log("%i rejected abort", i)
			} else {
				// OK
				break
			}
		}
		return true
	})
	mutex.Lock()
	done = true
	mutex.Unlock()
}

// Abort aborts the current critical section state. If this node has already
// completed a 2PC precommit, then it should rollback the PreCommit.
func (res *TwoPCArchetypeResource) Abort() chan struct{} {
	res.enterMutexNamed("abort")
	// res.log(
	// 	"Aborts 2PC State %s, CS State: %s, replicas %s",
	// 	res.twoPCState,
	// 	res.criticalSectionState,
	// 	res.replicas,
	// )
	res.value = res.oldValue
	if res.criticalSectionState == hasPreCommitted {
		res.log("Rollback replicas due to Abort()")
		res.leaveMutexNamed("abort")
		res.rollback()
		res.enterMutexNamed("abort")
	}
	res.criticalSectionState = notInCriticalSection
	res.leaveMutexNamed("abort")
	return nil
}

func (res *TwoPCArchetypeResource) sendToMajority(name string, f func(int, ReplicaHandle) bool) bool {
	res.inMutexNamed("increaseNumInFlightRequests", func() {
		res.numInFlightRequests += len(res.replicas)
	})
	var required int
	if len(res.replicas) % 2 == 0 {
		required = len(res.replicas) / 2
	} else {
		required = len(res.replicas) / 2 + 1
	}
	var remaining = len(res.replicas)
	responses := make(chan bool, len(res.replicas))

	for i, r := range res.replicas {
		ii := i
		rr := r
		timing_key := fmt.Sprintf("%s_sendToMajority_%s_%d", res.archetypeID, name, i)
		go func() {
			res.startTiming(timing_key)
			responses <- f(ii, rr)
			res.stopTiming(timing_key)
			res.inMutexNamed("decreaseNumInFlightRequests", func() {
				res.numInFlightRequests -= 1
				if res.numInFlightRequests == 0 && res.allRequestsComplete != nil {
					res.allRequestsComplete <- true
				}
			})
		}()
	}

	for required > 0 && remaining >= required {
		timing_key := fmt.Sprintf("%s wait response %d/%d", res.archetypeID, required, remaining)
		res.startTiming(timing_key)
		response := <-responses
		res.stopTiming(timing_key)
		if response {
			required -= 1
	 	}
		remaining -= 1
	}

	return required == 0
}

// PreCommit attempts to perform a PreCommit on the local critical sectionLocal.
// This triggers the 2PC PreCommit on all relicas. If any replica refuses the
// PreCommit(), then the operation will fail.
func (res *TwoPCArchetypeResource) PreCommit() chan error {
	sleepTime := time.Duration(0)
	res.enterMutexNamed("PreCommit1")
	initialVersion := res.version
	if res.precommitAttempts > 0 {
		s := rand.NewSource(int64(res.archetypeID.Hash()) + time.Now().UnixNano())
		constant := float64(5)
		exponent := math.Pow(2, float64(res.precommitAttempts)) - 1
		sleepTime = time.Duration(rand.New(s).Intn(int(constant * exponent))) * time.Millisecond
		res.log("PreCommit Sleep time: %s", sleepTime)
	}
	res.leaveMutexNamed("PreCommit1")
	channel := make(chan error, 1)
	go func(){
		time.Sleep(sleepTime)
		res.enterMutexNamed("PreCommit2")
		if res.version != initialVersion {
			// We handled a commit while we were sleeping. Don't try this precommit
			channel <- distsys.ErrCriticalSectionAborted
			res.leaveMutex()
			return
		}
		res.leaveMutexNamed("PreCommit2")
		res.startTiming("PreCommit")
		channel <- res.preCommit()
		res.stopTiming("PreCommit")
	}()
	return channel
}

// PreCommit attempts to perform a PreCommit on the local critical sectionLocal.
// This triggers the 2PC PreCommit on all relicas. If any replica refuses the
// PreCommit(), then the operation will fail.
func (res *TwoPCArchetypeResource) preCommit() error {
	res.enterMutexNamed("PreCommit3")
	res.log("[Enter PreCommit] Value: %s", res.value)

	if res.shouldAbortPreCommit() {
		res.log("[Exit PreCommit] PreCommit for %s aborted locally", res.value)
		res.leaveMutexNamed("PreCommit3")
		return distsys.ErrCriticalSectionAborted
	}
	res.log("[Enter PreCommit] Value: %s", res.value)
	res.criticalSectionState = inPreCommit
	request := res.makePreCommit()
	res.leaveMutexNamed("PreCommit3")

	success := res.sendToMajority("PreCommit", func(i int, r ReplicaHandle) bool {
		var reply TwoPCResponse
		timingKey := fmt.Sprintf("SendPreCommit-%d", i)
		res.startTiming(timingKey)
		errChannel := r.Send(request, &reply)
		err := <-errChannel
		res.stopTiming(timingKey)
		res.enterMutexNamed(fmt.Sprintf("HandlePreCommitResponse-%d", i))
		defer res.leaveMutexNamed(fmt.Sprintf("HandlePreCommitResponse-%d", i))
		if err != nil {
			res.warn("Encountered error when sending PreCommit message: %s", err)
			return false
		} else if !reply.Accept {
			res.log("Replica %s rejected the PreCommit", r)
			if reply.Version > res.version {
				res.acceptNewValue(reply.Value, reply.Version)
			}
			return false
		} else {
			return true
		}
	})

	res.enterMutexNamed("PreCommitComplete")
	if !success || res.criticalSectionState == acceptedNewValueInCriticalSection {
		res.leaveMutexNamed("PreCommitComplete")
		res.rollback()
		res.inMutexNamed("PreCommitFail", func() {
			res.criticalSectionState = failedPreCommit
			res.precommitAttempts += 1
			res.log("[Exit PreCommit] rollback %s", res.value)
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
		res.log("[Exit PreCommit] Succeeded for %s", res.value)
		res.leaveMutexNamed("PreCommitComplete")
		return nil
	}
}

// Commit unconditionally commits the local critical section, also performing
// the 2PC commit at this time. This is safe because PreCommit has already
// succeeded, thus all Replicas have already accepted the PreCommit and are able
// to accept the Commit() message.
func (res *TwoPCArchetypeResource) Commit() chan struct{} {
	res.startTiming("Commit")
	defer res.stopTiming("Commit")
	assert(
		res.criticalSectionState == hasPreCommitted,
		fmt.Sprintf("%s: Commit() called from CS State %s", res.archetypeID, res.criticalSectionState),
	)
	assert(res.twoPCState != acceptedPreCommit, "Commit() called, but we have already accepted a PreCommit!")

	originalVersion := res.version

	request := res.makeCommit()
	done := false
	var mutex sync.Mutex
	res.sendToMajority("Commit", func(i int, r ReplicaHandle) bool {
		for {
			mutex.Lock()
			if done {
				mutex.Unlock()
				break
			}
			mutex.Unlock()
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			err := <-call
			if err != nil {
				res.log("Error during commit RPC to %i: %s", i, err)
			} else if !reply.Accept {
				res.enterMutexNamed("RejectedCommit")
				if reply.Version > originalVersion {
					if (reply.Version > res.version) {
						res.acceptNewValue(reply.Value, reply.Version)
					}
				} else {
					res.warn("%i rejected commit %s with %s! We should be dead!", i, request, reply)
				}
				res.leaveMutexNamed("RejectedCommit")
				break
			} else {
				// OK
				break
			}
		}
		return true
	})
	mutex.Lock()
	done = true
	mutex.Unlock()

	res.inMutexNamed("FinishCommit", func() {
		// Subtle edge case: It's possible that between the time this node has sent the `commit`
		// messages to a majority and received the response, another node has already successfully
		// sent a pre-commit to a distinct majority (not including this node), and has subsequently sent
		// a commit message to this node (which it must accept).
		//
		// In this case, we don't need to update the value here. Note that any
		// intermediate reads / writes would not see the new committed value
		// until the critical section has completed here.
		if res.version == originalVersion {
			res.log("Commit(%s) has been sent to a majority of replicas", res.value)
			res.oldValue = res.value
			res.version += 1
			res.log("Commit(%s) complete", res.value)
		}
		res.criticalSectionState = notInCriticalSection
	})
	return nil
}

// ReadValue reads the current value, potential aborting the local critical
func (res *TwoPCArchetypeResource) ReadValue() (tla.TLAValue, error) {
	res.enterMutexNamed("ReadValue")
	defer res.leaveMutexNamed("ReadValue")
	if res.criticalSectionPermanentlyFailed() {
		// res.log("ReadValue() rejected")
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
	// res.log("ReadValue() allowed: %s", res.value)
	res.criticalSectionState = inUninterruptedCriticalSection
	return res.value, nil
}

// WriteValue writes the given value, potential aborting the local critical state
func (res *TwoPCArchetypeResource) WriteValue(value tla.TLAValue) error {
	res.enterMutexNamed("WriteValue")
	defer res.leaveMutexNamed("WriteValue")
	if res.criticalSectionPermanentlyFailed() {
		res.log("WriteValue() rejected")
		return distsys.ErrCriticalSectionAborted
	}
	res.log("WriteValue() allowed")
	res.value = value
	res.criticalSectionState = inUninterruptedCriticalSection
	return nil
}

// Close cleanly shuts down this 2PC instance.
func (res *TwoPCArchetypeResource) Close() error {
	res.enterMutexNamed("close")
	res.closeRequested = true
	if res.numInFlightRequests > 0 {
		res.allRequestsComplete = make (chan interface{}, 1)
		res.leaveMutexNamed("close")
		<-res.allRequestsComplete
	} else {
		res.leaveMutexNamed("close")
	}
	res.log("Closed 2PC Instance")
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

// EnableDebug enables debug messages for this resource
func (res *TwoPCArchetypeResource) EnableDebug() {
	res.debug = true
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
	twopc.enterMutexNamed("receiveInternal")
	defer twopc.leaveMutexNamed("receiveInternal")
	twopc.log(
		"Received 2PC message %s. CS State: %s, 2PC State: %s.",
		arg,
		twopc.twoPCState,
		twopc.criticalSectionState,
	)
	if(arg.RequestType == GetState) {
		*reply = TwoPCResponse{ Value: twopc.oldValue, Version: twopc.version }
		return nil
	}
	higherVersionMessage := arg.Version > twopc.version + 1
	if higherVersionMessage {
		twopc.log(
			"%s message (version %d) from %s is higher than expected %d",
			arg.RequestType,
			arg.Version, arg.Sender, twopc.version + 1)
	} else if(arg.Version < twopc.version + 1) {
		twopc.log(
			"%s message (version %d) from %s is lower than expected %d",
			arg.RequestType,
			arg.Version, arg.Sender, twopc.version + 1)
        if arg.RequestType == Abort {
			*reply = makeAccept()
		} else {
			*reply = twopc.makeReject(true)
		}
		return nil
	}
	switch arg.RequestType {
	case PreCommit:
		*reply = twopc.makeReject(false)
		if twopc.twoPCState == acceptedPreCommit {
			if (twopc.acceptedPreCommit.Sender == arg.Sender && twopc.version == arg.Version - 1) {
				// Duplicate precommit request
				*reply = makeAccept()
			} else {
				twopc.log("Rejected PreCommit %s: already accepted PreCommit %s", arg, twopc.acceptedPreCommit)
			}
		} else if twopc.criticalSectionState == hasPreCommitted {
			twopc.log("Rejected PreCommit message %s: already PreCommitted.", arg.Value)
		} else if twopc.criticalSectionState == inPreCommit {
			twopc.log("Rejected PreCommit message %s: in precommit.", arg.Value)
		} else {
			twopc.twoPCState = acceptedPreCommit
			twopc.log("Accepted PreCommit message %s.", arg.Value)
			*reply = makeAccept()
			twopc.acceptedPreCommit = arg
			twopc.log(
				"After accepting PreCommit: CS State: %s, 2PC State: %s.",
				twopc.twoPCState,
				twopc.criticalSectionState,
			)
		}
	case Commit:
		twopc.log("Accepted Commit %s", arg)
		twopc.twoPCState = initial
	    twopc.acceptNewValue(arg.Value, arg.Version)
		*reply = makeAccept()
	case Abort:
		// Always accept in the reply, since this means an abort wasn't necessary
		*reply = makeAccept()
		if arg.Sender != twopc.acceptedPreCommit.Sender {
			twopc.log(
				"Received Abort message from proposer %s, but the PreCommit was from %s",
				arg.Sender,
				twopc.acceptedPreCommit.Sender,
			)
		} else if twopc.twoPCState != acceptedPreCommit {
			twopc.log(
				"Received 'Abort' message, but was in state %s",
				twopc.twoPCState,
			)
		} else {
			twopc.twoPCState = initial
		}
	}
	return nil
}

// Receive is the generic handler for receiving a 2PC request from another node.
func (rcvr *TwoPCReceiver) Receive(arg TwoPCRequest, reply *TwoPCResponse) error {
	rcvr.log("[RPC Receive Start %s]", arg)
	twopc := rcvr.twopc
	err := twopc.receiveInternal(arg, reply)
	rcvr.log("[RPC Receive End %s] Error: %s", arg, err)
	return err
}

//--- Helper Functions

func assert(condition bool, message string) {
	if !condition {
		panic(message)
	}
}

func (res *TwoPCArchetypeResource) log(format string, args ...interface{}) {
	if res.debug {
		printfArgs := append([]interface{}{res.archetypeID, res.version}, args...)
		log.Printf("%s(%d): "+format+"\n", printfArgs...)
	}
}

func (res *TwoPCArchetypeResource) warn(format string, args ...interface{}) {
	printfArgs := append([]interface{}{res.archetypeID, res.version}, args...)
	log.Printf("%s(%d): "+format+"\n", printfArgs...)
}

func (res *RPCReplicaHandle) log(format string, args ...interface{}) {
	if res.debug {
		log.Printf(format+"\n", args...)
	}
}

func (res *RPCReplicaHandle) warn(format string, args ...interface{}) {
	log.Printf(format+"\n", args...)
}

func (res *TwoPCReceiver) log(format string, args ...interface{}) {
	res.twopc.inMutexNamed("log", func() {
		res.twopc.log(format, args...)
	})
}

func (res *TwoPCReceiver) warn(format string, args ...interface{}) {
	res.twopc.warn(format, args...)
}

// TwoPCArchetypeResourceMaker is the function that enables creation of 2PC
// resources.
func TwoPCArchetypeResourceMaker(
	value tla.TLAValue,
	address string,
	replicas []ReplicaHandle,
	archetypeID tla.TLAValue,
	onCreate func (*TwoPCReceiver),
) distsys.ArchetypeResourceMaker {

	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		resource := TwoPCArchetypeResource{
			value:                value,
			oldValue:             value,
			criticalSectionState: notInCriticalSection,
			twoPCState:           initial,
			replicas:             replicas,
			archetypeID:          archetypeID,
			debug:                false,
			timers:               make(map[string]time.Time),
	        version:              0,
		}
		receiver := makeTwoPCReceiver(&resource, address)
		if onCreate != nil {
			onCreate(&receiver)
		}
		go receiver.listenAndServe(nil)
		go resource.fetchStateFromReplicas()
		if timersEnabled {
			go func() {
				for {
					time.Sleep(time.Second)
					checkTimers(&resource)
				}
			}()
		}
		return &resource
	})
}

func (res *TwoPCArchetypeResource) fetchStateFromReplicas() {
	getStateRequest := TwoPCRequest {
		RequestType: GetState,
		Sender: res.archetypeID,
	}
	go res.sendToMajority("Fetch", func(i int, r ReplicaHandle) bool {
		var response TwoPCResponse
		r.Send(getStateRequest, &response)
		res.inMutex(func() {
			if response.Version > res.version {
				res.acceptNewValue(response.Value, response.Version)
			}
		})
		return true
	})
}

func (res *TwoPCArchetypeResource) acceptNewValue(value tla.TLAValue, version int) {
	res.log("Accept new value: %s %d", value, version)
	res.version = version
	res.value = value
	res.oldValue = value
	res.precommitAttempts = 0 // progress has been made, reset the counter
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
	}
}

func (res *TwoPCArchetypeResource) makeAbort() TwoPCRequest {
	return TwoPCRequest{
		RequestType: Abort,
		Sender:      res.archetypeID,
		Version:     res.version + 1,
	}
}

func (res *TwoPCArchetypeResource) makePreCommit() TwoPCRequest {
	return TwoPCRequest{
		RequestType: PreCommit,
		Value:       res.value,
		Sender:      res.archetypeID,
		Version:     res.version + 1,
	}
}

func (res *TwoPCArchetypeResource) makeReject(includeCurrentValue bool) TwoPCResponse {
	return TwoPCResponse{
		Accept:      false,
		Version: res.version,
		Value: res.oldValue,
	}
}

func makeAccept() TwoPCResponse {
	return TwoPCResponse{
		Accept: true,
	}
}
