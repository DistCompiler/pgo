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

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// TwoPCRequestType is the type of 2PC message to a remote node; i.e either
// "PreCommit", "Commit", or "Abort"
type TwoPCRequestType int

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
	listener   *net.Listener
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

// Send sends a 2PC request to a remote replica. This function will initiate the
// RPC client for the handle if it has not been initiated yet.
func (handle *RPCReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	handle.log("RPC call initiated with request %s\n", request)
	assert(reply != nil, "reply was not initialized correctly")
	errorChannel := make(chan error, 1)

	handle.mutex.Lock()
	if handle.client == nil {
		client, err := makeClient(handle.address)
		if err != nil {
			handle.mutex.Unlock()
			errorChannel <- err
			return errorChannel
		}
		handle.client = client
	}
	handle.mutex.Unlock()
	client := handle.client
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
	rpcRcvr.warn("Monitor: started listening on %s\n", rpcRcvr.ListenAddr)
	if done != nil {
		done <- rpcRcvr.twopc
	}
	// open := true
	// go func() {
	// 	s := rand.NewSource(int64(rpcRcvr.twopc.archetypeID.Hash()) + time.Now().UnixNano())
	// 	r := rand.New(s).Intn(5000)
	// 	time.Sleep(time.Duration(r) * time.Millisecond)
	// 	listener.Close()
	// 	open = false
	// 	rpcRcvr.twopc.enterMutex()
	// 	if rpcRcvr.twopc.numInFlightRequests > 0 {
	// 		rpcRcvr.twopc.allRequestsComplete = make(chan interface{}, 1)
	// 		rpcRcvr.twopc.leaveMutex()
	// 		<-rpcRcvr.twopc.allRequestsComplete
	// 		time.Sleep(50 * time.Millisecond)
	// 		rpcRcvr.twopc.enterMutex()
	// 	}
	// 	if rpcRcvr.twopc.version == 21 || rpcRcvr.twopc.criticalSectionState == hasPreCommitted {
	// 		rpcRcvr.twopc.leaveMutex()
	// 		go rpcRcvr.listenAndServe(nil)
	// 		return
	// 	}
	// 	rpcRcvr.twopc.version = 1
	// 	rpcRcvr.twopc.criticalSectionState = notInCriticalSection
	// 	rpcRcvr.twopc.numInFlightRequests = 0
	// 	rpcRcvr.twopc.precommitAttempts = 0
	// 	rpcRcvr.twopc.twoPCState = initial
	// 	rpcRcvr.twopc.oldValue = tla.MakeTLANumber(0)
	// 	rpcRcvr.twopc.value = tla.MakeTLANumber(0)
	// 	rpcRcvr.twopc.allRequestsComplete = nil
	// 	rpcRcvr.twopc.leaveMutex()
	// 	time.Sleep(1 * time.Second)
	// 	go rpcRcvr.listenAndServe(nil)
	// 	go rpcRcvr.twopc.fetchStateFromReplicas()
	// }()
	for {
		conn, err := listener.Accept()
		if err != nil {
			rpcRcvr.warn("Failure in listener.Accept(): %s", err)
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
	if res.debug {
		res.timerMutex.Lock()
		// res.log("Timing Start: %s", key)
		res.timers[key] = time.Now()
		res.timerMutex.Unlock()
	}
}

func (res *TwoPCArchetypeResource) stopTiming(key string) {
	if res.debug {
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

func (res *TwoPCArchetypeResource) outsideMutex(action func()) {
	res.mutex.Unlock()
	action()
	res.mutex.Lock()
}

func (res *TwoPCArchetypeResource) inMutex(action func()) {
	res.mutex.Lock()
	action()
	res.mutex.Unlock()
}

func checkTimers(res *TwoPCArchetypeResource) {
	res.timerMutex.Lock()
	for key, start := range res.timers {
		duration := time.Now().Sub(start)
		if duration > 3 * time.Second {
			res.log("Timer %s: %s", key, duration)
		}
	}
	res.timerMutex.Unlock()
}

func (res *TwoPCArchetypeResource) rollback() {
	res.enterMutex()
	request := res.makeAbort()
	res.leaveMutex()
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
	res.enterMutex()
	// res.log(
	// 	"Aborts 2PC State %s, CS State: %s, replicas %s",
	// 	res.twoPCState,
	// 	res.criticalSectionState,
	// 	res.replicas,
	// )
	res.value = res.oldValue
	if res.criticalSectionState == hasPreCommitted {
		res.log("Rollback replicas due to Abort()")
		res.leaveMutex()
		res.rollback()
		res.enterMutex()
	}
	res.criticalSectionState = notInCriticalSection
	res.leaveMutex()
	return nil
}

func (res *TwoPCArchetypeResource) sendToMajority(name string, f func(int, ReplicaHandle) bool) bool {
	res.inMutex(func() {
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
			res.inMutex(func() {
				res.numInFlightRequests -= 1
				if res.numInFlightRequests == 0 && res.allRequestsComplete != nil {
					res.allRequestsComplete <- true
				}
			})
			res.stopTiming(timing_key)
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
	res.enterMutex()
	initialVersion := res.version
	if res.precommitAttempts > 0 {
		s := rand.NewSource(int64(res.archetypeID.Hash()) + time.Now().UnixNano())
		constant := float64(5)
		exponent := math.Pow(2, float64(res.precommitAttempts)) - 1
		sleepTime = time.Duration(rand.New(s).Intn(int(constant * exponent))) * time.Millisecond
		res.log("PreCommit Sleep time: %s", sleepTime)
	}
	res.leaveMutex()
	channel := make(chan error, 1)
	go func(){
		time.Sleep(sleepTime)
		res.enterMutex()
		if res.version != initialVersion {
			// We handled a commit while we were sleeping. Don't try this precommit
			channel <- distsys.ErrCriticalSectionAborted
			res.leaveMutex()
			return
		}
		res.leaveMutex()
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
	res.enterMutex()
	res.log("[Enter PreCommit] Value: %s", res.value)

	if res.shouldAbort() {
		res.log("[Exit PreCommit] PreCommit for %s aborted locally", res.value)
		res.leaveMutex()
		return distsys.ErrCriticalSectionAborted
	}
	res.log("[Enter PreCommit] Value: %s", res.value)
	res.criticalSectionState = inPreCommit
	request := res.makePreCommit()
	res.leaveMutex()

	success := res.sendToMajority("PreCommit", func(i int, r ReplicaHandle) bool {
		var reply TwoPCResponse
		res.startTiming(fmt.Sprintf("Send PreCommit to %d", i))
		errChannel := r.Send(request, &reply)
		err := <-errChannel
		res.stopTiming(fmt.Sprintf("Send PreCommit to %d", i))
		if err != nil {
			res.warn("Encountered error when sending PreCommit message: %s", err)
			return false
		} else if !reply.Accept {
			res.log("Replica %s rejected the PreCommit", r)
			res.inMutex(func() {
				if reply.Version > res.version {
					res.acceptNewValue(reply.Value, reply.Version)
				}
			})
			return false
		} else {
			return true
		}
	})

	res.enterMutex()
	if !success || res.criticalSectionState == acceptedNewValueInCriticalSection {
		res.leaveMutex()
		res.rollback()
		res.inMutex(func() {
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
		res.leaveMutex()
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
				res.log("%i rejected commit", i)
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

	res.inMutex(func() {
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
// state (see shouldAbort() for the corresponding logic).
func (res *TwoPCArchetypeResource) ReadValue() (tla.TLAValue, error) {
	res.enterMutex()
	defer res.leaveMutex()
	if res.shouldAbort() {
		// res.log("ReadValue() rejected")
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
	// res.log("ReadValue() allowed: %s", res.value)
	res.criticalSectionState = inUninterruptedCriticalSection
	return res.value, nil
}

// ReadValue writes the given value, potential aborting the local critical state
// (see shouldAbort() for the corresponding logic).
func (res *TwoPCArchetypeResource) WriteValue(value tla.TLAValue) error {
	res.enterMutex()
	defer res.leaveMutex()
	if res.shouldAbort() {
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
	res.enterMutex()
	if res.numInFlightRequests > 0 {
		res.allRequestsComplete = make (chan interface{}, 1)
		res.leaveMutex()
		<-res.allRequestsComplete
	} else {
		res.leaveMutex()
	}
	return nil
}

func (res *TwoPCArchetypeResource) inCriticalSection() bool {
	return res.criticalSectionState != notInCriticalSection
}

// criticalSectionPermanentlyFailed returns true iff this node has accepted a
// 2PC commit while inside a critical section. In that case, the current
// critical section must abort to maintain serializability.
// TODO: Consider case when the accepted commit has the same value as before
//       entering the critical section, or if the local value hasn't yet been
//       *read* in the critical section.
func (res *TwoPCArchetypeResource) criticalSectionPermanentlyFailed() bool {
	return res.criticalSectionState == acceptedNewValueInCriticalSection ||
		res.criticalSectionState == failedPreCommit
}

// shouldAbort returns true if the critical section has permanently failed, or
// if this node has already pre-committed to a value from a remote node. This
// behaviour is pessimistic: in principle the precommit could be rolled back,
// allowing the local critical section to commit. However, logic is likely
// better for preventing deadlock.
func (res *TwoPCArchetypeResource) shouldAbort() bool {
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
	twopc.startTiming("receive")
	defer twopc.stopTiming("receive")
	twopc.enterMutex()
	defer twopc.leaveMutex()
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
			twopc.log("Rejected PreCommit %s: already accepted PreCommit %s", arg, twopc.acceptedPreCommit)
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
		fmt.Printf("%s(%d): "+format+"\n", printfArgs...)
	}
}

func (res *TwoPCArchetypeResource) warn(format string, args ...interface{}) {
	printfArgs := append([]interface{}{res.archetypeID, res.version}, args...)
	fmt.Printf("%s(%d): "+format+"\n", printfArgs...)
}

func (res *RPCReplicaHandle) log(format string, args ...interface{}) {
	if res.debug {
		fmt.Printf(format+"\n", args...)
	}
}

func (res *RPCReplicaHandle) warn(format string, args ...interface{}) {
	fmt.Printf(format+"\n", args...)
}

func (res *TwoPCReceiver) log(format string, args ...interface{}) {
	res.twopc.inMutex(func() {
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
		go receiver.listenAndServe(nil)
		go resource.fetchStateFromReplicas()
		// if resource.debug {
		// 	go func() {
		// 		for {
		// 			time.Sleep(time.Second)
		// 			checkTimers(&resource)
		// 		}
		// 	}()
		// }
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
	res.warn("Accept new value: %s %d", value, version)
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
