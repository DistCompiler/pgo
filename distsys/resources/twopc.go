package resources

import (
	"math/rand"
	"fmt"
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
)

func (requestType TwoPCRequestType) String() string {
	switch requestType {
	case PreCommit:
		return "PreCommit"
	case Commit:
		return "Commit"
	case Abort:
		return "Abort"
	}
	panic("Unknown requestType")
}

// TwoPCRequest is the message for a 2PC request, typically sent over an RPC
// interface.
type TwoPCRequest struct {
	RequestType TwoPCRequestType
	Value       tla.TLAValue
	Reponsible  tla.TLAValue
	Sender      tla.TLAValue
	Version     int
}

// TwoPCRequest is the corresponding response to a 2PC request, also sent via
// the RPC interface.
type TwoPCResponse struct {
	Accept      bool
	Responsible tla.TLAValue
}

// TwoPCReceiver defines the RPC receiver for 2PC communication. The associated
// functions for this struct are exposed via the RPC interface.
type TwoPCReceiver struct {
	ListenAddr string
	done       chan struct{}
	twopc      *TwoPCArchetypeResource
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

func (handle RPCReplicaHandle) String() string {
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

	call := client.Go("TwoPCReceiver.Receive", &request, &reply, nil)
	<-call.Done

	if call.Error != nil {
		handle.log("RPC call encountered an error %s\n", call.Error)
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
	rpcRcvr.log("Monitor: started listening on %s\n", rpcRcvr.ListenAddr)
	if done != nil {
		done <- rpcRcvr.twopc
	}
	for {
		conn, err := listener.Accept()
		if err != nil {
			select {
			case <-rpcRcvr.done:
				return nil
			default:
				return err
			}
		}
		go server.ServeConn(conn)
	}
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
	conn, err := net.Dial("tcp", address)
	if err != nil {
		time.Sleep(1 * time.Second)
		conn, err = net.Dial("tcp", address)
	}
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

	// Replicas for 2PC
	replicas []ReplicaHandle

	archetypeID tla.TLAValue

	// Whether or not to enable debugging
	debug bool

	// Initial time of in-progress operations, used for debugging only
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
	acceptedCommitInCriticalSection
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
	case acceptedCommitInCriticalSection:
		return "acceptedCommitInCriticalSection"
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
		res.log("Timing Start: %s", key)
		res.timers[key] = time.Now()
	}
}

func (res *TwoPCArchetypeResource) stopTiming(key string) {
	if res.debug {
		res.log("Timing Stop: %s", key)
		delete(res.timers, key)
	}
}

func (res *TwoPCArchetypeResource) enterMutex() {
	res.mutex.Lock()
	res.startTiming("lock")
}

func (res *TwoPCArchetypeResource) leaveMutex() {
	res.mutex.Unlock()
	res.stopTiming("lock")
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
	res.log("Timers:")
	for key, start := range res.timers {
		duration := time.Now().Sub(start)
		res.log("%s: %s", key, duration)
	}
}

func (res *TwoPCArchetypeResource) rollback() {
	res.enterMutex()
	request := res.makeAbort()
	res.leaveMutex()
	res.sendToMajority( func(i int, r ReplicaHandle, resp (chan bool)) {
		res.log("Send rollback to %s", r)
		var reply TwoPCResponse
		res.startTiming(fmt.Sprintf("PreCommit: Rollback %d", i))
		call := r.Send(request, &reply)
		<-call
		res.stopTiming(fmt.Sprintf("PreCommit: Rollback %d", i))
		res.log("Rollback sent to %s", r)
		resp <- true
	})
}

// Abort aborts the current critical section state. If this node has already
// completed a 2PC precommit, then it should rollback the PreCommit.
func (res *TwoPCArchetypeResource) Abort() chan struct{} {
	res.enterMutex()
	res.log(
		"Aborts 2PC State %s, CS State: %s, replicas %s",
		res.twoPCState,
		res.criticalSectionState,
		res.replicas,
	)
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

// PreCommit attempts to perform a PreCommit on the local critical sectionLocal.
// This triggers the 2PC PreCommit on all relicas. If any replica refuses the
// PreCommit(), then the operation will fail.
func (res *TwoPCArchetypeResource) PreCommit() chan error {
	s := rand.NewSource(int64(res.archetypeID.Hash()))
	r := rand.New(s).Intn(50)
	time.Sleep(time.Duration(r) * time.Millisecond)
	res.startTiming("PreCommit")
	defer res.stopTiming("PreCommit")
	return res.preCommit()
}

func (res *TwoPCArchetypeResource) sendToMajority(f func(int, ReplicaHandle, chan bool)) bool {
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
		go func() {
			res.log("sendToMajority start")
			f(ii, rr, responses)
			res.log("sendToMajority end")
		}()
	}

	for required > 0 && remaining >= required {
		res.log("wait response")
		response := <-responses
		res.log("done waiting")
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
func (res *TwoPCArchetypeResource) preCommit() chan error {
	res.enterMutex()
	res.log("[Enter PreCommit] Value: %s", res.value)
	channel := make(chan error, 1)

	if res.shouldAbort() {
		res.log("[Exit PreCommit] PreCommit for %s aborted locally", res.value)
		channel <- distsys.ErrCriticalSectionAborted
		res.leaveMutex()
		return channel
	}
	res.warn("[Enter PreCommit] Value: %s", res.value)
	res.criticalSectionState = inPreCommit
	request := res.makePreCommit()
	res.leaveMutex()

	success := res.sendToMajority( func(i int, r ReplicaHandle, resp (chan bool)) {
		var reply TwoPCResponse
		errChannel := r.Send(request, &reply)
		res.startTiming(fmt.Sprintf("Send PreCommit to %d", i))
		err := <-errChannel
		res.stopTiming(fmt.Sprintf("Send PreCommit to %d", i))
		if err != nil {
			res.warn("Encountered error when sending PreCommit message", err)
			resp <- false
		} else if !reply.Accept {
			res.log("Replica %s rejected the PreCommit", r)
			resp <- false
		} else {
			resp <- true
		}
	})

	if !success {
		res.rollback()
		res.inMutex(func() {
			res.criticalSectionState = failedPreCommit
			res.warn("[Exit PreCommit] rollback %s", res.value)
		})
		channel <- distsys.ErrCriticalSectionAborted
		return channel
	} else {
		res.enterMutex()
		defer res.leaveMutex()
		if res.criticalSectionState == acceptedCommitInCriticalSection {
			res.outsideMutex(res.rollback)
			res.criticalSectionState = failedPreCommit
			res.log("[Exit PreCommit] rollback %s", res.value)
			channel <- distsys.ErrCriticalSectionAborted
			return channel
		} else {
			assert(
				res.criticalSectionState == inPreCommit,
				fmt.Sprintf(
					"%s: Critical Section Changed to %s during PreCommit!",
					res.archetypeID,
					res.criticalSectionState,
				),
			)
			res.criticalSectionState = hasPreCommitted
			res.warn("[Exit PreCommit] Succeeded for %s", res.value)
			return nil
		}
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

	request := res.makeCommit()
	res.sendToMajority(func(i int, r ReplicaHandle, resp (chan bool)) {
		var reply TwoPCResponse
		call := r.Send(request, &reply)
		<-call
		resp <- true
	})

	res.inMutex(func() {
		res.log("Commit(%s) has been sent to a majority of replicas", res.value)
		res.oldValue = res.value
		res.criticalSectionState = notInCriticalSection
		res.version += 1
		res.warn("Commit(%s) complete", res.value)
	})
	return nil
}

// ReadValue reads the current value, potential aborting the local critical
// state (see shouldAbort() for the corresponding logic).
func (res *TwoPCArchetypeResource) ReadValue() (tla.TLAValue, error) {
	res.enterMutex()
	defer res.leaveMutex()
	if res.shouldAbort() {
		res.log("ReadValue() rejected")
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
	res.log("ReadValue() allowed: %s", res.value)
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

// Close should cleanly shut down this 2PC instance. TODO: Implement this
// functionality.
func (res *TwoPCArchetypeResource) Close() error {
	res.log("Close()")
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
	return res.criticalSectionState == acceptedCommitInCriticalSection ||
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
// TODO: Save state to stable storage
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
	if(arg.Version > twopc.version + 1) {
		twopc.warn(
			"%s message (version %d) from %s is higher than expected %d",
			arg.RequestType,
			arg.Version, arg.Sender, twopc.version + 1)
	}
	if(arg.Version < twopc.version + 1) {
		twopc.warn(
			"%s message (version %d) from %s is lower than expected %d",
			arg.RequestType,
			arg.Version, arg.Sender, twopc.version + 1)
		*reply = makeReject(twopc.archetypeID)
		return nil
	}
	switch arg.RequestType {
	case PreCommit:
		if twopc.twoPCState == acceptedPreCommit {
			twopc.log("Rejected PreCommit %s: already accepted PreCommit %s", arg, twopc.acceptedPreCommit)
			*reply = makeReject(twopc.acceptedPreCommit.Sender)
		} else if twopc.criticalSectionState == hasPreCommitted {
			twopc.log("Rejected PreCommit message %s: already PreCommitted.", arg.Value)
			*reply = makeReject(twopc.archetypeID)
		} else if twopc.criticalSectionState == inPreCommit {
			twopc.log("Rejected PreCommit message %s: in precommit.", arg.Value)
			*reply = makeReject(twopc.archetypeID)
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
		twopc.log("Accepted Commit %s", twopc.acceptedPreCommit)
		twopc.twoPCState = initial
		twopc.value = arg.Value
		twopc.oldValue = arg.Value
		twopc.version = arg.Version
		if twopc.inCriticalSection() {
			twopc.criticalSectionState = acceptedCommitInCriticalSection
		}
	case Abort:
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

func (res *TwoPCReceiver) log(format string, args ...interface{}) {
	res.twopc.log(format, args...)
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
		return &resource
	})
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

func makeReject(responsible tla.TLAValue) TwoPCResponse {
	return TwoPCResponse{
		Accept:      false,
		Responsible: responsible,
	}
}

func makeAccept() TwoPCResponse {
	return TwoPCResponse{
		Accept: true,
	}
}
