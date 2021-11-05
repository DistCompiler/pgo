package resources

import (
	"fmt"
	"net"
	"net/rpc"
	"sort"
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

	if handle.client == nil {
		client, err := makeClient(handle.address)
		if err != nil {
			errorChannel <- err
			return errorChannel
		}
		handle.client = client
	}
	client := handle.client

	call := client.Go("TwoPCReceiver.Receive", &request, &reply, nil)
	<-call.Done

	if call.Error != nil {
		handle.log("RPC call encountered an error %s\n", call.Error)
		errorChannel <- call.Error
	} else {
		handle.log("RPC call completed successfully\n")
		errorChannel <- nil
	}

	return errorChannel
}

func (handle *RPCReplicaHandle) getArchetypeID() tla.TLAValue {
	return handle.archetypeID
}

// ListenAndServce initialize the RPC server for listening to incoming 2PC messages
// from remote nodes.
func ListenAndServe(rpcRcvr *TwoPCReceiver, done chan *TwoPCArchetypeResource) error {
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

	// Replicas for 2PC
	replicas []ReplicaHandle

	archetypeID tla.TLAValue

	// Whether or not to enable debugging
	debug bool

	rollbackComplete chan interface{}
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
)

func (state CriticalSectionState) String() string {
	switch state {
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

// Abort aborts the current critical section state. If this node has already
// completed a 2PC precommit, then it should rollback the PreCommit.
func (res *TwoPCArchetypeResource) Abort() chan struct{} {
	res.mutex.Lock()
	res.log(
		"Aborts 2PC State %s, CS State: %s, replicas %s",
		res.twoPCState,
		res.criticalSectionState,
		res.replicas,
	)
	res.value = res.oldValue
	if res.criticalSectionState == hasPreCommitted {
		res.log("Rollback replicas due to Abort()")
		res.mutex.Unlock()
		for _, r := range res.replicas {
			request := makeAbort(res.archetypeID)
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
		}
		res.mutex.Lock()
	}
	res.criticalSectionState = notInCriticalSection
	res.mutex.Unlock()
	return nil
}

// PreCommit attempts to perform a PreCommit on the local critical sectionLocal.
// This triggers the 2PC PreCommit on all relicas. If any replica refuses the
// PreCommit(), then the operation will fail.
func (res *TwoPCArchetypeResource) PreCommit() chan error {
	res.log("Initiate PreCommit for value %s", res.value)
	channel := make(chan error, 1)
	res.mutex.Lock()
	if res.shouldAbort() {
		res.log("PreCommit for %s aborted locally", res.value)
		channel <- distsys.ErrCriticalSectionAborted
		res.mutex.Unlock()
		return channel
	}
	res.criticalSectionState = inPreCommit
	res.mutex.Unlock()

	var numSuccessfulPreCommits = 0
	for _, r := range res.replicas {
		request := makePreCommit(res.value, res.archetypeID)
		var reply TwoPCResponse
		errChannel := r.Send(request, &reply)
		err := <-errChannel
		if err != nil {
			res.log("Encountered error when sending PreCommit message", err)
			res.mutex.Lock()
			res.criticalSectionState = notInCriticalSection
			res.mutex.Unlock()
			channel <- err
			break
		} else if !reply.Accept {
			channel <- distsys.ErrCriticalSectionAborted
			break
		}
		numSuccessfulPreCommits += 1
		res.mutex.Lock()
		if res.shouldAbort() {
			res.log("Aborting PreCommit due to pre-emption by %s", res.acceptedPreCommit.Sender)
			res.mutex.Unlock()
			break
		}
		res.mutex.Unlock()
	}

	res.mutex.Lock()
	if res.shouldAbort() || numSuccessfulPreCommits != len(res.replicas) {
		// Note, critical section state will be reset when Abort() is called
		res.log("PreCommit for %s failed, rollback", res.value)
		res.mutex.Unlock()
		for _, r := range res.replicas[0:numSuccessfulPreCommits] {
			res.log("Send rollback to %s", r)
			request := makeAbort(res.archetypeID)
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
			res.log("Rollback sent to %s", r)
		}
		if res.rollbackComplete != nil {
			res.rollbackComplete <- true
		}
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
		res.log("Successful PreCommit")
		res.mutex.Unlock()
		return nil
	}
}

// Commit unconditionally commits the local critical section, also performing
// the 2PC commit at this time. This is safe because PreCommit has already
// succeeded, thus all Replicas have already accepted the PreCommit and are able
// to accept the Commit() message.
func (res *TwoPCArchetypeResource) Commit() chan struct{} {
	assert(
		res.criticalSectionState == hasPreCommitted,
		fmt.Sprintf("%s: Commit() called from CS State %s", res.archetypeID, res.criticalSectionState),
	)
	assert(res.twoPCState != acceptedPreCommit, "Commit() called, but we have already accepted a PreCommit!")

	request := makeCommit(res.archetypeID)
	for _, r := range res.replicas {
		var reply TwoPCResponse
		call := r.Send(request, &reply)
		<-call
	}
	res.log("Commit(%s) has been acknowledged by all replicas", res.value)
	res.mutex.Lock()
	res.oldValue = res.value
	res.criticalSectionState = notInCriticalSection
	res.mutex.Unlock()
	res.log("Commit(%s) complete", res.value)
	return nil
}

// ReadValue reads the current value, potential aborting the local critical
// state (see shouldAbort() for the corresponding logic).
func (res *TwoPCArchetypeResource) ReadValue() (tla.TLAValue, error) {
	res.mutex.Lock()
	defer res.mutex.Unlock()
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
	res.mutex.Lock()
	defer res.mutex.Unlock()
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
	return res.criticalSectionState == acceptedCommitInCriticalSection
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
	twopc.mutex.Lock()
	twopc.log(
		"Received 2PC message %s. CS State: %s, 2PC State: %s.",
		arg,
		twopc.twoPCState,
		twopc.criticalSectionState,
	)
	switch arg.RequestType {
	case PreCommit:
		if twopc.twoPCState == acceptedPreCommit {
			twopc.log("Rejected PreCommit %s: already accepted PreCommit %s", arg, twopc.acceptedPreCommit)
			*reply = makeReject(twopc.acceptedPreCommit.Sender)
		} else if twopc.criticalSectionState == hasPreCommitted {
			twopc.log("Rejected PreCommit message %s: already PreCommitted.", arg.Value)
			*reply = makeReject(twopc.archetypeID)
		} else if twopc.criticalSectionState == inPreCommit && shouldDeferTo(twopc.archetypeID, arg.Sender) {
			twopc.log("Rejected PreCommit message %s: in precommit.", arg.Value)
			twopc.mutex.Unlock()
			twopc.rollbackComplete = make(chan interface{}, 1)
			<-twopc.rollbackComplete
			twopc.rollbackComplete = nil
			*reply = makeReject(twopc.archetypeID)
			return nil
		} else {
			twopc.log("Accepted PreCommit message %s.", arg.Value)
			*reply = makeAccept()
			twopc.twoPCState = acceptedPreCommit
			twopc.acceptedPreCommit = arg
			twopc.log(
				"After accepting PreCommit: CS State: %s, 2PC State: %s.",
				twopc.twoPCState,
				twopc.criticalSectionState,
			)
		}
	case Commit:
		if arg.Sender != twopc.acceptedPreCommit.Sender {
			twopc.log(
				"Received Commit() message from proposer %s, but the PreCommit was from %s",
				arg.Sender,
				twopc.acceptedPreCommit.Sender,
			)
		} else {
			twopc.log("Accepted Commit %s", twopc.acceptedPreCommit)
			twopc.twoPCState = initial
			twopc.value = twopc.acceptedPreCommit.Value
			twopc.oldValue = twopc.acceptedPreCommit.Value
			if twopc.inCriticalSection() {
				twopc.criticalSectionState = acceptedCommitInCriticalSection
			}
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
	twopc.mutex.Unlock()
	return nil
}

// Receive is the generic handler for receiving a 2PC request from another node.
func (rcvr *TwoPCReceiver) Receive(arg TwoPCRequest, reply *TwoPCResponse) error {
	rcvr.log("Got an RPC request.")
	twopc := rcvr.twopc
	return twopc.receiveInternal(arg, reply)
}

//--- Helper Functions

func assert(condition bool, message string) {
	if !condition {
		panic(message)
	}
}

func (res *TwoPCArchetypeResource) log(format string, args ...interface{}) {
	if res.debug {
		printfArgs := append([]interface{}{res.archetypeID}, args...)
		fmt.Printf("%s: "+format+"\n", printfArgs...)
	}
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

	// Sorts the replicas in descending order of priority. This ensures that
	// PreCommit messages are sent to high-priority nodes first, and that
	// all replicas send messages in the same order.
	sortedReplicas := append([]ReplicaHandle(nil), replicas...)
	sort.SliceStable(sortedReplicas, func(i, j int) bool {
		return !shouldDeferTo(
			sortedReplicas[i].getArchetypeID(),
			sortedReplicas[j].getArchetypeID(),
		)
	})
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		resource := TwoPCArchetypeResource{
			value:                value,
			oldValue:             value,
			criticalSectionState: notInCriticalSection,
			twoPCState:           initial,
			replicas:             sortedReplicas,
			archetypeID:          archetypeID,
			debug:                true,
		}
		receiver := makeTwoPCReceiver(&resource, address)
		go ListenAndServe(&receiver, nil)
		return &resource
	})
}

func makeAbort(sender tla.TLAValue) TwoPCRequest {
	return TwoPCRequest{
		RequestType: Abort,
		Sender:      sender,
	}
}

func makePreCommit(value tla.TLAValue, proposer tla.TLAValue) TwoPCRequest {
	return TwoPCRequest{
		RequestType: PreCommit,
		Value:       value,
		Sender:      proposer,
	}
}

func makeCommit(proposer tla.TLAValue) TwoPCRequest {
	return TwoPCRequest{
		RequestType: Commit,
		Sender:      proposer,
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

// shouldDeferTo returns true iff lhs should abort it's in-progress PreCommit if
// it receives a PreCommit from rhs. Node that shouldDeferTo should define a
// total ordering on nodes.
func shouldDeferTo(lhs tla.TLAValue, rhs tla.TLAValue) bool {
	return lhs.Hash() < rhs.Hash()
}
