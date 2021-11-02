package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"net"
	"net/rpc"
	"sync"
	"time"
)

// TwoPCRequest is the interface for messages to remote 2PC Replicas.
// getType() returns a description of the message; used for debugging only.
type TwoPCRequest interface {
	getType() string
}

// PreCommitMessage is the structure for sending a "PreCommit" message to a
// remote 2PC replica. Proposer is the name of the node making the request.
type PreCommitMessage struct {
	Value    tla.TLAValue
	Proposer string
}

func (m PreCommitMessage) getType() string {
	return "PreCommit"
}

// GobEncode encodes a PreCommitMessage into a byte slice. This is necessary for
// RPC communication.
func (m *PreCommitMessage) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(&m.Value)
	if err != nil {
		return nil, err
	}
	err = encoder.Encode(&m.Proposer)
	return buf.Bytes(), err
}

// GobDecodes decodes a byte slice into a PreCommitMessage. This is necessary
// for RPC communication.
func (m *PreCommitMessage) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	err := decoder.Decode(&m.Value)
	if err != nil {
		return err
	}
	return decoder.Decode(&m.Proposer)
}

// CommitMessage is the structure for "Commit" messages sent to remote 2PC
// replicas.
type CommitMessage struct {
	Proposer string
}

func (m CommitMessage) getType() string {
	return "Commit"
}

// AbortMessage is the structure for "Commit" messages sent to remote 2PC
// replicas.
type AbortMessage struct {
	Proposer string
}

func (m AbortMessage) getType() string {
	return "Abort"
}

// TwoPCResponse defines the response to a message from a remote 2PC node.
type TwoPCResponse interface {
	isAccept() bool
}

// TwoPCAccept is the structure for an accept response from a 2PC node.
type TwoPCAccept struct {
}

// TwoPCReject is the structure for a reject response from a 2PC node.
// ResponsibleNode is the name of the node that caused this node to reject the
// request. For example, if a node A has already pre-committed to a request from
// node B, when node A receives a request from node C, it will reject the
// request indicating "B" as the responsible node. A node can also refernce
// itself as the responsible node; for example in the case when it has already
// done a local precommit.
type TwoPCReject struct {
	ResponsibleNode string
}

func (response TwoPCAccept) isAccept() bool {
	return true
}

func (response TwoPCReject) isAccept() bool {
	return false
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
}

// LocalReplicaHandle is a structure for interacting with a replica operating in
// the same process (although likely running in a seperate goroutine). This is
// probably only useful for testing.
type LocalReplicaHandle struct {
	receiver *TwoPCArchetypeResource
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
	address string      // Client address
	client  *rpc.Client // RPC Client. Initialized during the first RPC request.
	debug   bool        // Whether or not to display debug output
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
func MakeRPCReplicaHandle(address string) RPCReplicaHandle {
	return RPCReplicaHandle{address: address}
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
	// The saved preCommit value from 2PC
	acceptedPreCommit PreCommitMessage
	// State relating to 2PC replication
	twoPCState TwoPCState

	// Replicas for 2PC
	replicas []ReplicaHandle

	// Name for this node
	// Used in debugging, and as a method for resolving PreCommit conflicts
	name string

	// Whether or not to enable debugging
	debug bool

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

//--- Archetype Functions

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
		for _, r := range res.replicas {
			request := AbortMessage{Proposer: res.name}
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
		}
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
		request := PreCommitMessage{Value: res.value, Proposer: res.name}
		var reply TwoPCResponse
		err_channel := r.Send(request, &reply)
		err := <-err_channel
		if err != nil {
			res.log("Encountered error when sending PreCommit message", err)
			res.criticalSectionState = notInCriticalSection
			channel <- err
			break
		}
		if !reply.isAccept() {
			channel <- distsys.ErrCriticalSectionAborted
			break
		}
		numSuccessfulPreCommits += 1
	}

	if numSuccessfulPreCommits != len(res.replicas) {
		// Note, critical section state will be reset when Abort() is called
		res.log("PreCommit for %s failed, rollback", res.value)
		for _, r := range res.replicas[0:numSuccessfulPreCommits] {
			res.log("Send rollback to %s", r)
			request := AbortMessage{Proposer: res.name}
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
			res.log("Rollback sent to %s", r)
		}
		return channel
	} else {
		assert(
			res.criticalSectionState == inPreCommit,
			fmt.Sprintf(
				"%s: Critical Section Changed to %s during PreCommit!",
				res.name,
				res.criticalSectionState,
			),
		)
		res.criticalSectionState = hasPreCommitted
		res.log("Successful PreCommit")
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
		fmt.Sprintf("%s: Commit() called from CS State %s", res.name, res.criticalSectionState),
	)
	assert(res.twoPCState != acceptedPreCommit, "Commit() called, but we have already accepted a PreCommit!")

	request := CommitMessage{Proposer: res.name}
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

func (res *TwoPCArchetypeResource) SetName(name string) {
	res.name = name
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
	defer twopc.mutex.Unlock()
	twopc.log(
		"Received %s message %s. CS State: %s, 2PC State: %s.",
		arg.getType(),
		arg,
		twopc.twoPCState,
		twopc.criticalSectionState,
	)
	switch message := arg.(type) {
	case PreCommitMessage:
		if twopc.twoPCState == acceptedPreCommit {
			twopc.log("Rejected PreCommit %s: already accepted PreCommit %s", message, twopc.acceptedPreCommit)
			*reply = TwoPCReject{ResponsibleNode: twopc.acceptedPreCommit.Proposer}
		} else if twopc.criticalSectionState == hasPreCommitted {
			twopc.log("Rejected PreCommit message %s: already PreCommitted.", message.Value)
			*reply = TwoPCReject{ResponsibleNode: twopc.name}
		} else if twopc.criticalSectionState == inPreCommit {
			twopc.log("Rejected PreCommit message %s: in precommit.", message.Value)
			*reply = TwoPCReject{ResponsibleNode: twopc.name}
		} else {
			twopc.log("Accepted PreCommit message %s.", message.Value)
			*reply = TwoPCAccept{}
			twopc.twoPCState = acceptedPreCommit
			twopc.acceptedPreCommit = message
			twopc.log(
				"After accepting PreCommit: CS State: %s, 2PC State: %s.",
				twopc.twoPCState,
				twopc.criticalSectionState,
			)
		}
	case CommitMessage:
		if message.Proposer != twopc.acceptedPreCommit.Proposer {
			twopc.log(
				"Received Commit() message from proposer %s, but the PreCommit was from %s",
				message.Proposer,
				twopc.acceptedPreCommit.Proposer,
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
	case AbortMessage:
		if message.Proposer != twopc.acceptedPreCommit.Proposer {
			twopc.log(
				"Received Abort message from proposer %s, but the PreCommit was from %s",
				message.Proposer,
				twopc.acceptedPreCommit.Proposer,
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
		printf_args := append([]interface{}{res.name}, args...)
		fmt.Printf("%s: "+format+"\n", printf_args...)
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
	name string,
) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		resource := TwoPCArchetypeResource{
			value:                value,
			oldValue:             value,
			criticalSectionState: notInCriticalSection,
			twoPCState:           initial,
			replicas:             replicas,
			name:                 name,
			debug:                false,
		}
		receiver := makeTwoPCReceiver(&resource, address)
		go ListenAndServe(&receiver, nil)
		return &resource
	})
}

func init() {
	gob.Register(TwoPCAccept{})
	gob.Register(TwoPCReject{ResponsibleNode: ""})
	gob.Register(PreCommitMessage{Value: tla.MakeTLANumber(0), Proposer: ""})
	gob.Register(CommitMessage{Proposer: ""})
	gob.Register(AbortMessage{Proposer: ""})
}
