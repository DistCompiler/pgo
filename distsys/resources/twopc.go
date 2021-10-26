package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys"
	"net"
	"net/rpc"
	"time"
	"sync"
)

//--- TwoPC Protocol

// TODO: Add a a unique ID associated for this iteration of 2PC
//       This is necessary for associating Aborts / Commits to
//       previous PreCommit requests
type TwoPCRequest interface{
	GetType() string
}

type PreCommitMessage struct {
   Value tla.TLAValue
   Proposer string
}

func (m PreCommitMessage) GetType() string {
	return "PreCommit"
}

func (m PreCommitMessage) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(&m.Value)
	if err != nil {
		return nil, err
	}
	err = encoder.Encode(&m.Proposer)
	return buf.Bytes(), err
}

func (m *PreCommitMessage) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	err := decoder.Decode(&m.Value)
	if err != nil {
		return err
	}
	return decoder.Decode(&m.Proposer)
}

// TODO: Add a a unique ID associated for this iteration of 2PC
type CommitMessage struct {
	Proposer string
}

func (m CommitMessage) GetType() string {
	return "Commit"
}

// TODO: Add a a unique ID associated for this iteration of 2PC
type AbortMessage struct {
	Proposer string
}

func (m AbortMessage) GetType() string {
	return "Abort"
}

type TwoPCResponse interface {
	IsAccept() bool
}

type TwoPCAccept struct {

}

type TwoPCReject struct {
	ResponsibleNode string
}

func (response TwoPCAccept) IsAccept() bool {
	return true
}

func (response TwoPCReject) IsAccept() bool {
	return false
}

//--- TwoPC IO

type TwoPCReceiver struct {
	ListenAddr string
	done chan struct{}
	twopc *TwoPCArchetypeResource
	debug bool // Whether or not to display debug output
}

func MakeTwoPCReceiver(twopc *TwoPCArchetypeResource, ListenAddr string) TwoPCReceiver {
	return TwoPCReceiver {
		ListenAddr: ListenAddr,
		twopc: twopc,
		done: make(chan struct{}),
	}
}

// Interface for connecting with 2PC replicas
// Basically the same as the RPC interface, but allows for custom transports
type ReplicaHandle interface {
	Send(request TwoPCRequest, reply *TwoPCResponse) chan error
}

// Interact with a local replica. Most likely only useful for testing
type LocalReplicaHandle struct {
	receiver *TwoPCArchetypeResource
}

func (handle LocalReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	error_channel := make(chan error, 1)
	err := handle.receiver.receiveInternal(request, reply)
	error_channel <- err
	return error_channel
}

// Interface for connecting with 2PC replicas over RPC
type RPCReplicaHandle struct {
	address string     // Client address
    client *rpc.Client // RPC Client. Initialized during the first RPC request.
	debug bool         // Whether or not to display debug output
}

func (handle RPCReplicaHandle) String() string {
    return fmt.Sprintf("%s[connected: %t]", handle.address, handle.client != nil)
}

func (handle *RPCReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	handle.log("RPC call initiated with request %s\n", request)
	assert(reply != nil, "reply was not initialized correctly")
	error_channel := make(chan error, 1)

	if(handle.client == nil) {
		client, err := makeClient(handle.address)
		if err != nil {
			error_channel <- err
			return error_channel
		}
		handle.client = client
	}
	client := handle.client

	call := client.Go("TwoPCReceiver.Receive", &request, &reply, nil)
	<-call.Done

	if call.Error != nil {
		handle.log("RPC call encountered an error %s\n", call.Error)
		error_channel <- call.Error
	} else {
		handle.log("RPC call completed successfully\n")
		error_channel <- nil
	}

	return error_channel
}

// Initialize server for listening to incoming replica requests
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
	done <- rpcRcvr.twopc
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

//--- Archetype and state data structures

type TwoPCArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin

	// Current value, and value in the critical state respectively
	value, oldValue tla.TLAValue

	// The saved preCommit value from 2PC
	acceptedPreCommit PreCommitMessage

	// State relating to the local critical section
	criticalSectionState CriticalSectionState

	// State relating to 2PC replication
	twoPCState TwoPCState

	// Replicas for 2PC
	replicas []ReplicaHandle

	// Name for this node
	// Used in debugging, and as a method for resolving PreCommit conflicts
	name string

	// Whether or not to enable debugging
	debug bool

	// Internal Mutex
	mutex sync.Mutex
}

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

// The *local* critical state section of the resource
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

// Abort the current critical section state
// If were also attempting 2PC replication, sned a rollback message
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
			request := AbortMessage { Proposer: res.name }
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
		}
	}
	res.criticalSectionState = notInCriticalSection;
	res.mutex.Unlock()
	return nil
}


// Local Critical Section PreCommit. This triggers the 2PC PreCommit on all
// relicas. If any replica refuses the PreCommit(), then this should fail
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
	res.criticalSectionState = inPreCommit;
	res.mutex.Unlock()

	var num_successful_precommits = 0
	for _, r := range res.replicas {
		request := PreCommitMessage { Value: res.value , Proposer: res.name }
		var reply TwoPCResponse
		err_channel := r.Send(request, &reply)
		err := <-err_channel
		if err != nil {
			res.criticalSectionState = notInCriticalSection
			channel <- err
			break
		}
		if !reply.IsAccept() {
			channel <- distsys.ErrCriticalSectionAborted
			break
		}
		num_successful_precommits += 1
	}

	if num_successful_precommits != len(res.replicas) {
		// Note, critical section state will be reset when Abort() is called
		res.log("PreCommit for %s failed, rollback", res.value)
		for _, r := range res.replicas[0:num_successful_precommits] {
			res.log("Send rollback to %s", r)
			request := AbortMessage { Proposer: res.name }
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
		);
		res.criticalSectionState = hasPreCommitted;
		res.log("Successful PreCommit")
		return nil
	}
}

// Unconditionally Commit, also performing the 2PC commit at this time This is
// safe because `PreCommit` has already succeeded, thus all Replicas have
// already accepted the PreCommit and are able to accept the Commit() message.
func (res *TwoPCArchetypeResource) Commit() chan struct{} {
	assert(
		res.criticalSectionState == hasPreCommitted,
		fmt.Sprintf("%s: Commit() called from CS State %s", res.name, res.criticalSectionState),
	)
	assert(res.twoPCState != acceptedPreCommit, "Commit() called, but we have already accepted a PreCommit!")

	request := CommitMessage { Proposer: res.name }
	for _, r := range res.replicas {
		var reply TwoPCResponse
		call := r.Send(request, &reply)
		<-call
	}
	res.log("Commit(%s) has been acknowledged by all replicas", res.value)
	res.mutex.Lock()
	res.oldValue = res.value;
	res.criticalSectionState = notInCriticalSection;
	res.mutex.Unlock()
	return nil
}

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

func (res *TwoPCArchetypeResource) WriteValue(value tla.TLAValue) error {
	res.mutex.Lock()
	defer res.mutex.Unlock()
	if res.shouldAbort() {
		res.log("WriteValue() rejected")
		return distsys.ErrCriticalSectionAborted
	}
	res.log("WriteValue() allowed")
	res.value = value
	res.criticalSectionState = inUninterruptedCriticalSection;
	return nil
}

// TODO: Any cleanup logic
func (res *TwoPCArchetypeResource) Close() error {
	res.log("Close()")
	return nil
}

func (res *TwoPCArchetypeResource) inCriticalSection() bool {
   return res.criticalSectionState != notInCriticalSection
}

// If a resource accepted a commit while in a critical section,
// this critical section must abort, because serializability is violated
// TODO: Consider case when the accepted commit has the same value as before
//       entering the critical section, or if the local value hasn't yet been
//       *read* in the critical section.
func (res *TwoPCArchetypeResource) criticalSectionPermanentlyFailed() bool {
   return res.criticalSectionState == acceptedCommitInCriticalSection;
}

// We abort even if we have pre-commmitted a 2PC update. This behaviour is
// pessimistic: in principle the precommit could be rolled back, allowing this
// CS to succeed. However, logic is likely better for preventing deadlock.
func (res *TwoPCArchetypeResource) shouldAbort() bool {
   return res.criticalSectionPermanentlyFailed() ||
	   res.twoPCState == acceptedPreCommit
}


// Updates the replicas for 2PC replication This function is only for testing;
// things will likely break if this is called during 2PC operation.
func (res *TwoPCArchetypeResource) SetReplicas(replicas []ReplicaHandle) {
	res.replicas = replicas
}

func (res *TwoPCArchetypeResource) SetName(name string) {
	res.name = name
}

func (res *TwoPCArchetypeResource) EnableDebug() {
	res.debug = true
}

//--- TwoPC Related Functions


// Handler for receiving a 2PC message
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
		arg.GetType(),
		arg,
		twopc.twoPCState,
		twopc.criticalSectionState,
	);
	switch message := arg.(type) {
	case PreCommitMessage:
		if twopc.twoPCState == acceptedPreCommit {
			twopc.log("Rejected PreCommit %s: already accepted PreCommit %s", message, twopc.acceptedPreCommit)
			*reply = TwoPCReject { ResponsibleNode : twopc.acceptedPreCommit.Proposer }
		} else if twopc.criticalSectionState == hasPreCommitted {
			twopc.log("Rejected PreCommit message %s: already PreCommitted.", message.Value)
			*reply = TwoPCReject { ResponsibleNode : twopc.name }
		} else if twopc.criticalSectionState == inPreCommit {
			twopc.log("Rejected PreCommit message %s: in precommit.", message.Value)
			*reply = TwoPCReject { ResponsibleNode : twopc.name }
		} else {
			twopc.log("Accepted PreCommit message %s.", message.Value)
			*reply = TwoPCAccept{};
			twopc.twoPCState = acceptedPreCommit;
			twopc.acceptedPreCommit = message;
			twopc.log(
				"After accepting PreCommit: CS State: %s, 2PC State: %s.",
				twopc.twoPCState,
				twopc.criticalSectionState,
			);
		}
	case CommitMessage:
		if message.Proposer != twopc.acceptedPreCommit.Proposer {
			twopc.log(
				"Received Commit() message from proposer %s, but the PreCommit was from %s",
				message.Proposer,
				twopc.acceptedPreCommit.Proposer,
			)
		}  else {
			twopc.log("Accepted Commit %s", twopc.acceptedPreCommit)
            twopc.twoPCState = initial;
			twopc.value = twopc.acceptedPreCommit.Value;
			twopc.oldValue = twopc.acceptedPreCommit.Value;
			if twopc.inCriticalSection() {
				twopc.criticalSectionState = acceptedCommitInCriticalSection;
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
			twopc.twoPCState = initial;
		}
	}
	return nil
}

func (rcvr *TwoPCReceiver) Receive(arg TwoPCRequest, reply *TwoPCResponse) error {
	rcvr.log("Got an RPC request.")
	twopc := rcvr.twopc;
	return twopc.receiveInternal(arg, reply)
}

//--- Helper Functions

func assert(condition bool, message string) {
	if !condition {
		panic(message)
	}
}

func (res *TwoPCArchetypeResource) log(format string, args... interface{}) {
	if res.debug {
		printf_args := append([]interface{}{res.name}, args...)
		fmt.Printf("%s: " + format + "\n", printf_args...)
	}
}

func (res *RPCReplicaHandle) log(format string, args... interface{}) {
	if res.debug {
		fmt.Printf(format + "\n", args...)
	}
}

func (res *TwoPCReceiver) log(format string, args... interface{}) {
	res.twopc.log(format, args...)
}

func TwoPCArchetypeResourceMaker(
	value tla.TLAValue,
	address string,
	replicas []ReplicaHandle,
	name string,
	done chan *TwoPCArchetypeResource,
) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		resource := TwoPCArchetypeResource{
			value: value,
			oldValue: value,
			criticalSectionState: notInCriticalSection,
			twoPCState: initial,
			replicas: replicas,
			name: name,
			debug: false,
		}
		receiver := MakeTwoPCReceiver(&resource, address)
		go ListenAndServe(&receiver, done)
		return &resource
	})
}

func init(){
	gob.Register(TwoPCAccept{})
	gob.Register(TwoPCReject{ ResponsibleNode: ""})
	gob.Register(PreCommitMessage{ Value: tla.MakeTLANumber(0), Proposer: ""})
	gob.Register(CommitMessage{ Proposer: ""})
	gob.Register(AbortMessage{ Proposer : ""})
}

