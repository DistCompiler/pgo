package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"errors"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys"
	"net"
	"net/rpc"
)

//--- TwoPC Protocol

// TODO: Add a a unique ID associated for this iteration of 2PC
//       This is necessary for associating Aborts / Commits to
//       previous PreCommit requests
type TwoPCRequest interface{}

type PreCommitMessage struct {
   Value tla.TLAValue
}

func (m PreCommitMessage) GobEncode() ([]byte, error) {
	var buf bytes.Buffer
	encoder := gob.NewEncoder(&buf)
	err := encoder.Encode(&m.Value)
	return buf.Bytes(), err
}

func (m *PreCommitMessage) GobDecode(input []byte) error {
	buf := bytes.NewBuffer(input)
	decoder := gob.NewDecoder(buf)
	return decoder.Decode(&m.Value)
}

// TODO: Add a a unique ID associated for this iteration of 2PC
type CommitMessage struct {}

// TODO: Add a a unique ID associated for this iteration of 2PC
type AbortMessage struct {}

type TwoPCResponse int

const (
	accept TwoPCResponse = iota
	reject
)

//--- TwoPC IO

type TwoPCReceiver struct {
	ListenAddr string
	done chan struct{}
	twopc *twopcArchetypeResource
	debug bool // Whether or not to display debug output
}

// Interface for connecting with 2PC replicas
// Basically the same as the RPC interface, but allows for custom transports
type ReplicaHandle interface {
	Send(request TwoPCRequest, reply *TwoPCResponse) chan error
}

// Interact with a local replica. Most likely only useful for testing
type LocalReplicaHandle struct {
	receiver *twopcArchetypeResource
}

func (handle LocalReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	error_channel := make(chan error, 1)
	err := handle.receiver.receiveInternal(request, reply)
	error_channel <- err
	return error_channel
}

// Interface for connecting with 2PC replicas over RPC
type RPCReplicaHandle struct {
    client *rpc.Client
	debug bool // Whether or not to display debug output
}

func (handle RPCReplicaHandle) Send(request TwoPCRequest, reply *TwoPCResponse) chan error {
	assert(reply != nil, "reply was not initialized correctly")

	client := handle.client
	assert(client != nil, "client was not initialized correctly")

	error_channel := make(chan error, 1)
	handle.log("RPC call initiated with request %s\n", request)
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
func ListenAndServe(rpcRcvr *TwoPCReceiver) error {
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

func MakeClient(address string) (*rpc.Client, error) {
	conn, err := net.Dial("tcp", address)
	if err != nil {
		return nil, err
	}
	return rpc.NewClient(conn), nil
}

//--- Archetype and state data structures

type twopcArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin

	// Current value, and value in the critical state respectively
	value, oldValue tla.TLAValue

	// The saved preCommit value from 2PC
	precommitValue tla.TLAValue

	// State relating to the local critical section
	criticalSectionState CriticalSectionState

	// State relating to 2PC replication
	twoPCState TwoPCState

	// Replicas for 2PC
	replicas []ReplicaHandle

	// Name for debug purposes
	name string

	// Whether or not to enable debugging
	debug bool
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
	case hasPreCommitted:
		return "hasPreCommitted"
	}
	return "unknown"
}


//--- Archetype Functions

// Abort the current critical section state
// If were also attempting 2PC replication, sned a rollback message
func (res *twopcArchetypeResource) Abort() chan struct{} {
	res.value = res.oldValue;
	if res.criticalSectionState == hasPreCommitted {
		for _, r := range res.replicas {
			request := AbortMessage {}
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
		}
	}
	res.criticalSectionState = notInCriticalSection;
	return nil
}


// Local Critical Section PreCommit. This triggers the 2PC PreCommit on all
// relicas. If any replica refuses the PreCommit(), then this should fail
func (res *twopcArchetypeResource) PreCommit() chan error {
	channel := make(chan error, 1)
	if res.shouldAbort() {
		channel <- errors.New("Cannot PreCommit() now")
		return channel
	}
	res.criticalSectionState = hasPreCommitted;
	var num_successful_precommits = 0
	for _, r := range res.replicas {
		request := PreCommitMessage { res.value }
		var reply TwoPCResponse
		err_channel := r.Send(request, &reply)
		err := <-err_channel
		if err != nil {
			res.criticalSectionState = notInCriticalSection
			channel <- err
			break
		}
		if reply == reject {
			channel <- errors.New("Recieved error calling PreCommit")
			break
		}
		num_successful_precommits += 1
	}

	if num_successful_precommits != len(res.replicas) {
		for _, r := range res.replicas[0:num_successful_precommits] {
			request := AbortMessage {}
			var reply TwoPCResponse
			call := r.Send(request, &reply)
			<-call
		}
		return channel
	} else {
		res.log("Successful PreCommit")
		return nil
	}

}

// Unconditionally Commit, also performing the 2PC commit at this time This is
// safe because `PreCommit` has already succeeded, thus all Replicas have
// already accepted the PreCommit and are able to accept the Commit() message.
func (res *twopcArchetypeResource) Commit() chan struct{} {
	// Commit 2PC transaction here
	request := CommitMessage {}
	for _, r := range res.replicas {
		var reply TwoPCResponse
		call := r.Send(request, &reply)
		<-call
	}
	res.log("Commit() has been acknowledged by all replicas")
	res.oldValue = res.value;
	res.criticalSectionState = notInCriticalSection;
	return nil
}

func (res *twopcArchetypeResource) ReadValue() (tla.TLAValue, error) {
	if res.shouldAbort() {
		res.log("ReadValue() rejected")
		return tla.TLAValue{}, errors.New("Cannot ReadValue() now")
	}
	res.log("ReadValue() allowed")
	res.criticalSectionState = inUninterruptedCriticalSection;
	return res.value, nil
}

func (res *twopcArchetypeResource) WriteValue(value tla.TLAValue) error {
	if res.shouldAbort() {
		return errors.New("Cannot WriteValue() now")
	}
	res.value = value
	res.criticalSectionState = inUninterruptedCriticalSection;
	return nil
}

// TODO: Any cleanup logic
func (res *twopcArchetypeResource) Close() error {
	return nil
}

func (res *twopcArchetypeResource) inCriticalSection() bool {
   return res.criticalSectionState != notInCriticalSection
}

// If a resource accepted a commit while in a critical section,
// this critical section must abort, because serializability is violated
// TODO: Consider case when the accepted commit has the same value as before
//       entering the critical section, or if the local value hasn't yet been
//       *read* in the critical section.
func (res *twopcArchetypeResource) criticalSectionPermanentlyFailed() bool {
   return res.criticalSectionState == acceptedCommitInCriticalSection;
}

// We abort even if we have pre-commmitted a 2PC update. This behaviour is
// pessimistic: in principle the precommit could be rolled back, allowing this
// CS to succeed. However, logic is likely better for preventing deadlock.
func (res *twopcArchetypeResource) shouldAbort() bool {
   return res.criticalSectionPermanentlyFailed() ||
	   res.twoPCState == acceptedPreCommit
}


// Updates the replicas for 2PC replication This function is only for testing;
// things will likely break if this is called during 2PC operation.
func (res *twopcArchetypeResource) SetReplicas(replicas []ReplicaHandle) {
	res.replicas = replicas
}

func (res *twopcArchetypeResource) SetName(name string) {
	res.name = name
}

func (res *twopcArchetypeResource) EnableDebug() {
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
func (twopc *twopcArchetypeResource) receiveInternal(arg TwoPCRequest, reply *TwoPCResponse) error {
	switch message := arg.(type) {
	case PreCommitMessage:
		twopc.log(
			"Received a PreCommit message. CS State: %s, 2PC State: %s.",
			twopc.twoPCState,
			twopc.criticalSectionState,
		);
		if twopc.twoPCState == acceptedPreCommit || twopc.criticalSectionState == hasPreCommitted {
			twopc.log("Rejected the PreCommit message.")
			*reply = reject;
		} else {
			twopc.log("Accepted the PreCommit message.")
			*reply = accept;
			twopc.twoPCState = acceptedPreCommit;
			twopc.precommitValue = message.Value;
			twopc.log(
				"After accepting PreCommit: CS State: %s, 2PC State: %s.",
				twopc.twoPCState,
				twopc.criticalSectionState,
			);
		}
	case CommitMessage:
		if twopc.twoPCState != acceptedPreCommit {
			return errors.New("Called commit in wrong state")
		} else {
			twopc.log("Accepted Commit")
            twopc.twoPCState = initial;
			twopc.value = twopc.precommitValue;
			twopc.oldValue = twopc.precommitValue;
			if twopc.inCriticalSection() {
				twopc.criticalSectionState = acceptedCommitInCriticalSection;
			}
		}
	case AbortMessage:
		twopc.twoPCState = initial;
		if twopc.inCriticalSection() && !twopc.criticalSectionPermanentlyFailed() {
			twopc.criticalSectionState = inUninterruptedCriticalSection;
		}
	}
	return nil
}

func (rcvr *TwoPCReceiver) Receive(arg TwoPCRequest, reply *TwoPCResponse) error {
	rcvr.log("Got an RPC request.\n")
	twopc := rcvr.twopc;
	return twopc.receiveInternal(arg, reply)
}

//--- Helper Functions

// Assertions are for conditions that should always be true
// even if the protocol is violated.
func assert(condition bool, message string) {
	if !condition {
		panic(message)
	}
}

func (res *twopcArchetypeResource) log(format string, args... interface{}) {
	if res.debug {
		printf_args := append([]interface{}{res.name}, args...)
		fmt.Printf("%s: " + format + "\n", printf_args...)
	}
}

func (res *RPCReplicaHandle) log(format string, args... interface{}) {
	if res.debug {
		fmt.Printf("%s: " + format + "\n", args...)
	}
}

func (res *TwoPCReceiver) log(format string, args... interface{}) {
	if res.debug {
		fmt.Printf("%s: " + format + "\n", args...)
	}
}

func TwoPCArchetypeResourceMaker(value tla.TLAValue, replicas []ReplicaHandle) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &twopcArchetypeResource{
			value: value,
			oldValue: value,
			criticalSectionState: notInCriticalSection,
			twoPCState: initial,
			replicas: replicas,
		}
	})
}

func init(){
	gob.Register(PreCommitMessage{tla.TLAValue{}})
	gob.Register(CommitMessage{})
	gob.Register(AbortMessage{})
}

