package resources

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
	"time"
)

func defaultArchetypeID() tla.Value {
	return tla.MakeString("node")
}

func makeLocalReplicaHandle(twopc *TwoPCArchetypeResource) ReplicaHandle {
	return LocalReplicaHandle{receiver: twopc}
}

func makeUnreplicatedTwoPC(value tla.Value) *TwoPCArchetypeResource {
	return makeUnreplicatedTwoPCNamed(value, "node")
}

func makeUnreplicatedTwoPCNamed(value tla.Value, name string) *TwoPCArchetypeResource {
	return &TwoPCArchetypeResource{
		value:                value,
		oldValue:             value,
		criticalSectionState: notInCriticalSection,
		twoPCState:           initial,
		replicas:             []ReplicaHandle{},
		logLevel:             defaultLogLevel,
		archetypeID:          tla.MakeString(name),
		timers:               make(map[string]time.Time),
		version:              0,
		senderTimes:          make(map[tla.Value]int64),
	}
}

func TestInitialRead(t *testing.T) {
	magicNumber := tla.MakeNumber(42)
	twopc := makeUnreplicatedTwoPC(magicNumber)
	result, _ := twopc.ReadValue()
	if result != magicNumber {
		t.Errorf("Expected %s, got %s", magicNumber, result)
	}
}

func TestWriteRead(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	newNumber := tla.MakeNumber(50)
	twopc.WriteValue(newNumber)
	result, _ := twopc.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}
}

func TestWriteAbortRead(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	newNumber := tla.MakeNumber(50)
	twopc.WriteValue(newNumber)
	twopc.Abort()
	result, _ := twopc.ReadValue()
	if result != initialNumber {
		t.Errorf("Expected %s, got %s", initialNumber, result)
	}
}

func TestAcceptPreCommitAllowsRead(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	senderNumber := tla.MakeNumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	sender := makeUnreplicatedTwoPCNamed(senderNumber, "sender")
	var reply TwoPCResponse
	twopc.receiveInternal(sender.makePreCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	_, err := twopc.ReadValue()
	if err != nil {
		t.Errorf("Unexpected error")
	}
}

func TestAcceptPreCommitAllowsWrite(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	sender := makeUnreplicatedTwoPCNamed(newNumber, "sender")
	var reply TwoPCResponse
	twopc.receiveInternal(sender.makePreCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	err := twopc.WriteValue(newNumber)
	if err != nil {
		t.Errorf("Unexpected error")
	}
}

func TestAcceptPreCommitPreventsPreCommit(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	sender := makeUnreplicatedTwoPCNamed(newNumber, "sender")
	twopc := makeUnreplicatedTwoPC(initialNumber)
	twopc.ReadValue() // enter critical section
	var reply TwoPCResponse
	twopc.receiveInternal(sender.makePreCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	err := <-twopc.PreCommit()
	if err == nil {
		t.Errorf("Expected error")
	}
}

func TestAcceptCommitReadValue(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	sender := makeUnreplicatedTwoPC(newNumber)
	var reply TwoPCResponse
	twopc.receiveInternal(sender.makePreCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	twopc.receiveInternal(sender.makeCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	result, _ := twopc.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}
}

func TestAcceptCommitInCriticalSectionMustAbort(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	sender := makeUnreplicatedTwoPCNamed(newNumber, "sender")
	var reply TwoPCResponse
	twopc.ReadValue() // enter critical section
	twopc.receiveInternal(sender.makePreCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	twopc.receiveInternal(sender.makeCommit(), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	_, err := twopc.ReadValue()
	if err == nil {
		t.Errorf("Expected error")
	}
}

func TestInitiatePreCommitMustRejectIncoming(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	sender := makeUnreplicatedTwoPCNamed(newNumber, "sender")
	twopc.ReadValue()
	err := twopc.PreCommit()
	<-err
	var reply TwoPCResponse
	twopc.receiveInternal(sender.makePreCommit(), &reply)
	if reply.Accept {
		t.Errorf("Got accept, wanted reject")
	}
}

func TestReplicationCommit(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)

	primary := makeUnreplicatedTwoPC(initialNumber)
	replica := makeUnreplicatedTwoPC(initialNumber)
	primary.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(replica)})
	replica.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(primary)})
	primary.WriteValue(newNumber)
	err := primary.PreCommit()
	<-err
	primary.Commit()
	result, _ := replica.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}
}

func TestReplicationPreCommit(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)

	primary := makeUnreplicatedTwoPC(initialNumber)
	replica := makeUnreplicatedTwoPC(initialNumber)
	primary.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(replica)})
	replica.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(primary)})
	primary.WriteValue(newNumber)
	<-primary.PreCommit()
	_, err := replica.ReadValue()
	if err != nil {
		t.Errorf("Read was rejected unexpectedly")
	}
}

func TestReplicationAbort(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)

	primary := makeUnreplicatedTwoPC(initialNumber)
	replica := makeUnreplicatedTwoPC(initialNumber)
	primary.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(replica)})
	replica.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(primary)})
	primary.WriteValue(newNumber)
	primary.PreCommit()
	primary.Abort()
	result, _ := replica.ReadValue()
	if result != initialNumber {
		t.Errorf("Expected %s, got %s", initialNumber, result)
	}
}

func TestReplicationAbortInCriticalSection(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)

	primary := makeUnreplicatedTwoPC(initialNumber)
	replica := makeUnreplicatedTwoPC(initialNumber)
	primary.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(replica)})
	replica.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(primary)})
	replica.ReadValue() // replica enter critical section
	primary.WriteValue(newNumber)
	primary.PreCommit()
	primary.Abort()
	result, _ := replica.ReadValue()
	if result != initialNumber {
		t.Errorf("Expected %s, got %s", initialNumber, result)
	}
}

func TestReplicationFailedPreCommit(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	replicaAcceptedNumber := tla.MakeNumber(51)

	primary1 := makeUnreplicatedTwoPCNamed(initialNumber, "primary1")
	primary2 := makeUnreplicatedTwoPCNamed(replicaAcceptedNumber, "primary2")
	replicaAccept := makeUnreplicatedTwoPCNamed(initialNumber, "accept")
	replicaReject := makeUnreplicatedTwoPCNamed(initialNumber, "reject")
	replicaReject2 := makeUnreplicatedTwoPCNamed(initialNumber, "reject2")
	replicaAcceptHandle := makeLocalReplicaHandle(replicaAccept)
	replicaRejectHandle := makeLocalReplicaHandle(replicaReject)
	replicaReject2Handle := makeLocalReplicaHandle(replicaReject2)
	primary1.SetReplicas([]ReplicaHandle{replicaAcceptHandle, replicaRejectHandle, replicaReject2Handle})
	var response TwoPCResponse
	replicaReject.receiveInternal(primary2.makePreCommit(), &response)
	replicaReject2.receiveInternal(primary2.makePreCommit(), &response)
	primary1.WriteValue(newNumber)
	err := <-primary1.PreCommit()
	if err == nil {
		t.Errorf("PreCommit should have failed")
	}
}

func TestRPCReplication(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)

	twopc1 := makeUnreplicatedTwoPCNamed(initialNumber, "twopc1")
	twopc2 := makeUnreplicatedTwoPCNamed(initialNumber, "twopc2")
	address1 := "127.0.0.1:8000"
	address2 := "127.0.0.1:8001"
	receiver1 := makeTwoPCReceiver(twopc1, address1)
	receiver2 := makeTwoPCReceiver(twopc2, address2)
	go receiver1.listenAndServe()
	go receiver2.listenAndServe()
	time.Sleep(50 * time.Millisecond)
	handle1 := MakeRPCReplicaHandle(address1, twopc1.archetypeID)
	handle2 := MakeRPCReplicaHandle(address2, twopc2.archetypeID)
	twopc1.SetReplicas([]ReplicaHandle{&handle2})
	twopc2.SetReplicas([]ReplicaHandle{&handle1})
	twopc1.WriteValue(newNumber)
	<-twopc1.PreCommit()
	twopc1.Commit()
	result, _ := twopc2.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}

}

func TestAbortRestoresCommitValue(t *testing.T) {
	initialNumber := tla.MakeNumber(42)
	newNumber := tla.MakeNumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	sender := makeUnreplicatedTwoPCNamed(newNumber, "sender")
	twopc.ReadValue() // Enter critical section
	var response TwoPCResponse
	error := twopc.receiveInternal(sender.makePreCommit(), &response)
	if error != nil {
		t.Errorf("Error at PreCommit: %s", error)
	}
	error = twopc.receiveInternal(sender.makeCommit(), &response)
	if error != nil {
		t.Errorf("Error at Commit: %s", error)
	}
	twopc.Abort()
	result, _ := twopc.ReadValue()
	if result != newNumber {
		t.Errorf("The 2PC committed value %s was expected, but got %s", newNumber, initialNumber)
	}
}
