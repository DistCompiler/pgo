package resources

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
	"time"
)

func defaultArchetypeID() tla.TLAValue {
	return tla.MakeTLAString("node")
}

func makeLocalReplicaHandle(twopc *TwoPCArchetypeResource) ReplicaHandle {
	return LocalReplicaHandle{receiver: twopc}
}

func makeUnreplicatedTwoPC(value tla.TLAValue) *TwoPCArchetypeResource {
	return makeUnreplicatedTwoPCNamed(value, "node")
}

func makeUnreplicatedTwoPCNamed(value tla.TLAValue, name string) *TwoPCArchetypeResource {
	return &TwoPCArchetypeResource{
		value:                value,
		oldValue:             value,
		criticalSectionState: notInCriticalSection,
		twoPCState:           initial,
		replicas:             []ReplicaHandle{},
		debug:                false,
		archetypeID:          tla.MakeTLAString(name),
		timers:               make(map[string]time.Time),
	}
}

func TestInitialRead(t *testing.T) {
	magicNumber := tla.MakeTLANumber(42)
	twopc := makeUnreplicatedTwoPC(magicNumber)
	result, _ := twopc.ReadValue()
	if result != magicNumber {
		t.Errorf("Expected %s, got %s", magicNumber, result)
	}
}

func TestWriteRead(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	newNumber := tla.MakeTLANumber(50)
	twopc.WriteValue(newNumber)
	result, _ := twopc.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}
}

func TestWriteAbortRead(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	newNumber := tla.MakeTLANumber(50)
	twopc.WriteValue(newNumber)
	twopc.Abort()
	result, _ := twopc.ReadValue()
	if result != initialNumber {
		t.Errorf("Expected %s, got %s", initialNumber, result)
	}
}

func TestAcceptPreCommitPreventsRead(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	var reply TwoPCResponse
	twopc.receiveInternal(makePreCommit(tla.MakeTLANumber(50), defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	_, err := twopc.ReadValue()
	if err == nil {
		t.Errorf("Expected error")
	}
}

func TestAcceptPreCommitPreventsWrite(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	var reply TwoPCResponse
	twopc.receiveInternal(makePreCommit(tla.MakeTLANumber(50), defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	err := twopc.WriteValue(newNumber)
	if err == nil {
		t.Errorf("Expected error")
	}
}

func TestAcceptPreCommitPreventsPreCommit(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	twopc.ReadValue() // enter critical section
	var reply TwoPCResponse
	twopc.receiveInternal(makePreCommit(tla.MakeTLANumber(50), defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	err := <-twopc.PreCommit()
	if err == nil {
		t.Errorf("Expected error")
	}
}

func TestAcceptCommitReadValue(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	var reply TwoPCResponse
	twopc.receiveInternal(makePreCommit(newNumber, defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	twopc.receiveInternal(makeCommit(defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	result, _ := twopc.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}
}

func TestAcceptCommitInCriticalSectionMustAbort(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	var reply TwoPCResponse
	twopc.ReadValue() // enter critical section
	twopc.receiveInternal(makePreCommit(newNumber, defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	twopc.receiveInternal(makeCommit(defaultArchetypeID()), &reply)
	if !reply.Accept {
		t.Errorf("Got reject, wanted accept")
	}
	_, err := twopc.ReadValue()
	if err == nil {
		t.Errorf("Expected error")
	}
}

func TestInitiatePreCommitMustRejectIncoming(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	twopc.ReadValue()
	twopc.PreCommit()
	var reply TwoPCResponse
	twopc.receiveInternal(makePreCommit(newNumber, defaultArchetypeID()), &reply)
	if reply.Accept {
		t.Errorf("Got accept, wanted reject")
	}
}

func TestReplicationCommit(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)

	primary := makeUnreplicatedTwoPC(initialNumber)
	replica := makeUnreplicatedTwoPC(initialNumber)
	primary.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(replica)})
	replica.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(primary)})
	primary.WriteValue(newNumber)
	primary.PreCommit()
	primary.Commit()
	result, _ := replica.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}
}

func TestReplicationPreCommit(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)

	primary := makeUnreplicatedTwoPC(initialNumber)
	replica := makeUnreplicatedTwoPC(initialNumber)
	primary.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(replica)})
	replica.SetReplicas([]ReplicaHandle{makeLocalReplicaHandle(primary)})
	primary.WriteValue(newNumber)
	primary.PreCommit()
	_, err := replica.ReadValue()
	if err == nil {
		t.Errorf("Expected read to be rejected due to acceptance of precommit")
	}
}

func TestReplicationAbort(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)

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
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)

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
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)
	replicaAcceptedNumber := tla.MakeTLANumber(51)

	primary := makeUnreplicatedTwoPCNamed(initialNumber, "primary")
	replicaAccept := makeUnreplicatedTwoPCNamed(initialNumber, "accept")
	replicaReject := makeUnreplicatedTwoPCNamed(initialNumber, "reject")
	replicaAcceptHandle := makeLocalReplicaHandle(replicaAccept)
	replicaRejectHandle := makeLocalReplicaHandle(replicaReject)
	primary.SetReplicas([]ReplicaHandle{replicaAcceptHandle, replicaRejectHandle})
	var response TwoPCResponse
	replicaReject.receiveInternal(makePreCommit(replicaAcceptedNumber, defaultArchetypeID()), &response)
	primary.WriteValue(newNumber)
	err := <-primary.PreCommit()
	if err == nil {
		t.Errorf("PreCommit should have failed")
	}
}

func TestRPCReplication(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)

	twopc1 := makeUnreplicatedTwoPCNamed(initialNumber, "twopc1")
	twopc2 := makeUnreplicatedTwoPCNamed(initialNumber, "twopc2")
	address1 := "127.0.0.1:8000"
	address2 := "127.0.0.1:8001"
	receiver1 := makeTwoPCReceiver(twopc1, address1)
	receiver2 := makeTwoPCReceiver(twopc2, address2)
	complete := make(chan *TwoPCArchetypeResource, 2)
	go ListenAndServe(&receiver1, complete)
	go ListenAndServe(&receiver2, complete)
	<-complete
	<-complete
	handle1 := MakeRPCReplicaHandle(address1, twopc1.archetypeID)
	handle2 := MakeRPCReplicaHandle(address2, twopc2.archetypeID)
	twopc1.SetReplicas([]ReplicaHandle{&handle2})
	twopc2.SetReplicas([]ReplicaHandle{&handle1})
	twopc1.WriteValue(newNumber)
	twopc1.PreCommit()
	twopc1.Commit()
	result, _ := twopc2.ReadValue()
	if result != newNumber {
		t.Errorf("Expected %s, got %s", newNumber, result)
	}

}

func TestAbortRestoresCommitValue(t *testing.T) {
	initialNumber := tla.MakeTLANumber(42)
	newNumber := tla.MakeTLANumber(50)
	twopc := makeUnreplicatedTwoPC(initialNumber)
	twopc.ReadValue() // Enter critical section
	var response TwoPCResponse
	error := twopc.receiveInternal(makePreCommit(newNumber, defaultArchetypeID()), &response)
	if error != nil {
		t.Errorf("Error at PreCommit: %s", error)
	}
	error = twopc.receiveInternal(makeCommit(defaultArchetypeID()), &response)
	if error != nil {
		t.Errorf("Error at Commit: %s", error)
	}
	twopc.Abort()
	result, _ := twopc.ReadValue()
	if result != newNumber {
		t.Errorf("The 2PC committed value %s was expected, but got %s", newNumber, initialNumber)
	}
}