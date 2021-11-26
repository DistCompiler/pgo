package resources

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
)

func makeUnreplicatedSet(sid string) (id tla.TLAValue, set crdtValue) {
	return tla.MakeTLAString(sid), MakeAWORSet()
}

func makeRequest(cmd int32, val tla.TLAValue) tla.TLAValue {
	return tla.MakeTLARecord([]tla.TLARecordField{
		{Key: cmdKey, Value: tla.MakeTLANumber(cmd)},
		{Key: elemKey, Value: val},
	})
}

func defaultId() tla.TLAValue {
	return tla.MakeTLAString("node")
}

func TestInitAWORSet(t *testing.T) {
	_, set := makeUnreplicatedSet("node")
	result := set.Read()
	if !result.Equal(tla.MakeTLASet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestAdd(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val := tla.MakeTLANumber(0)
	set = set.Write(id, makeRequest(ADD, val))
	result := set.Read()
	expected := tla.MakeTLASet(val)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestAddRemove(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val := tla.MakeTLANumber(0)
	set = set.Write(id, makeRequest(ADD, val))
	set = set.Write(id, makeRequest(REMOVE, val))
	result := set.Read()
	if !result.Equal(tla.MakeTLASet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestMultipleAdds(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val1 := tla.MakeTLANumber(0)
	val2 := tla.MakeTLAString("val2")
	val3 := tla.MakeTLABool(false)
	set = set.Write(id, makeRequest(ADD, val1))
	set = set.Write(id, makeRequest(ADD, val2))
	set = set.Write(id, makeRequest(ADD, val3))
	result := set.Read()
	expected := tla.MakeTLASet(val1, val2, val3)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestMultipleAddRemoves(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val1 := tla.MakeTLANumber(0)
	val2 := tla.MakeTLAString("val2")
	val3 := tla.MakeTLABool(false)
	set = set.Write(id, makeRequest(ADD, val1))
	set = set.Write(id, makeRequest(ADD, val2))
	set = set.Write(id, makeRequest(REMOVE, val1))
	set = set.Write(id, makeRequest(ADD, val3))
	result := set.Read()
	expected := tla.MakeTLASet(val2, val3)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestMergeAdds(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val1 := tla.MakeTLANumber(0)
	val2 := tla.MakeTLANumber(1)

	set1 = set1.Write(id1, makeRequest(ADD, val1))
	set2 = set2.Write(id2, makeRequest(ADD, val2))

	merged := set1.Merge(set2)
	result := merged.Read()
	expected := tla.MakeTLASet(val1, val2)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestRemoveMyAdd(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val1 := tla.MakeTLANumber(0)
	val2 := tla.MakeTLANumber(1)

	set1 = set1.Write(id1, makeRequest(ADD, val1))
	set2 = set2.Write(id2, makeRequest(ADD, val2))

	set1 = set1.Write(id1, makeRequest(REMOVE, val1))
	set2 = set2.Write(id2, makeRequest(REMOVE, val2))

	merged := set1.Merge(set2)
	result := merged.Read()
	if !result.Equal(tla.MakeTLASet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestRemoveTheirAdd(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val1 := tla.MakeTLANumber(0)
	val2 := tla.MakeTLANumber(1)

	set1 = set1.Write(id1, makeRequest(ADD, val1))
	set2 = set2.Write(id2, makeRequest(ADD, val2))

	mset1 := set1.Merge(set2)
	mset2 := set2.Merge(set1)

	mset1 = mset1.Write(id1, makeRequest(REMOVE, val2))
	mset2 = mset2.Write(id2, makeRequest(REMOVE, val1))

	merged := mset1.Merge(mset2)
	result := merged.Read()
	if !result.Equal(tla.MakeTLASet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestAddWins(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val := tla.MakeTLAString("val")
	set1 = set1.Write(id1, makeRequest(ADD, val))
	set2 = set2.Merge(set1)

	set1 = set1.Write(id1, makeRequest(REMOVE, val))
	set2 = set2.Write(id2, makeRequest(ADD, val))

	merged := set1.Merge(set2)
	result := merged.Read()
	expected := tla.MakeTLASet(val)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}
