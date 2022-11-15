package resources

import (
	"log"
	"math/rand"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys/tla"
)

func makeUnreplicatedSet(sid string) (id tla.Value, set CRDTValue) {
	return tla.MakeString(sid), AWORSet{}.Init()
}

func makeRequest(cmd int32, val tla.Value) tla.Value {
	return tla.MakeRecord([]tla.RecordField{
		{Key: cmdKey, Value: tla.MakeNumber(cmd)},
		{Key: elemKey, Value: val},
	})
}

func defaultId() tla.Value {
	return tla.MakeString("node")
}

func TestInitAWORSet(t *testing.T) {
	_, set := makeUnreplicatedSet("node")
	result := set.Read()
	if !result.Equal(tla.MakeSet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestAdd(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val := tla.MakeNumber(0)
	set = set.Write(id, makeRequest(addOp, val))
	result := set.Read()
	expected := tla.MakeSet(val)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestAddRemove(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val := tla.MakeNumber(0)
	set = set.Write(id, makeRequest(addOp, val))
	set = set.Write(id, makeRequest(remOp, val))
	result := set.Read()
	if !result.Equal(tla.MakeSet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestMultipleAdds(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val1 := tla.MakeNumber(0)
	val2 := tla.MakeString("val2")
	val3 := tla.MakeBool(false)
	set = set.Write(id, makeRequest(addOp, val1))
	set = set.Write(id, makeRequest(addOp, val2))
	set = set.Write(id, makeRequest(addOp, val3))
	result := set.Read()
	expected := tla.MakeSet(val1, val2, val3)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestMultipleAddRemoves(t *testing.T) {
	id, set := makeUnreplicatedSet("node")
	val1 := tla.MakeNumber(0)
	val2 := tla.MakeString("val2")
	val3 := tla.MakeBool(false)
	set = set.Write(id, makeRequest(addOp, val1))
	set = set.Write(id, makeRequest(addOp, val2))
	set = set.Write(id, makeRequest(remOp, val1))
	set = set.Write(id, makeRequest(addOp, val3))
	result := set.Read()
	expected := tla.MakeSet(val2, val3)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestMergeAdds(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val1 := tla.MakeNumber(0)
	val2 := tla.MakeNumber(1)

	set1 = set1.Write(id1, makeRequest(addOp, val1))
	set2 = set2.Write(id2, makeRequest(addOp, val2))

	merged := set1.Merge(set2)
	result := merged.Read()
	expected := tla.MakeSet(val1, val2)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

func TestRemoveMyAdd(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val1 := tla.MakeNumber(0)
	val2 := tla.MakeNumber(1)

	set1 = set1.Write(id1, makeRequest(addOp, val1))
	set2 = set2.Write(id2, makeRequest(addOp, val2))

	set1 = set1.Write(id1, makeRequest(remOp, val1))
	set2 = set2.Write(id2, makeRequest(remOp, val2))

	merged := set1.Merge(set2)
	result := merged.Read()
	if !result.Equal(tla.MakeSet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestRemoveTheirAdd(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val1 := tla.MakeNumber(0)
	val2 := tla.MakeNumber(1)

	set1 = set1.Write(id1, makeRequest(addOp, val1))
	set2 = set2.Write(id2, makeRequest(addOp, val2))

	mset1 := set1.Merge(set2)
	mset2 := set2.Merge(set1)

	mset1 = mset1.Write(id1, makeRequest(remOp, val2))
	mset2 = mset2.Write(id2, makeRequest(remOp, val1))

	merged := mset1.Merge(mset2)
	result := merged.Read()
	if !result.Equal(tla.MakeSet()) {
		t.Errorf("Expected empty set, got %v", result)
	}
}

func TestAddWins(t *testing.T) {
	id1, set1 := makeUnreplicatedSet("node1")
	id2, set2 := makeUnreplicatedSet("node2")

	val := tla.MakeString("val")
	set1 = set1.Write(id1, makeRequest(addOp, val))
	set2 = set2.Merge(set1)

	set1 = set1.Write(id1, makeRequest(remOp, val))
	set2 = set2.Write(id2, makeRequest(addOp, val))

	merged := set1.Merge(set2)
	result := merged.Read()
	expected := tla.MakeSet(val)
	if !result.Equal(expected) {
		t.Errorf("Expected %v, got %v", expected, result)
	}
}

type req struct {
	cmd  int32
	elem int32
}

func TestCommutativity(t *testing.T) {
	numAdds := 6
	numRems := 2

	reqs := make([]req, numAdds+numRems)
	r := rand.New(rand.NewSource(time.Now().UnixNano()))
	for i := 0; i < numAdds; i++ {
		reqs[i] = req{addOp, int32(r.Intn(numAdds))}
	}

	for i := numAdds; i < numRems; i++ {
		reqs[i] = req{remOp, int32(r.Intn(numAdds))}
	}

	permutations := permute(reqs)

	mergedSet := tla.Value{}
	for _, perm := range permutations {
		_, thisSet := makeUnreplicatedSet("this")
		for _, req := range perm {
			other, otherSet := makeUnreplicatedSet("other")
			otherSet = otherSet.Write(other, makeRequest(req.cmd, tla.MakeNumber(req.elem)))
			thisSet = thisSet.Merge(otherSet)
		}
		finalSet := thisSet.Read()
		if !mergedSet.Equal(tla.Value{}) && !mergedSet.Equal(finalSet) {
			t.Errorf("Expected %v, got %v\n", mergedSet, finalSet)
		} else {
			mergedSet = finalSet
		}
	}
	log.Printf("Merged to: %v", mergedSet)
}

// produce permutation of requests
func permute(reqs []req) [][]req {
	var permuteHelper func([]req, int)
	permutations := make([][]req, 0)
	permuteHelper = func(reqs []req, n int) {
		if n == 1 {
			tmp := make([]req, len(reqs))
			copy(tmp, reqs)
			permutations = append(permutations, tmp)
		} else {
			for i := 0; i < n; i++ {
				permuteHelper(reqs, n-1)
				if n%2 == 1 {
					tmp := reqs[i]
					reqs[i] = reqs[n-1]
					reqs[n-1] = tmp
				} else {
					tmp := reqs[0]
					reqs[0] = reqs[n-1]
					reqs[n-1] = tmp
				}
			}
		}
	}
	permuteHelper(reqs, len(reqs))
	return permutations
}
