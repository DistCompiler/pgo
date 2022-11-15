package distsys

import (
	"fmt"
	"math/rand"
)

// FairnessCounter is an abstraction over policies for MPCal's non-deterministic
// branch selection. See ArchetypeInterface.NextFairnessCounter.
type FairnessCounter interface {
	// BeginCriticalSection will be called once per critical section, and should
	// contain any necessary set-up for that critical section's execution.
	BeginCriticalSection(pc string)
	// NextFairnessCounter may be called repeatedly within a critical section,
	// with distinct ids per distinct branching point.
	NextFairnessCounter(id string, ceiling uint) uint
}

type roundRobinFairnessCounterRecord struct {
	id             string
	count, ceiling uint
}

type roundRobinFairnessCounter struct {
	pc           string
	counterStack []roundRobinFairnessCounterRecord
	counterIdx   int
}

var _ FairnessCounter = &roundRobinFairnessCounter{}

// MakeRoundRobinFairnessCounter produces a FairnessCounter that follows a
// round-robin pattern.
// This process is similar to BigInt incrementation, but also tracking branch
// identifiers and trying to be robust to changes in the ceiling value (which
// may happen if we are exploring selections from a set whose cardinality
// changes).
func MakeRoundRobinFairnessCounter() FairnessCounter {
	return &roundRobinFairnessCounter{}
}

func (cnt *roundRobinFairnessCounter) BeginCriticalSection(pc string) {
	cnt.counterIdx = 0
	if pc != cnt.pc { // if different pc, reset everything
		cnt.counterStack = cnt.counterStack[:0]
		cnt.pc = pc
	}
	// "increment" the current counter, but make sure to explore the
	// "furthest-along" state first this is important because not all execution
	// paths will get "that far", so exploring "earlier" state first can skip
	// branches.
	counterStack := cnt.counterStack
	var carry uint = 1
	for idx := len(counterStack) - 1; idx >= 0; idx-- {
		count, ceiling := counterStack[idx].count, counterStack[idx].ceiling
		count += carry
		carry = 0
		if count >= ceiling {
			carry = count / ceiling
			count = count % ceiling
		}
		counterStack[idx].count = count
	}
}

func (cnt *roundRobinFairnessCounter) NextFairnessCounter(id string, ceiling uint) uint {
	idx := cnt.counterIdx
	cnt.counterIdx++

	if idx > len(cnt.counterStack) {
		panic(fmt.Errorf("bad state: index %d is invalid for stack %v", idx, cnt.counterStack))
	}

	// if the id or ceiling don't match, drop the rest of the stack as we have
	// shifted nested branches / changed cardinality.
	// note: the cardinality part optimises a case where element selection is
	//       looped with element removal, or a set selection is otherwise
	//       "disturbed"; no sense in traversing more than the first element if
	//       the set has been "freshened" ... and it also makes increment logic
	//       conceptually simpler, as we can "trust" the stored ceiling value.
	if idx < len(cnt.counterStack) && (cnt.counterStack[idx].id != id || cnt.counterStack[idx].ceiling != ceiling) {
		cnt.counterStack = cnt.counterStack[:idx]
	}

	// if we are top of stack, initialise to a random value
	if idx == len(cnt.counterStack) {
		cnt.counterStack = append(cnt.counterStack, roundRobinFairnessCounterRecord{
			id:      id,
			count:   uint(rand.Uint32()) % ceiling,
			ceiling: ceiling,
		})
	}

	countToReturn := cnt.counterStack[idx].count
	if countToReturn >= ceiling {
		panic(fmt.Errorf("bad state: tried to return count %d, which doesn't fit ceiling %d", countToReturn, ceiling))
	}
	return countToReturn
}
