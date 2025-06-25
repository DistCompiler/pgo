package tla

import (
	"testing"
)

type MergeOp struct {
	From, To int
	IsLeft   bool
}

func (op MergeOp) perform(clks []VClock) {
	if op.IsLeft {
		clks[op.From] = clks[op.From].Merge(clks[op.To])
	} else {
		clks[op.To] = clks[op.To].Merge(clks[op.From])
	}
}

func genOpSequences(fuel int, clkCount int) ([][]MergeOp, [][]MergeOp) {
	if fuel == 0 {
		return [][]MergeOp{{}}, [][]MergeOp{{}}
	} else {
		allSeqs, addedSeqs := genOpSequences(fuel-1, clkCount)
		var nextAddedSeqs [][]MergeOp
		for _, addedSeq := range addedSeqs {
			for _, isLeft := range []bool{false, true} {
				for i := range clkCount {
					for j := range clkCount {
						var nextAddedSeq []MergeOp
						nextAddedSeq = append(nextAddedSeq, addedSeq...)
						nextAddedSeq = append(nextAddedSeq, MergeOp{
							From:   i,
							To:     j,
							IsLeft: isLeft,
						})
						allSeqs = append(allSeqs, nextAddedSeq)
						nextAddedSeqs = append(nextAddedSeqs, nextAddedSeq)
					}
				}
			}
		}
		return allSeqs, nextAddedSeqs
	}
}

func TestVClockMerge(t *testing.T) {
	const clkCount = 3
	opSequences, _ := genOpSequences(2, clkCount)
	for _, opSeq := range opSequences {
		var clks [clkCount]VClock
		clks[0] = clks[0].Inc("foo", MakeNumber(1))
		for _, op := range opSeq {
			op.perform(clks[:])
		}

		resultingClk1 := clks[0].Get("foo", MakeNumber(1))
		if resultingClk1 != 1 {
			t.Errorf("clks[0] became other than 1: %v", clks)
		}
	}
}
