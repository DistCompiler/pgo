package nestedcrdtimpl

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"testing"
)

func mkTestRig(idx int, reps int32, peerHosts []string) (*distsys.MPCalContext, chan tla.TLAValue) {
	rigSelf := tla.MakeTLAString(fmt.Sprintf("rig%d", idx))
	peersSet := func() tla.TLAValue {
		var peerValues []tla.TLAValue
		for peerIdx := range peerHosts {
			if peerIdx != idx {
				peerValues = append(peerValues, tla.MakeTLANumber(int32(peerIdx)))
			}
		}
		return tla.MakeTLASet(peerValues...)
	}()
	outCh := make(chan tla.TLAValue, reps)
	return distsys.NewMPCalContext(rigSelf, ATestRig,
		distsys.EnsureArchetypeRefParam("countingCh", resources.OutputChannelMaker(outCh)),
		distsys.EnsureArchetypeValueParam("iterCount", tla.MakeTLANumber(reps)),
		distsys.EnsureArchetypeRefParam("crdt", resources.NestedArchetypeMaker(func(sendCh chan<- tla.TLAValue, receiveCh <-chan tla.TLAValue) []*distsys.MPCalContext {
			self := tla.MakeTLANumber(int32(idx))
			return []*distsys.MPCalContext{
				distsys.NewMPCalContext(self, ACRDTResource,
					resources.NestedArchetypeConstantDefs,
					distsys.DefineConstantValue("ZERO_VALUE", tla.MakeTLARecord(nil)),
					distsys.EnsureArchetypeRefParam("in", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
						if !index.Equal(self) {
							panic(fmt.Errorf("only in[self] is allowed, where self = %v, and the actual index was %v", self, index))
						}
						return resources.InputChannelMaker(receiveCh)
					})),
					distsys.EnsureArchetypeRefParam("out", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
						if !index.Equal(self) {
							panic(fmt.Errorf("only out[self] is allowed, where self = %v, and the actual index was %v", self, index))
						}
						return resources.OutputChannelMaker(sendCh)
					})),
					distsys.EnsureArchetypeRefParam("peers", distsys.LocalArchetypeResourceMaker(peersSet)),
					distsys.EnsureArchetypeRefParam("network", resources.TCPMailboxesMaker(func(index tla.TLAValue) (resources.MailboxKind, string) {
						kind := resources.MailboxesRemote
						if index.Equal(self) {
							kind = resources.MailboxesLocal
						}
						return kind, peerHosts[index.AsNumber()]
					})),
					distsys.DefineConstantOperator("COMBINE_FN", func(lhs, rhs tla.TLAValue) tla.TLAValue {
						builder := immutable.NewMapBuilder(&tla.TLAValueHasher{})
						incorporate := func(fn tla.TLAValue) {
							it := fn.AsFunction().Iterator()
							for !it.Done() {
								k, v := it.Next()
								if v2, ok := builder.Get(k); ok {
									if v.(tla.TLAValue).AsNumber() > v2.(tla.TLAValue).AsNumber() {
										builder.Set(k, v)
									}
								} else {
									builder.Set(k, v)
								}
							}
						}
						incorporate(lhs)
						incorporate(rhs)
						return tla.MakeTLARecordFromMap(builder.Map())
					}),
					distsys.DefineConstantOperator("UPDATE_FN", func(self, state, v tla.TLAValue) tla.TLAValue {
						origVal := tla.TLA_Zero
						if orig, ok := state.AsFunction().Get(self); ok {
							origVal = orig.(tla.TLAValue)
						}
						return tla.MakeTLARecordFromMap(
							state.AsFunction().Set(self, tla.TLA_PlusSymbol(origVal, v)))
					}),
					distsys.DefineConstantOperator("VIEW_FN", func(state tla.TLAValue) tla.TLAValue {
						var total int32 = 0
						it := state.AsFunction().Iterator()
						for !it.Done() {
							_, counter := it.Next()
							total += counter.(tla.TLAValue).AsNumber()
						}
						return tla.MakeTLANumber(total)
					}),
				),
			}
		})),
	), outCh
}

func consumeCountsUntilStable(t *testing.T, expectedTotal int32, ch chan tla.TLAValue, ctx *distsys.MPCalContext) {
	prevCount := int32(0)
	for prevCount < expectedTotal {
		valueV := <-ch
		value := valueV.AsNumber()
		if value < prevCount {
			t.Fatalf("incrementing counter for node %v observed decreasing, from %v to %v", ctx.IFace().Self(), prevCount, valueV)
		}
		prevCount = value
	}
	if prevCount != expectedTotal {
		t.Fatalf("final count %d for node %v did not equal expected final count %d", prevCount, ctx.IFace().Self(), expectedTotal)
	}
	ctx.Stop()
}

func testForNInstances(t *testing.T, n int) {
	var peers []string
	for i := 0; i < n; i++ {
		peers = append(peers, fmt.Sprintf("localhost:8%03d", i))
	}
	var reps []int32
	var sumOfReps int32
	for i := 0; i < n; i++ {
		reps = append(reps, int32((i+1)*10))
		sumOfReps += reps[i]
	}

	var contexts []*distsys.MPCalContext
	var outChannels []chan tla.TLAValue
	for i := 0; i < n; i++ {
		ctx, outCh := mkTestRig(i, reps[i], peers)
		contexts = append(contexts, ctx)
		outChannels = append(outChannels, outCh)
	}

	// make sure that, no matter what, all contexts are cleaned up
	defer func() {
		for _, ctx := range contexts {
			ctx.Stop()
		}
	}()

	for i := 0; i < n; i++ {
		ctx := contexts[i]
		outCh := outChannels[i]
		go func() {
			err := ctx.Run()
			if err != nil {
				panic(err)
			}
			close(outCh)
		}()
	}

	for i := 0; i < n; i++ {
		consumeCountsUntilStable(t, sumOfReps, outChannels[i], contexts[i])
	}
}

func TestOneInstance(t *testing.T) {
	testForNInstances(t, 1)
}

func TestTwoInstances(t *testing.T) {
	testForNInstances(t, 2)
}

func TestThreeInstances(t *testing.T) {
	testForNInstances(t, 3)
}
