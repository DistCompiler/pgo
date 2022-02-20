package nestedcrdtimpl

import (
	"fmt"
	"log"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
)

func makeGCounterResource(idx int, peerHosts []string) distsys.ArchetypeResourceMaker {
	peersSet := func() tla.TLAValue {
		var peerValues []tla.TLAValue
		for peerIdx := range peerHosts {
			if peerIdx != idx {
				peerValues = append(peerValues, tla.MakeTLANumber(int32(peerIdx)))
			}
		}
		return tla.MakeTLASet(peerValues...)
	}()
	return resources.NestedArchetypeMaker(func(sendCh chan<- tla.TLAValue, receiveCh <-chan tla.TLAValue) []*distsys.MPCalContext {
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
				distsys.EnsureArchetypeRefParam("timer", distsys.LocalArchetypeResourceMaker(tla.TLA_TRUE)),
				//distsys.EnsureArchetypeRefParam("timer", TimerResourceMaker(100*time.Millisecond)),
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
	})
}

func mkTestRig(idx int, reps int32, peerHosts []string) (*distsys.MPCalContext, chan tla.TLAValue) {
	rigSelf := tla.MakeTLAString(fmt.Sprintf("rig%d", idx))
	outCh := make(chan tla.TLAValue, reps)
	return distsys.NewMPCalContext(rigSelf, ATestRig,
		distsys.EnsureArchetypeRefParam("countingCh", resources.OutputChannelMaker(outCh)),
		distsys.EnsureArchetypeValueParam("iterCount", tla.MakeTLANumber(reps)),
		distsys.EnsureArchetypeRefParam("crdt", makeGCounterResource(idx, peerHosts)),
	), outCh
}

func mkTestBench(idx int, numRounds int, peerHosts []string, outCh chan tla.TLAValue) *distsys.MPCalContext {
	benchSelf := tla.MakeTLAString(fmt.Sprintf("bench%d", idx))
	numNodes := len(peerHosts)
	return distsys.NewMPCalContext(benchSelf, ATestBench,
		distsys.EnsureArchetypeRefParam("crdt", makeGCounterResource(idx, peerHosts)),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)),
		distsys.EnsureArchetypeValueParam("iterCount", tla.MakeTLANumber(int32(numRounds))),
		distsys.EnsureArchetypeValueParam("numNodes", tla.MakeTLANumber(int32(numNodes))),
	)
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

func testRigForNInstances(t *testing.T, n int) {
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

func testBenchForNInstances(t *testing.T, n int) {
	numRounds := 5
	numEvents := n * numRounds * 2

	var peers []string
	for i := 0; i < n; i++ {
		peers = append(peers, fmt.Sprintf("localhost:8%03d", i))
	}

	iface := distsys.NewMPCalContextWithoutArchetype().IFace()

	outCh := make(chan tla.TLAValue, numEvents)
	errs := make(chan error, n)
	var ctxs []*distsys.MPCalContext
	for i := 0; i < n; i++ {
		ctx := mkTestBench(i, numRounds+1, peers, outCh)
		ctxs = append(ctxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}

	starts := make(map[string]time.Time)
	for i := 0; i < numEvents; i++ {
		resp := <-outCh
		node := resp.ApplyFunction(tla.MakeTLAString("node")).AsString()
		event := resp.ApplyFunction(tla.MakeTLAString("event"))
		if event.Equal(IncStart(iface)) {
			starts[node] = time.Now()
		} else if event.Equal(IncFinish(iface)) {
			elapsed := time.Since(starts[node])
			log.Println(node, elapsed)
		}
	}

	for i := 0; i < n; i++ {
		ctxs[i].Stop()
	}

	for i := 0; i < n; i++ {
		err := <-errs
		if err != nil {
			t.Fatal(err)
		}
	}
}

func TestRig_OneInstance(t *testing.T) {
	//testRigForNInstances(t, 1)
}

func TestRig_TwoInstances(t *testing.T) {
	//testRigForNInstances(t, 2)
}

func TestRig_ThreeInstances(t *testing.T) {
	//testRigForNInstances(t, 3)
}

func TestBench_OneInstance(t *testing.T) {
	//testBenchForNInstances(t, 1)
}

func TestBench_ThreeInstances(t *testing.T) {
	//testBenchForNInstances(t, 3)
}
