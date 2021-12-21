package shopcart_test

import (
	"benchmark"
	"fmt"
	"log"
	"math/rand"
	"testing"
	"time"

	"example.com/shopcart"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func makeNodeCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn,
	inCh, outCh chan tla.TLAValue) *distsys.MPCalContext {
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	ctx := distsys.NewMPCalContext(self, shopcart.ANode,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("crdt", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			var peers []tla.TLAValue
			nodes := shopcart.NODE_SET(iface).AsSet()
			it := nodes.Iterator()
			for !it.Done() {
				elem, _ := it.Next()
				val := elem.(tla.TLAValue)
				if !val.Equal(self) {
					peers = append(peers, val)
				}
			}
			return resources.CRDTMaker(self, peers, func(index tla.TLAValue) string {
				portNum := 8000 + index.AsNumber()
				addr := fmt.Sprintf("localhost:%d", portNum)
				return addr
			}, 5, len(peers), resources.MakeAWORSet)
		})),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(inCh)),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)),
	)
	return ctx
}

func makeNodeBenchCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn,
	outCh chan tla.TLAValue) *distsys.MPCalContext {
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	ctx := distsys.NewMPCalContext(self, shopcart.ANodeBench,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("crdt", resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
			if !index.Equal(self) {
				panic("wrong index")
			}
			var peers []tla.TLAValue
			nodes := shopcart.NODE_SET(iface).AsSet()
			it := nodes.Iterator()
			for !it.Done() {
				elem, _ := it.Next()
				val := elem.(tla.TLAValue)
				if !val.Equal(self) {
					peers = append(peers, val)
				}
			}
			return resources.CRDTMaker(self, peers, func(index tla.TLAValue) string {
				portNum := 8000 + index.AsNumber()
				addr := fmt.Sprintf("localhost:%d", portNum)
				return addr
			}, 100*time.Millisecond, len(peers), resources.MakeAWORSet)
		})),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)),
	)
	return ctx
}

func TestShopCart_Node(t *testing.T) {
	numNodes := 3
	numRequests := 10

	elems := []tla.TLAValue{
		tla.MakeTLAString("elem0"),
		tla.MakeTLAString("elem1"),
		tla.MakeTLAString("elem2"),
	}

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
		distsys.DefineConstantValue("ELEM_SET", tla.MakeTLASet(elems...)),
	}
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	var ctxs []*distsys.MPCalContext
	errs := make(chan error)
	inCh := make(chan tla.TLAValue, numRequests)
	outCh := make(chan tla.TLAValue, numRequests)
	for i := 1; i <= numNodes; i++ {
		ctx := makeNodeCtx(tla.MakeTLANumber(int32(i)), constants, inCh, outCh)
		ctxs = append(ctxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		for i := 0; i < numNodes; i++ {
			err := <-errs
			if err != nil {
				t.Fatal(err)
			}
		}
	}()

	for i := 0; i < numRequests; i++ {
		r := rand.Intn(2)

		elem := elems[i%len(elems)]
		if r == 0 {
			addReq := tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("cmd"), Value: shopcart.AddCmd(iface)},
				{Key: tla.MakeTLAString("elem"), Value: elem},
			})
			inCh <- addReq
		} else {
			remReq := tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("cmd"), Value: shopcart.RemoveCmd(iface)},
				{Key: tla.MakeTLAString("elem"), Value: elem},
			})
			inCh <- remReq
		}
	}

	for i := 0; i < numRequests; i++ {
		resp := <-outCh
		fmt.Println(resp)
	}
}

func nodeBench(t *testing.T, numNodes int, numRounds int) {
	numEvents := numRounds * numNodes * 2

	var elems []tla.TLAValue
	for i := 1; i <= numNodes; i++ {
		for j := 0; j < numRounds; j++ {
			elem := tla.MakeTLATuple(tla.MakeTLANumber(int32(i)), tla.MakeTLANumber(int32(j)))
			elems = append(elems, elem)
		}
	}

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
		distsys.DefineConstantValue("ELEM_SET", tla.MakeTLASet(elems...)),
		distsys.DefineConstantValue("BENCH_NUM_ROUNDS", tla.MakeTLANumber(int32(numRounds))),
	}
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	var ctxs []*distsys.MPCalContext
	errs := make(chan error)
	outCh := make(chan tla.TLAValue, numEvents)
	for i := 1; i <= numNodes; i++ {
		ctx := makeNodeBenchCtx(tla.MakeTLANumber(int32(i)), constants, outCh)
		ctxs = append(ctxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}

	starts := make(map[int32]time.Time)
	for i := 0; i < numEvents; i++ {
		resp := <-outCh
		node := resp.ApplyFunction(tla.MakeTLAString("node")).AsNumber()
		event := resp.ApplyFunction(tla.MakeTLAString("event"))
		if event.Equal(shopcart.AddStart(iface)) {
			starts[node] = time.Now()
		} else if event.Equal(shopcart.AddFinish(iface)) {
			elapsed := time.Since(starts[node])
			log.Println(node, elapsed)
		}
	}

	for i := 0; i < numNodes; i++ {
		err := <-errs
		if err != nil {
			t.Fatal(err)
		}
	}
}

func TestShopCart_OneNodeCrash(t *testing.T) {
	numNodes := 3
	numRequests := 5
	elems := []tla.TLAValue{
		tla.MakeTLAString("elem0"),
		tla.MakeTLAString("elem1"),
		tla.MakeTLAString("elem2"),
	}
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_NODES", tla.MakeTLANumber(int32(numNodes))),
		distsys.DefineConstantValue("ELEM_SET", tla.MakeTLASet(elems...)),
	}
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	var ctxs []*distsys.MPCalContext
	errs := make(chan error)
	inCh := make(chan tla.TLAValue, numRequests*2)
	outCh := make(chan tla.TLAValue, numRequests*2)
	for i := 1; i <= numNodes; i++ {
		ctx := makeNodeCtx(tla.MakeTLANumber(int32(i)), constants, inCh, outCh)
		ctxs = append(ctxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		for i := 0; i < numNodes; i++ {
			err := <-errs
			if err != nil {
				t.Fatal(err)
			}
		}
	}()

	makeRequests := func() {
		for i := 0; i < numRequests; i++ {
			r := rand.Intn(2)

			elem := elems[i%len(elems)]
			if r == 0 {
				addReq := tla.MakeTLARecord([]tla.TLARecordField{
					{Key: tla.MakeTLAString("cmd"), Value: shopcart.AddCmd(iface)},
					{Key: tla.MakeTLAString("elem"), Value: elem},
				})
				inCh <- addReq
			} else {
				remReq := tla.MakeTLARecord([]tla.TLARecordField{
					{Key: tla.MakeTLAString("cmd"), Value: shopcart.RemoveCmd(iface)},
					{Key: tla.MakeTLAString("elem"), Value: elem},
				})
				inCh <- remReq
			}
		}
	}

	makeRequests()
	for i := 0; i < numRequests; i++ {
		resp := <-outCh
		fmt.Println(resp)
	}
	ctxs[1].Stop()
	makeRequests()
	for i := 0; i < numRequests-1; i++ {
		resp := <-outCh
		fmt.Println(resp)
	}
}

func TestShopCart_NodeBench(t *testing.T) {
	nodeBench(t, 3, 5)
}

func TestShopCartForCompare(t *testing.T) {
	benchmark.TestAndReport(func(numNodes int) {
		nodeBench(t, numNodes, 1)
	})
}
