package main

import (
	"example.com/shopcart"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"log"
)

var numNodes = 5

var addrs = map[int32]string{
	1: "localhost:8000",
	2: "localhost:8001",
	3: "localhost:8002",
	4: "localhost:8003",
	5: "localhost:8004",
}

func getAWORSetMaker(self tla.TLAValue) distsys.ArchetypeResourceMaker {
	peers := make([]tla.TLAValue, 0)
	for nid := range addrs {
		if nid != self.AsNumber() {
			peers = append(peers, tla.MakeTLANumber(nid))
		}
	}
	return resources.IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
		if !index.Equal(self) {
			panic("wrong index")
		}
		return resources.CRDTMaker(index, peers, func(index tla.TLAValue) string {
			return addrs[index.AsNumber()]
		}, resources.MakeAWORSet)
	})
}

func main() {
	replicaCtxs := make([]*distsys.MPCalContext, numNodes)
	replicaChans := make([]shopcart.NodeChannels, numNodes)
	doneChan := make(chan struct{}, numNodes)
	outChan := make(chan tla.TLAValue)
	for i := 1; i <= numNodes; i++ {
		self := tla.MakeTLANumber(int32(i))
		in := make(chan tla.TLAValue)
		ctx := distsys.NewMPCalContext(self, shopcart.ANode,
			distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(in)),
			distsys.EnsureArchetypeRefParam("crdt", getAWORSetMaker(self)),
		)
		replicaCtxs[i-1] = ctx
		replicaChans[i-1] = shopcart.NodeChannels{
			In :  in,
			Done: doneChan,
		}

	}

	for _, ctx := range replicaCtxs {
		go ctx.Run()
	}

	go func() {
		for i := 1; i <= numNodes; i++ {
			<- doneChan
		}
		for _, ctx := range replicaCtxs {
			ctx.Stop()
		}

		getVal := func(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
			crdt, err := ctx.IFace().RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return tla.TLAValue{}, err
			}
			return ctx.IFace().Read(crdt, []tla.TLAValue{ctx.IFace().Self()})
		}

		allEquallyDefined := func(vals []tla.TLAValue) bool {
			if vals[0].Equal(tla.TLAValue{}) {
				return false
			}
			for i := 1; i < len(vals); i++ {
				if !vals[i].Equal(vals[0]) {
					return false
				}
			}
			return true
		}

		// read until all crdt set values converge
		var vals = make([]tla.TLAValue, numNodes)
		for !allEquallyDefined(vals) {
			for i, ctx := range replicaCtxs {
				replicaVal, err := getVal(ctx)
				if err != nil {
					log.Fatalf("could not read value from cntr")
				}
				vals[i] = replicaVal
			}
		}
		outChan <- vals[0]
	}()

	shopcart.Benchmark(replicaChans, outChan)
}