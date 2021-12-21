package kvs

import (
	"fmt"
	"log"
	"math/rand"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNetworkMaker(nodeIndex int) distsys.ArchetypeResourceMaker {
	return resources.TCPMailboxesMaker(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			kind := resources.MailboxesRemote
			if nodeIndex == int(idx.AsNumber()) {
				kind = resources.MailboxesLocal
			}
			port := 9000 + idx.AsNumber()
			addr := fmt.Sprintf("localhost:%d", port)
			return kind, addr
		},
	)
}

func getListenAddress(nodeIndex int) string {
	return fmt.Sprintf("localhost:%d", 8000+nodeIndex)
}

func getArchetypeID(nodeIndex int) tla.TLAValue {
	return tla.MakeTLANumber(int32(nodeIndex))
}

func getReplicas(selfIndex int, numNodes int) []resources.ReplicaHandle {
	var replicas []resources.ReplicaHandle
	for i := 0; i < numNodes; i++ {
		if i == selfIndex {
			continue
		}
		globalID := i
		handle := resources.MakeRPCReplicaHandle(getListenAddress(globalID), getArchetypeID(globalID))
		replicas = append(replicas, &handle)
	}
	return replicas
}

func makeServerContext(nodeIndex int, numServers int, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	replicas := getReplicas(nodeIndex, numServers)
	twoPCMaker := resources.TwoPCArchetypeResourceMaker(
		tla.MakeTLAFunction([]tla.TLAValue{tla.MakeTLASet()}, nil),
		getListenAddress(nodeIndex),
		replicas,
		getArchetypeID(nodeIndex),
		nil,
	)

	return distsys.NewMPCalContext(getArchetypeID(nodeIndex), AServer,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("kvs", twoPCMaker),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(nodeIndex)),
	)
}

const monAddr = "localhost:9500"

func makeClientCtx(nodeIndex int, constants []distsys.MPCalContextConfigFn,
	inCh, outCh chan tla.TLAValue) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(getArchetypeID(nodeIndex), AClient,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(nodeIndex)),
		distsys.EnsureArchetypeRefParam("in", resources.InputChannelMaker(inCh)),
		distsys.EnsureArchetypeRefParam("out", resources.OutputChannelMaker(outCh)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
	)
	return ctx
}

func setupMonitor() *resources.Monitor {
	mon := resources.NewMonitor(monAddr)
	go func() {
		if err := mon.ListenAndServe(); err != nil {
			log.Fatal(err)
		}
	}()
	return mon
}

func runTest(t *testing.T, numServers int, numClients int) {
	numRequests := 1000

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(int32(numServers))),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(int32(numClients))),
	}
	mon := setupMonitor()

	var ctxs []*distsys.MPCalContext
	errs := make(chan error)

	var serverCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		ctx := makeServerContext(i, numServers, constants)
		serverCtxs = append(serverCtxs, ctx)
		ctxs = append(ctxs, ctx)

		go func() {
			errs <- mon.RunArchetype(ctx)
		}()
	}

	inCh := make(chan tla.TLAValue, numRequests)
	outCh := make(chan tla.TLAValue, numRequests)
	for i := numServers + 1; i <= numServers+numClients; i++ {
		ctx := makeClientCtx(i, constants, inCh, outCh)
		ctxs = append(ctxs, ctx)

		go func() {
			errs <- ctx.Run()
		}()
	}

	defer func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		log.Println("stop done")
		for range ctxs {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %v", err)
			}
		}
	}()

	keys := []tla.TLAValue{
		tla.MakeTLAString("key0"),
		tla.MakeTLAString("key1"),
		tla.MakeTLAString("key2"),
		tla.MakeTLAString("key4"),
		tla.MakeTLAString("key5"),
		tla.MakeTLAString("key6"),
		tla.MakeTLAString("key7"),
		tla.MakeTLAString("key8"),
		tla.MakeTLAString("key9"),
	}
	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()

	start := time.Now()

	for i := 0; i < numRequests; i++ {
		r := rand.Intn(2)

		key := keys[i%len(keys)]
		if r == 0 {
			valueStr := fmt.Sprintf("value%d", i)
			value := tla.MakeTLAString(valueStr)
			putReq := tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: Put(iface)},
				{Key: tla.MakeTLAString("key"), Value: key},
				{Key: tla.MakeTLAString("value"), Value: value},
			})
			//log.Println(putReq)
			inCh <- putReq
		} else {
			getReq := tla.MakeTLARecord([]tla.TLARecordField{
				{Key: tla.MakeTLAString("type"), Value: Get(iface)},
				{Key: tla.MakeTLAString("key"), Value: key},
			})
			//log.Println(getReq)
			inCh <- getReq
		}
	}

	for i := 0; i < numRequests; i++ {
		<-outCh
		//resp := <-outCh
		//log.Println(resp)
	}

	elapsed := time.Since(start)

	fmt.Printf("elapsed = %s, iops = %f\n", elapsed, float64(numRequests)/elapsed.Seconds())
}

func TestKVS(t *testing.T) {
	runTest(t, 5, 10)
}
