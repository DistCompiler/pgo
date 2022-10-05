package pbkvs_test

import (
	"fmt"
	"log"
	"os"
	"testing"
	"time"

	"github.com/DistCompiler/pgo/systems/pbkvs"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

const testTimeout = 20 * time.Second

func newNetwork(self tla.TLAValue, constIFace distsys.ArchetypeInterface) *resources.Mailboxes {
	return resources.NewRelaxedMailboxes(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			aid := idx.AsTuple().Get(0).(tla.TLAValue).AsNumber()
			msgType := idx.AsTuple().Get(1).(tla.TLAValue).AsNumber()
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			msgTypeSize := pbkvs.MSG_INDEX_SET(constIFace).AsSet().Len()
			portNum := 8000 + (aid-1)*int32(msgTypeSize) + (msgType - 1)
			addr := fmt.Sprintf("localhost:%d", portNum)

			log.Println(self, aid, kind, addr)
			return kind, addr
		},
	)
}

const monAddr = "localhost:9000"

func getReplicaFSCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	var constIFace = distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	network := newNetwork(self, constIFace)
	networkLen := resources.NewMailboxesLength(network)
	ctx := distsys.NewMPCalContext(self, pbkvs.AReplica, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fs", resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
			if !index.Equal(self) {
				panic("wrong index")
			}
			return resources.NewFileSystem(fmt.Sprintf("data/%v", self))
		})),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(time.Millisecond*200),
			resources.WithFailureDetectorTimeout(time.Millisecond*500),
		)),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.NewPlaceHolder()),
		distsys.EnsureArchetypeRefParam("primary", pbkvs.NewLeaderElection()),
		distsys.EnsureArchetypeRefParam("netLen", networkLen),
	)...)
	return ctx
}

func getReplicaMapCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	var constIFace = distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	network := newNetwork(self, constIFace)
	networkLen := resources.NewMailboxesLength(network)
	ctx := distsys.NewMPCalContext(self, pbkvs.AReplica, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fs", resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
			if !index.Equal(self) {
				panic("wrong index")
			}
			return resources.NewIncMap(func(index tla.TLAValue) distsys.ArchetypeResource {
				return distsys.NewLocalArchetypeResource(tla.MakeTLAString(""))
			})
		})),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(time.Millisecond*200),
			resources.WithFailureDetectorTimeout(time.Millisecond*500),
		)),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.NewPlaceHolder()),
		distsys.EnsureArchetypeRefParam("primary", pbkvs.NewLeaderElection()),
		distsys.EnsureArchetypeRefParam("netLen", networkLen),
	)...)
	return ctx
}

func getPutClientCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn,
	inChan <-chan tla.TLAValue, outChan chan<- tla.TLAValue) *distsys.MPCalContext {
	var constIFace = distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	network := newNetwork(self, constIFace)
	networkLen := resources.NewMailboxesLength(network)

	ctx := distsys.NewMPCalContext(self, pbkvs.APutClient, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(time.Millisecond*200),
			resources.WithFailureDetectorTimeout(time.Millisecond*500),
		)),
		distsys.EnsureArchetypeRefParam("primary", pbkvs.NewLeaderElection()),
		distsys.EnsureArchetypeRefParam("netLen", networkLen),
		distsys.EnsureArchetypeRefParam("input", resources.NewInputChan(inChan)),
		distsys.EnsureArchetypeRefParam("output", resources.NewOutputChan(outChan)),
	)...)
	return ctx
}

func getGetClientCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn,
	inChan <-chan tla.TLAValue, outChan chan<- tla.TLAValue) *distsys.MPCalContext {
	var constIFace = distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	network := newNetwork(self, constIFace)
	networkLen := resources.NewMailboxesLength(network)

	ctx := distsys.NewMPCalContext(self, pbkvs.AGetClient, append(constants,
		distsys.EnsureArchetypeRefParam("net", network),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(time.Millisecond*200),
			resources.WithFailureDetectorTimeout(time.Millisecond*500),
		)),
		distsys.EnsureArchetypeRefParam("primary", pbkvs.NewLeaderElection()),
		distsys.EnsureArchetypeRefParam("netLen", networkLen),
		distsys.EnsureArchetypeRefParam("input", resources.NewInputChan(inChan)),
		distsys.EnsureArchetypeRefParam("output", resources.NewOutputChan(outChan)),
	)...)
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

func TestPBKVS_OneReplicaOnePutOneGet(t *testing.T) {
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_REPLICAS", tla.MakeTLANumber(1)),
		distsys.DefineConstantValue("NUM_PUT_CLIENT", tla.MakeTLANumber(1)),
		distsys.DefineConstantValue("NUM_GET_CLIENTS", tla.MakeTLANumber(1)),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.TLA_FALSE),
		distsys.DefineConstantValue("PUT_CLIENT_RUN", tla.TLA_TRUE),
		distsys.DefineConstantValue("GET_CLIENT_RUN", tla.TLA_TRUE),
	}
	mon := setupMonitor()
	errs := make(chan error)
	putInput := make(chan tla.TLAValue)
	putOutput := make(chan tla.TLAValue)
	getInput := make(chan tla.TLAValue)
	getOutput := make(chan tla.TLAValue)

	err := os.MkdirAll("data/1/", 0700)
	if err != nil {
		t.Fatal(err)
	}

	var ctxs []*distsys.MPCalContext
	replicaCtx := getReplicaFSCtx(tla.MakeTLANumber(1), constants)
	ctxs = append(ctxs, replicaCtx)
	go func() {
		errs <- mon.RunArchetype(replicaCtx)
	}()

	putCtx := getPutClientCtx(tla.MakeTLANumber(2), constants, putInput, putOutput)
	ctxs = append(ctxs, putCtx)
	go func() {
		errs <- putCtx.Run()
	}()

	getCtx := getGetClientCtx(tla.MakeTLANumber(3), constants, getInput, getOutput)
	ctxs = append(ctxs, getCtx)
	go func() {
		errs <- getCtx.Run()
	}()
	defer func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		for i := 0; i < len(ctxs); i++ {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %s", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}

		if err := os.RemoveAll("data/"); err != nil {
			log.Println(err)
		}
	}()

	iface := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	key1 := pbkvs.KEY1(iface)
	val1 := pbkvs.VALUE1(iface)

	putInput <- tla.MakeTLARecord([]tla.TLARecordField{
		{Key: tla.MakeTLAString("key"), Value: key1},
		{Key: tla.MakeTLAString("value"), Value: val1},
	})
	select {
	case <-putOutput:
	case <-time.After(testTimeout):
		t.Fatal("timeout")
	}

	getInput <- tla.MakeTLARecord([]tla.TLARecordField{
		{Key: tla.MakeTLAString("key"), Value: key1},
	})
	select {
	case resp := <-getOutput:
		body, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
		if !ok {
			t.Fatal("response body not found")
		}
		val, ok := body.(tla.TLAValue).AsFunction().Get(tla.MakeTLAString("content"))
		if !ok {
			t.Fatal("response body content not found")
		}
		if !val.(tla.TLAValue).Equal(val1) {
			t.Fatalf("wrong response value, got %v, expected %v", val, val1)
		}
	case <-time.After(testTimeout):
		t.Fatal("timeout")
	}
}

func TestPBKVS_ThreeReplicasConcurrentPut(t *testing.T) {
	numReplicas := 3
	numPutClients := 3
	numReqs := 15
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_REPLICAS", tla.MakeTLANumber(int32(numReplicas))),
		distsys.DefineConstantValue("NUM_PUT_CLIENT", tla.MakeTLANumber(int32(numPutClients))),
		distsys.DefineConstantValue("NUM_GET_CLIENTS", tla.MakeTLANumber(0)),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.TLA_FALSE),
		distsys.DefineConstantValue("PUT_CLIENT_RUN", tla.TLA_TRUE),
		distsys.DefineConstantValue("GET_CLIENT_RUN", tla.TLA_FALSE),
	}
	mon := setupMonitor()
	errs := make(chan error)
	putInput := make(chan tla.TLAValue, numReqs)
	putOutput := make(chan tla.TLAValue, numReqs)

	var replicaCtxs []*distsys.MPCalContext
	for i := 1; i <= numReplicas; i++ {
		ctx := getReplicaMapCtx(tla.MakeTLANumber(int32(i)), constants)
		replicaCtxs = append(replicaCtxs, ctx)
		go func() {
			errs <- mon.RunArchetype(ctx)
		}()
	}
	var putCtxs []*distsys.MPCalContext
	for i := 1; i <= numPutClients; i++ {
		ctx := getPutClientCtx(tla.MakeTLANumber(int32(i+numReplicas)), constants, putInput, putOutput)
		putCtxs = append(putCtxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}
	ctxs := append(replicaCtxs, putCtxs...)
	cleanup := func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		for i := 0; i < len(ctxs); i++ {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %s", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}
	}

	key := tla.MakeTLAString("KEY1")
	for i := 0; i < numReqs; i++ {
		val := tla.MakeTLAString(fmt.Sprintf("VALUE%d", i%3))
		putInput <- tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("key"), Value: key},
			{Key: tla.MakeTLAString("value"), Value: val},
		})
	}
	for i := 0; i < numReqs; i++ {
		select {
		case <-putOutput:
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}

	cleanup()

	getVal := func(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
		fs, err := ctx.IFace().RequireArchetypeResourceRef("AReplica.fs")
		if err != nil {
			return tla.TLAValue{}, err
		}
		return ctx.IFace().Read(fs, []tla.TLAValue{ctx.IFace().Self(), key})
	}

	primaryVal, err := getVal(replicaCtxs[0])
	if err != nil {
		t.Fatalf("cannot read value from fs")
	}
	for _, ctx := range replicaCtxs {
		replicaVal, err := getVal(ctx)
		if err != nil {
			t.Fatalf("cannot read value from fs")
		}
		if !primaryVal.Equal(replicaVal) {
			t.Fatalf("expected values %v and %v to be equal", primaryVal, replicaVal)
		}
	}
}

func TestPBKVS_ThreeReplicasOneCrashConcurrentPut(t *testing.T) {
	numReplicas := 3
	numPutClients := 3
	numReqs := 15
	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_REPLICAS", tla.MakeTLANumber(int32(numReplicas))),
		distsys.DefineConstantValue("NUM_PUT_CLIENT", tla.MakeTLANumber(int32(numPutClients))),
		distsys.DefineConstantValue("NUM_GET_CLIENTS", tla.MakeTLANumber(0)),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.TLA_FALSE),
		distsys.DefineConstantValue("PUT_CLIENT_RUN", tla.TLA_TRUE),
		distsys.DefineConstantValue("GET_CLIENT_RUN", tla.TLA_FALSE),
	}
	mon := setupMonitor()
	errs := make(chan error)
	putInput := make(chan tla.TLAValue, numReqs)
	putOutput := make(chan tla.TLAValue, numReqs)

	var replicaCtxs []*distsys.MPCalContext
	for i := 1; i <= numReplicas; i++ {
		ctx := getReplicaMapCtx(tla.MakeTLANumber(int32(i)), constants)
		replicaCtxs = append(replicaCtxs, ctx)
		go func() {
			errs <- mon.RunArchetype(ctx)
		}()
	}
	var putCtxs []*distsys.MPCalContext
	for i := 1; i <= numPutClients; i++ {
		ctx := getPutClientCtx(tla.MakeTLANumber(int32(i+numReplicas)), constants, putInput, putOutput)
		putCtxs = append(putCtxs, ctx)
		go func() {
			errs <- ctx.Run()
		}()
	}
	ctxs := append(replicaCtxs, putCtxs...)
	cleanup := func() {
		for _, ctx := range ctxs {
			ctx.Stop()
		}
		for i := 0; i < len(ctxs); i++ {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %s", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}
	}

	key := tla.MakeTLAString("KEY1")
	for i := 0; i < numReqs; i++ {
		val := tla.MakeTLAString(fmt.Sprintf("VALUE%d", i%3))
		putInput <- tla.MakeTLARecord([]tla.TLARecordField{
			{Key: tla.MakeTLAString("key"), Value: key},
			{Key: tla.MakeTLAString("value"), Value: val},
		})
	}

	replicaCtxs[1].Stop()

	for i := 0; i < numReqs; i++ {
		select {
		case <-putOutput:
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}

	cleanup()

	getVal := func(ctx *distsys.MPCalContext) (tla.TLAValue, error) {
		fs, err := ctx.IFace().RequireArchetypeResourceRef("AReplica.fs")
		if err != nil {
			return tla.TLAValue{}, err
		}
		return ctx.IFace().Read(fs, []tla.TLAValue{ctx.IFace().Self(), key})
	}

	primaryVal, err := getVal(replicaCtxs[0])
	if err != nil {
		t.Fatalf("cannot read value from fs")
	}
	for i, ctx := range replicaCtxs {
		if i == 1 { // index of the crashing server
			continue
		}
		replicaVal, err := getVal(ctx)
		if err != nil {
			t.Fatalf("cannot read value from fs")
		}
		if !primaryVal.Equal(replicaVal) {
			t.Fatalf("expected values %v and %v to be equal", primaryVal, replicaVal)
		}
	}
}