package raft_test

import (
	"fmt"
	"log"
	"testing"
	"time"

	"example.org/raft"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func getNetworkMaker(self tla.TLAValue, iface distsys.ArchetypeInterface) distsys.ArchetypeResourceMaker {
	return resources.TCPMailboxesMaker(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			aid := idx.AsNumber()
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			port := 8000 + aid
			addr := fmt.Sprintf("localhost:%d", port)
			return kind, addr
		},
	)
}

const monAddr = "localhost:9000"

func makeServerCtx(self tla.TLAValue, constants []distsys.MPCalContextConfigFn) *distsys.MPCalContext {
	constIFace := distsys.NewMPCalContextWithoutArchetype(constants...).IFace()
	ctx := distsys.NewMPCalContext(self, raft.AServer,
		distsys.EnsureMPCalContextConfigs(constants...),
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constIFace)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(index tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(100*time.Millisecond),
			resources.WithFailureDetectorTimeout(200*time.Millisecond),
		)),
		distsys.EnsureArchetypeDerivedRefParam("netLen", "net", resources.MailboxesLengthMaker),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.PlaceHolderResourceMaker()),
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

func TestLeaderElection_ThreeServers(t *testing.T) {
	numServers := 3

	constants := []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NumServers", tla.MakeTLANumber(3)),
		distsys.DefineConstantValue("NumClients", tla.MakeTLANumber(0)),
		distsys.DefineConstantValue("ExploreFail", tla.TLA_FALSE),
	}
	mon := setupMonitor()
	errs := make(chan error)

	var serverCtxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		ctx := makeServerCtx(tla.MakeTLANumber(int32(i)), constants)
		serverCtxs = append(serverCtxs, ctx)
		go func() {
			errs <- mon.RunArchetype(ctx)
		}()
	}
	cleanup := func() {
		for _, ctx := range serverCtxs {
			ctx.Stop()
		}
		for i := 0; i < len(serverCtxs); i++ {
			err := <-errs
			if err != nil {
				t.Errorf("archetype error: %s", err)
			}
		}
		if err := mon.Close(); err != nil {
			log.Println(err)
		}
	}

	time.Sleep(10 * time.Second)

	log.Println("10 sec passed")

	cleanup()

	log.Println("cleanup done")

	getVar := func(ctx *distsys.MPCalContext, varName string) (tla.TLAValue, error) {
		name := fmt.Sprintf("AServer.%s", varName)
		varHandle := ctx.IFace().RequireArchetypeResource(name)
		return ctx.IFace().Read(varHandle, nil)
	}

	for _, ctx := range serverCtxs {
		state, _ := getVar(ctx, "state")
		currentTerm, _ := getVar(ctx, "currentTerm")
		votesResponded, _ := getVar(ctx, "votesResponded")
		votesGranted, _ := getVar(ctx, "votesGranted")
		log.Println(state, currentTerm, votesResponded, votesGranted)
	}
}
