package proxy_test

import (
	"fmt"
	"log"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"example.org/proxy"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

const numRequests = 10
const testTimeout = 2 * time.Second

func TestNUM_NODES(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype(
		distsys.DefineConstantValue("NUM_SERVERS", tla.MakeTLANumber(2)),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeTLANumber(3)))
	res := proxy.NUM_NODES(ctx.IFace())
	if res.AsNumber() != 6 {
		t.Fatalf("wrong NUM_NODES results, expected 6, got %v", res)
	}
}

func getNetworkMaker(self tla.TLAValue, constantsIFace distsys.ArchetypeInterface) distsys.ArchetypeResourceMaker {
	return resources.TCPMailboxesMaker(
		func(idx tla.TLAValue) (resources.TCPMailboxKind, string) {
			aid := idx.AsTuple().Get(0).(tla.TLAValue).AsNumber()
			msgType := idx.AsTuple().Get(1).(tla.TLAValue).AsNumber()
			kind := resources.TCPMailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.TCPMailboxesLocal
			}
			msgTypeSize := proxy.MSG_TYP_SET(constantsIFace).AsSet().Len()
			portNum := 8000 + (aid-1)*int32(msgTypeSize) + (msgType - 1)
			addr := fmt.Sprintf("localhost:%d", portNum)
			return kind, addr
		},
	)
}

func runArchetype(fn func() error) error {
	err := fn()
	if err == distsys.ErrContextClosed {
		return nil
	}
	return err
}

const monAddr = "localhost:9000"

func genClientRun() func() tla.TLAValue {
	cnt := 0
	return func() tla.TLAValue {
		res := tla.TLA_FALSE
		if cnt < numRequests {
			res = tla.TLA_TRUE
		}
		cnt++
		return res
	}
}

const numServers = 2
const numClients = 1

func withConstantConfigs(configFns ...distsys.MPCalContextConfigFn) []distsys.MPCalContextConfigFn {
	var constantConfigs = []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_SERVERS", tla.MakeTLANumber(numServers)),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeTLANumber(numClients)),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.TLA_FALSE),
		distsys.DefineConstantOperator("CLIENT_RUN", genClientRun()),
	}

	var result []distsys.MPCalContextConfigFn
	result = append(result, constantConfigs...)
	result = append(result, configFns...)
	return result
}

var constantsIFace = distsys.NewMPCalContextWithoutArchetype(withConstantConfigs()...).IFace()

func getServerCtx(self tla.TLAValue) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AServer, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constantsIFace)),
		distsys.EnsureArchetypeRefParam("fd", resources.PlaceHolderResourceMaker()),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.PlaceHolderResourceMaker()))...)
	return ctx
}

func getClientCtx(self tla.TLAValue, outputChannel chan tla.TLAValue) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AClient, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constantsIFace)),
		distsys.EnsureArchetypeRefParam("output", resources.OutputChannelMaker(outputChannel)))...)
	return ctx
}

func getProxyCtx(self tla.TLAValue) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AProxy, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constantsIFace)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(idx tla.TLAValue) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(time.Millisecond*500),
			resources.WithFailureDetectorTimeout(time.Second*3000),
		)))...)
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

func TestProxy_AllServersRunning(t *testing.T) {
	outputChannel := make(chan tla.TLAValue)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		serverCtx := getServerCtx(tla.MakeTLANumber(int32(i)))
		ctxs = append(ctxs, serverCtx)
		go func() {
			errs <- runArchetype(func() error {
				return mon.RunArchetype(serverCtx)
			})
		}()
	}
	proxyCtx := getProxyCtx(tla.MakeTLANumber(4))
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- runArchetype(proxyCtx.Run)
	}()
	clientCtx := getClientCtx(tla.MakeTLANumber(3), outputChannel)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- runArchetype(clientCtx.Run)
	}()
	defer func() {
		for _, ctx := range ctxs {
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
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
	}()

	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outputChannel:
			val, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.TLAValue).Equal(tla.MakeTLANumber(1)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.TLAValue), tla.MakeTLANumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_SecondServerRunning(t *testing.T) {
	outputChannel := make(chan tla.TLAValue)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	secondServerCtx := getServerCtx(tla.MakeTLANumber(2))
	ctxs = append(ctxs, secondServerCtx)
	go func() {
		errs <- runArchetype(func() error {
			return mon.RunArchetype(secondServerCtx)
		})
	}()
	proxyCtx := getProxyCtx(tla.MakeTLANumber(4))
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- runArchetype(proxyCtx.Run)
	}()
	clientCtx := getClientCtx(tla.MakeTLANumber(3), outputChannel)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- runArchetype(clientCtx.Run)
	}()
	defer func() {
		for _, ctx := range ctxs {
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
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
	}()

	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outputChannel:
			val, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.TLAValue).Equal(tla.MakeTLANumber(2)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.TLAValue), tla.MakeTLANumber(2))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_NoServerRunning(t *testing.T) {
	outputChannel := make(chan tla.TLAValue)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	proxyCtx := getProxyCtx(tla.MakeTLANumber(4))
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- runArchetype(proxyCtx.Run)
	}()
	clientCtx := getClientCtx(tla.MakeTLANumber(3), outputChannel)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- runArchetype(clientCtx.Run)
	}()
	defer func() {
		for _, ctx := range ctxs {
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
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
	}()

	for i := 0; i < numRequests; i++ {
		resp := <-outputChannel
		val, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
		if !ok {
			t.Fatalf("response body not found")
		}
		if !val.(tla.TLAValue).Equal(proxy.FAIL(constantsIFace)) {
			t.Fatalf("wrong response body, got %v, expected %v", val.(tla.TLAValue), proxy.FAIL(constantsIFace))
		}
	}
}

func TestProxy_FirstServerCrashing(t *testing.T) {
	outputChannel := make(chan tla.TLAValue)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		serverCtx := getServerCtx(tla.MakeTLANumber(int32(i)))
		ctxs = append(ctxs, serverCtx)
		go func() {
			errs <- runArchetype(func() error {
				return mon.RunArchetype(serverCtx)
			})
		}()
	}
	proxyCtx := getProxyCtx(tla.MakeTLANumber(4))
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- runArchetype(proxyCtx.Run)
	}()
	clientCtx := getClientCtx(tla.MakeTLANumber(3), outputChannel)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- runArchetype(clientCtx.Run)
	}()
	defer func() {
		for _, ctx := range ctxs {
			if err := ctx.Close(); err != nil {
				log.Println(err)
			}
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
	}()

	for i := 0; i < numRequests/2; i++ {
		select {
		case resp := <-outputChannel:
			val, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.TLAValue).Equal(tla.MakeTLANumber(1)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.TLAValue), tla.MakeTLANumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}

	if err := ctxs[0].Close(); err != nil {
		log.Printf("error in closing first server context: %s", err)
	}

	for i := 0; i < numRequests/2; i++ {
		select {
		case resp := <-outputChannel:
			val, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.TLAValue).Equal(tla.MakeTLANumber(2)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.TLAValue), tla.MakeTLANumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}
