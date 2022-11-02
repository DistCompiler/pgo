package proxy_test

import (
	"fmt"
	"log"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/DistCompiler/pgo/systems/proxy"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

const numRequests = 10
const testTimeout = 20 * time.Second

func TestNUM_NODES(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype(
		distsys.DefineConstantValue("NUM_SERVERS", tla.MakeNumber(2)),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeNumber(3)))
	res := proxy.NUM_NODES(ctx.IFace())
	if res.AsNumber() != 6 {
		t.Fatalf("wrong NUM_NODES results, expected 6, got %v", res)
	}
}

func newNetwork(self tla.Value, constantsIFace distsys.ArchetypeInterface) *resources.Mailboxes {
	return resources.NewTCPMailboxes(
		func(idx tla.Value) (resources.MailboxKind, string) {
			aid := idx.AsTuple().Get(0).(tla.Value).AsNumber()
			msgType := idx.AsTuple().Get(1).(tla.Value).AsNumber()
			kind := resources.MailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.MailboxesLocal
			}
			msgTypeSize := proxy.MSG_TYP_SET(constantsIFace).AsSet().Len()
			portNum := 8000 + (aid-1)*int32(msgTypeSize) + (msgType - 1)
			addr := fmt.Sprintf("localhost:%d", portNum)
			return kind, addr
		},
	)
}

const monAddr = "localhost:9000"

const numServers = 2
const numClients = 1

func withConstantConfigs(configFns ...distsys.MPCalContextConfigFn) []distsys.MPCalContextConfigFn {
	var constantConfigs = []distsys.MPCalContextConfigFn{
		distsys.DefineConstantValue("NUM_SERVERS", tla.MakeNumber(numServers)),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeNumber(numClients)),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.Symbol_FALSE),
		distsys.DefineConstantValue("CLIENT_RUN", tla.Symbol_TRUE),
	}

	var result []distsys.MPCalContextConfigFn
	result = append(result, constantConfigs...)
	result = append(result, configFns...)
	return result
}

var constantsIFace = distsys.NewMPCalContextWithoutArchetype(withConstantConfigs()...).IFace()

func getServerCtx(self tla.Value, traceRecorder trace.Recorder) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AServer, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", newNetwork(self, constantsIFace)),
		distsys.EnsureArchetypeRefParam("fd", resources.NewPlaceHolder()),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.NewPlaceHolder()),
		distsys.SetTraceRecorder(traceRecorder))...)
	return ctx
}

func getClientCtx(self tla.Value, inChan chan tla.Value, outChan chan tla.Value, traceRecorder trace.Recorder) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AClient, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", newNetwork(self, constantsIFace)),
		distsys.EnsureArchetypeRefParam("input", resources.NewInputChan(inChan)),
		distsys.EnsureArchetypeRefParam("output", resources.NewOutputChan(outChan)),
		distsys.SetTraceRecorder(traceRecorder))...)
	return ctx
}

func getProxyCtx(self tla.Value, traceRecorder trace.Recorder) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AProxy, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", newNetwork(self, constantsIFace)),
		distsys.EnsureArchetypeRefParam("fd", resources.NewFailureDetector(
			func(idx tla.Value) string {
				return monAddr
			},
			resources.WithFailureDetectorPullInterval(time.Millisecond*200),
			resources.WithFailureDetectorTimeout(time.Millisecond*500),
		)),
		distsys.SetTraceRecorder(traceRecorder))...)
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
	traceRecorder := trace.MakeLocalFileRecorder("proxy_all_servers_running.txt")
	inChan := make(chan tla.Value, numRequests)
	outChan := make(chan tla.Value, numRequests)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		serverCtx := getServerCtx(tla.MakeNumber(int32(i)), traceRecorder)
		ctxs = append(ctxs, serverCtx)
		go func() {
			errs <- mon.RunArchetype(serverCtx)
		}()
	}
	proxyCtx := getProxyCtx(tla.MakeNumber(4), traceRecorder)
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- proxyCtx.Run()
	}()
	clientCtx := getClientCtx(tla.MakeNumber(3), inChan, outChan, traceRecorder)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- clientCtx.Run()
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
	}()

	for i := 0; i < numRequests; i++ {
		inChan <- tla.MakeNumber(int32(i))
	}
	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outChan:
			t.Log(resp)
			val, ok := resp.AsFunction().Get(tla.MakeString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.Value).Equal(tla.MakeNumber(1)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.Value), tla.MakeNumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_SecondServerRunning(t *testing.T) {
	traceRecorder := trace.MakeLocalFileRecorder("proxy_second_server_running.txt")
	inChan := make(chan tla.Value, numRequests)
	outChan := make(chan tla.Value, numRequests)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	secondServerCtx := getServerCtx(tla.MakeNumber(2), traceRecorder)
	ctxs = append(ctxs, secondServerCtx)
	go func() {
		errs <- mon.RunArchetype(secondServerCtx)
	}()
	proxyCtx := getProxyCtx(tla.MakeNumber(4), traceRecorder)
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- proxyCtx.Run()
	}()
	clientCtx := getClientCtx(tla.MakeNumber(3), inChan, outChan, traceRecorder)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- clientCtx.Run()
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
	}()

	for i := 0; i < numRequests; i++ {
		inChan <- tla.MakeNumber(int32(i))
	}
	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outChan:
			t.Log(resp)
			val, ok := resp.AsFunction().Get(tla.MakeString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.Value).Equal(tla.MakeNumber(2)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.Value), tla.MakeNumber(2))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_NoServerRunning(t *testing.T) {
	traceRecorder := trace.MakeLocalFileRecorder("proxy_no_server_running.txt")
	inChan := make(chan tla.Value, numRequests)
	outChan := make(chan tla.Value, numRequests)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	proxyCtx := getProxyCtx(tla.MakeNumber(4), traceRecorder)
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- proxyCtx.Run()
	}()
	clientCtx := getClientCtx(tla.MakeNumber(3), inChan, outChan, traceRecorder)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- clientCtx.Run()
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
	}()

	for i := 0; i < numRequests; i++ {
		inChan <- tla.MakeNumber(int32(i))
	}
	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outChan:
			t.Log(resp)
			val, ok := resp.AsFunction().Get(tla.MakeString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.Value).Equal(proxy.FAIL(constantsIFace)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.Value), proxy.FAIL(constantsIFace))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_FirstServerCrashing(t *testing.T) {
	traceRecorder := trace.MakeLocalFileRecorder("proxy_first_server_crashing.txt")
	inChan := make(chan tla.Value, numRequests)
	outChan := make(chan tla.Value, numRequests)
	mon := setupMonitor()
	errs := make(chan error)

	var ctxs []*distsys.MPCalContext
	for i := 1; i <= numServers; i++ {
		serverCtx := getServerCtx(tla.MakeNumber(int32(i)), traceRecorder)
		ctxs = append(ctxs, serverCtx)
		go func() {
			errs <- mon.RunArchetype(serverCtx)
		}()
	}
	proxyCtx := getProxyCtx(tla.MakeNumber(4), traceRecorder)
	ctxs = append(ctxs, proxyCtx)
	go func() {
		errs <- proxyCtx.Run()
	}()
	clientCtx := getClientCtx(tla.MakeNumber(3), inChan, outChan, traceRecorder)
	ctxs = append(ctxs, clientCtx)
	go func() {
		errs <- clientCtx.Run()
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
	}()

	for i := 0; i < numRequests; i++ {
		inChan <- tla.MakeNumber(int32(i))
	}
	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outChan:
			t.Log(resp)
			val, ok := resp.AsFunction().Get(tla.MakeString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.Value).Equal(tla.MakeNumber(1)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.Value), tla.MakeNumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}

	ctxs[0].Stop()

	for i := 0; i < numRequests; i++ {
		inChan <- tla.MakeNumber(int32(i))
	}
	for i := 0; i < numRequests; i++ {
		select {
		case resp := <-outChan:
			t.Log(resp)
			val, ok := resp.AsFunction().Get(tla.MakeString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(tla.Value).Equal(tla.MakeNumber(2)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(tla.Value), tla.MakeNumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}
