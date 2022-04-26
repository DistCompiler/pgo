package proxy_test

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"log"
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"example.org/proxy"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

const numRequests = 10
const testTimeout = 20 * time.Second

func TestNUM_NODES(t *testing.T) {
	ctx := distsys.NewMPCalContextWithoutArchetype(
		distsys.DefineConstantValue("NUM_SERVERS", tla.MakeTLANumber(2)),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeTLANumber(3)))
	res := proxy.NUM_NODES(ctx.IFace())
	if res.AsNumber() != 6 {
		t.Fatalf("wrong NUM_NODES results, expected 6, got %v", res)
	}
}

type mailboxMaker func(fn resources.MailboxesAddressMappingFn) distsys.ArchetypeResourceMaker

func getNetworkMaker(self tla.TLAValue, constantsIFace distsys.ArchetypeInterface, maker mailboxMaker) distsys.ArchetypeResourceMaker {
	return maker(
		func(idx tla.TLAValue) (resources.MailboxKind, string) {
			aid := idx.AsTuple().Get(0).(tla.TLAValue).AsNumber()
			msgType := idx.AsTuple().Get(1).(tla.TLAValue).AsNumber()
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
		distsys.DefineConstantValue("NUM_SERVERS", tla.MakeTLANumber(numServers)),
		distsys.DefineConstantValue("NUM_CLIENTS", tla.MakeTLANumber(numClients)),
		distsys.DefineConstantValue("EXPLORE_FAIL", tla.TLA_FALSE),
		distsys.DefineConstantValue("CLIENT_RUN", tla.TLA_TRUE),
	}

	var result []distsys.MPCalContextConfigFn
	result = append(result, constantConfigs...)
	result = append(result, configFns...)
	return result
}

var constantsIFace = distsys.NewMPCalContextWithoutArchetype(withConstantConfigs()...).IFace()

func getServerCtx(self tla.TLAValue, maker mailboxMaker, traceRecorder trace.Recorder) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AServer, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constantsIFace, maker)),
		distsys.EnsureArchetypeRefParam("fd", resources.PlaceHolderResourceMaker()),
		distsys.EnsureArchetypeRefParam("netEnabled", resources.PlaceHolderResourceMaker()),
		distsys.SetTraceRecorder(traceRecorder))...)
	return ctx
}

func getClientCtx(self tla.TLAValue, inChan chan tla.TLAValue, outChan chan tla.TLAValue, maker mailboxMaker, traceRecorder trace.Recorder) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AClient, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constantsIFace, maker)),
		distsys.EnsureArchetypeRefParam("input", resources.InputChannelMaker(inChan)),
		distsys.EnsureArchetypeRefParam("output", resources.OutputChannelMaker(outChan)),
		distsys.SetTraceRecorder(traceRecorder))...)
	return ctx
}

func getProxyCtx(self tla.TLAValue, maker mailboxMaker, traceRecorder trace.Recorder) *distsys.MPCalContext {
	ctx := distsys.NewMPCalContext(self, proxy.AProxy, withConstantConfigs(
		distsys.EnsureArchetypeRefParam("net", getNetworkMaker(self, constantsIFace, maker)),
		distsys.EnsureArchetypeRefParam("fd", resources.FailureDetectorMaker(
			func(idx tla.TLAValue) string {
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
	tests := map[string]mailboxMaker{
		"TCPMailboxes":     resources.TCPMailboxesMaker,
		"RelaxedMailboxes": resources.RelaxedMailboxesMaker,
	}

	for testName, maker := range tests {
		t.Run(testName, func(t *testing.T) {
			traceRecorder := trace.MakeLocalFileRecorder("proxy_all_servers_running_" + testName + ".txt")
			inChan := make(chan tla.TLAValue, numRequests)
			outChan := make(chan tla.TLAValue, numRequests)
			mon := setupMonitor()
			errs := make(chan error)

			var ctxs []*distsys.MPCalContext
			for i := 1; i <= numServers; i++ {
				serverCtx := getServerCtx(tla.MakeTLANumber(int32(i)), maker, traceRecorder)
				ctxs = append(ctxs, serverCtx)
				go func() {
					errs <- mon.RunArchetype(serverCtx)
				}()
			}
			proxyCtx := getProxyCtx(tla.MakeTLANumber(4), maker, traceRecorder)
			ctxs = append(ctxs, proxyCtx)
			go func() {
				errs <- proxyCtx.Run()
			}()
			clientCtx := getClientCtx(tla.MakeTLANumber(3), inChan, outChan, maker, traceRecorder)
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
				inChan <- tla.MakeTLANumber(int32(i))
			}
			for i := 0; i < numRequests; i++ {
				select {
				case resp := <-outChan:
					t.Log(resp)
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
		})
	}
}

func TestProxy_SecondServerRunning(t *testing.T) {
	tests := map[string]mailboxMaker{
		"TCPMailboxes":     resources.TCPMailboxesMaker,
		"RelaxedMailboxes": resources.RelaxedMailboxesMaker,
	}

	for testName, maker := range tests {
		t.Run(testName, func(t *testing.T) {
			traceRecorder := trace.MakeLocalFileRecorder("proxy_second_server_running_" + testName + ".txt")
			inChan := make(chan tla.TLAValue, numRequests)
			outChan := make(chan tla.TLAValue, numRequests)
			mon := setupMonitor()
			errs := make(chan error)

			var ctxs []*distsys.MPCalContext
			secondServerCtx := getServerCtx(tla.MakeTLANumber(2), maker, traceRecorder)
			ctxs = append(ctxs, secondServerCtx)
			go func() {
				errs <- mon.RunArchetype(secondServerCtx)
			}()
			proxyCtx := getProxyCtx(tla.MakeTLANumber(4), maker, traceRecorder)
			ctxs = append(ctxs, proxyCtx)
			go func() {
				errs <- proxyCtx.Run()
			}()
			clientCtx := getClientCtx(tla.MakeTLANumber(3), inChan, outChan, maker, traceRecorder)
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
				inChan <- tla.MakeTLANumber(int32(i))
			}
			for i := 0; i < numRequests; i++ {
				select {
				case resp := <-outChan:
					t.Log(resp)
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
		})
	}
}

func TestProxy_NoServerRunning(t *testing.T) {
	tests := map[string]mailboxMaker{
		"TCPMailboxes":     resources.TCPMailboxesMaker,
		"RelaxedMailboxes": resources.RelaxedMailboxesMaker,
	}

	for testName, maker := range tests {
		t.Run(testName, func(t *testing.T) {
			traceRecorder := trace.MakeLocalFileRecorder("proxy_no_server_running_" + testName + ".txt")
			inChan := make(chan tla.TLAValue, numRequests)
			outChan := make(chan tla.TLAValue, numRequests)
			mon := setupMonitor()
			errs := make(chan error)

			var ctxs []*distsys.MPCalContext
			proxyCtx := getProxyCtx(tla.MakeTLANumber(4), maker, traceRecorder)
			ctxs = append(ctxs, proxyCtx)
			go func() {
				errs <- proxyCtx.Run()
			}()
			clientCtx := getClientCtx(tla.MakeTLANumber(3), inChan, outChan, maker, traceRecorder)
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
				inChan <- tla.MakeTLANumber(int32(i))
			}
			for i := 0; i < numRequests; i++ {
				select {
				case resp := <-outChan:
					t.Log(resp)
					val, ok := resp.AsFunction().Get(tla.MakeTLAString("body"))
					if !ok {
						t.Fatalf("response body not found")
					}
					if !val.(tla.TLAValue).Equal(proxy.FAIL(constantsIFace)) {
						t.Fatalf("wrong response body, got %v, expected %v", val.(tla.TLAValue), proxy.FAIL(constantsIFace))
					}
				case <-time.After(testTimeout):
					t.Fatal("timeout")
				}
			}
		})
	}
}

func TestProxy_FirstServerCrashing(t *testing.T) {
	tests := map[string]mailboxMaker{
		"TCPMailboxes":     resources.TCPMailboxesMaker,
		"RelaxedMailboxes": resources.RelaxedMailboxesMaker,
	}

	for testName, maker := range tests {
		t.Run(testName, func(t *testing.T) {
			traceRecorder := trace.MakeLocalFileRecorder("proxy_first_server_crashing_" + testName + ".txt")
			inChan := make(chan tla.TLAValue, numRequests)
			outChan := make(chan tla.TLAValue, numRequests)
			mon := setupMonitor()
			errs := make(chan error)

			var ctxs []*distsys.MPCalContext
			for i := 1; i <= numServers; i++ {
				serverCtx := getServerCtx(tla.MakeTLANumber(int32(i)), maker, traceRecorder)
				ctxs = append(ctxs, serverCtx)
				go func() {
					errs <- mon.RunArchetype(serverCtx)
				}()
			}
			proxyCtx := getProxyCtx(tla.MakeTLANumber(4), maker, traceRecorder)
			ctxs = append(ctxs, proxyCtx)
			go func() {
				errs <- proxyCtx.Run()
			}()
			clientCtx := getClientCtx(tla.MakeTLANumber(3), inChan, outChan, maker, traceRecorder)
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
				inChan <- tla.MakeTLANumber(int32(i))
			}
			for i := 0; i < numRequests; i++ {
				select {
				case resp := <-outChan:
					t.Log(resp)
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

			ctxs[0].Stop()

			for i := 0; i < numRequests; i++ {
				inChan <- tla.MakeTLANumber(int32(i))
			}
			for i := 0; i < numRequests; i++ {
				select {
				case resp := <-outChan:
					t.Log(resp)
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
		})
	}
}
