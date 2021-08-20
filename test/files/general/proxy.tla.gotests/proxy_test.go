package proxy_test

import (
	"fmt"
	"log"
	"testing"
	"time"

	"example.org/proxy"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/resources"
)

const numRequests = 10
const testTimeout = 2 * time.Second

func TestNUM_NODES(t *testing.T) {
	res := proxy.NUM_NODES(
		proxy.Constants{
			NUM_SERVERS: distsys.NewTLANumber(2),
			NUM_CLIENTS: distsys.NewTLANumber(3),
		},
	)
	if res.AsNumber() != 6 {
		t.Fatalf("wrong NUM_NODES results, expected 6, got %v", res)
	}
}

func getNetworkMaker(self distsys.TLAValue, constants proxy.Constants) distsys.ArchetypeResourceMaker {
	return resources.TCPMailboxesArchetypeResourceMaker(
		func(idx distsys.TLAValue) (resources.TCPMailboxKind, string) {
			aid := idx.AsTuple().Get(0).(distsys.TLAValue).AsNumber()
			msgType := idx.AsTuple().Get(1).(distsys.TLAValue).AsNumber()
			kind := resources.TCPMailboxesRemote
			if aid == self.AsNumber() {
				kind = resources.TCPMailboxesLocal
			}
			msgTypeSize := proxy.MSG_TYP_SET(constants).AsSet().Len()
			portNum := 8000 + (aid-1)*int32(msgTypeSize) + (msgType - 1)
			addr := fmt.Sprintf("localhost:%d", portNum)
			return kind, addr
		},
	)
}

func runArchetype(done <-chan struct{}, ctx *distsys.MPCalContext, fn func() error) error {
	errCh := make(chan error)
	go func() {
		errCh <- fn()
	}()
	var err error
	select {
	case <-done:
		cerr := ctx.Close()
		if cerr != nil {
			log.Println(cerr)
		}
		err = <-errCh
	case err = <-errCh:
		cerr := ctx.Close()
		if cerr != nil {
			log.Println(cerr)
		}
	}
	if err == distsys.ErrContextClosed {
		return nil
	}
	return err
}

const monAddr = "localhost:9000"

func runServer(done <-chan struct{}, self distsys.TLAValue, constants proxy.Constants, mon *resources.Monitor) error {
	ctx := distsys.NewMPCalContext()
	networkMaker := getNetworkMaker(self, constants)
	network := ctx.EnsureArchetypeResourceByName("network", networkMaker)
	placeHolderMaker := resources.PlaceHolderResourceMaker()
	placeHolder := ctx.EnsureArchetypeResourceByName("placeHolder", placeHolderMaker)
	return runArchetype(done, ctx, func() error {
		return mon.RunArchetype(self, func() error {
			return proxy.AServer(ctx, self, constants, network, placeHolder, placeHolder)
		})
	})
}

func runClient(done <-chan struct{}, self distsys.TLAValue, constants proxy.Constants, outputChannel chan distsys.TLAValue) error {
	ctx := distsys.NewMPCalContext()
	networkMaker := getNetworkMaker(self, constants)
	network := ctx.EnsureArchetypeResourceByName("network", networkMaker)
	outputMaker := resources.OutputChannelResourceMaker(outputChannel)
	output := ctx.EnsureArchetypeResourceByName("output", outputMaker)
	return runArchetype(done, ctx, func() error {
		return proxy.AClient(ctx, self, constants, network, output)
	})
}

func runProxy(done <-chan struct{}, self distsys.TLAValue, constants proxy.Constants) error {
	ctx := distsys.NewMPCalContext()
	networkMaker := getNetworkMaker(self, constants)
	network := ctx.EnsureArchetypeResourceByName("network", networkMaker)
	fdMaker := resources.FailureDetectorResourceMaker(
		func(idx distsys.TLAValue) string {
			return monAddr
		},
		resources.WithFailureDetectorPullInterval(time.Millisecond*500),
		resources.WithFailureDetectorTimeout(time.Second*3000),
	)
	fd := ctx.EnsureArchetypeResourceByName("fd", fdMaker)
	return runArchetype(done, ctx, func() error {
		return proxy.AProxy(ctx, self, constants, network, fd)
	})
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

var constants = proxy.Constants{
	NUM_SERVERS:  distsys.NewTLANumber(2),
	NUM_CLIENTS:  distsys.NewTLANumber(1),
	EXPLORE_FAIL: distsys.NewTLABool(false),
}

func TestProxy_AllServersRunning(t *testing.T) {
	const numRunningArchetypes = 4

	outputChannel := make(chan distsys.TLAValue)
	mon := setupMonitor()
	done := make(chan struct{})
	errs := make(chan error)
	go func() {
		errs <- runServer(done, distsys.NewTLANumber(1), constants, mon)
	}()
	go func() {
		errs <- runServer(done, distsys.NewTLANumber(2), constants, mon)
	}()
	go func() {
		errs <- runProxy(done, distsys.NewTLANumber(4), constants)
	}()
	go func() {
		errs <- runClient(done, distsys.NewTLANumber(3), constants, outputChannel)
	}()
	defer func() {
		for i := 0; i < numRunningArchetypes; i++ {
			done <- struct{}{}
		}
		for i := 0; i < numRunningArchetypes; i++ {
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
			val, ok := resp.AsFunction().Get(distsys.NewTLAString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(distsys.TLAValue).Equal(distsys.NewTLANumber(1)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(distsys.TLAValue), distsys.NewTLANumber(1))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_SecondServerRunning(t *testing.T) {
	const numRunningArchetypes = 3

	outputChannel := make(chan distsys.TLAValue)
	mon := setupMonitor()
	done := make(chan struct{})
	errs := make(chan error)
	go func() {
		errs <- runServer(done, distsys.NewTLANumber(2), constants, mon)
	}()
	go func() {
		errs <- runProxy(done, distsys.NewTLANumber(4), constants)
	}()
	go func() {
		errs <- runClient(done, distsys.NewTLANumber(3), constants, outputChannel)
	}()
	defer func() {
		for i := 0; i < numRunningArchetypes; i++ {
			done <- struct{}{}
		}
		for i := 0; i < numRunningArchetypes; i++ {
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
			val, ok := resp.AsFunction().Get(distsys.NewTLAString("body"))
			if !ok {
				t.Fatalf("response body not found")
			}
			if !val.(distsys.TLAValue).Equal(distsys.NewTLANumber(2)) {
				t.Fatalf("wrong response body, got %v, expected %v", val.(distsys.TLAValue), distsys.NewTLANumber(2))
			}
		case <-time.After(testTimeout):
			t.Fatal("timeout")
		}
	}
}

func TestProxy_NoServerRunning(t *testing.T) {
	const numRunningArchetypes = 2

	outputChannel := make(chan distsys.TLAValue)
	mon := setupMonitor()
	done := make(chan struct{})
	errs := make(chan error)
	go func() {
		errs <- runProxy(done, distsys.NewTLANumber(4), constants)
	}()
	go func() {
		errs <- runClient(done, distsys.NewTLANumber(3), constants, outputChannel)
	}()
	defer func() {
		for i := 0; i < numRunningArchetypes; i++ {
			done <- struct{}{}
		}
		for i := 0; i < numRunningArchetypes; i++ {
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
		val, ok := resp.AsFunction().Get(distsys.NewTLAString("body"))
		if !ok {
			t.Fatalf("response body not found")
		}
		if !val.(distsys.TLAValue).Equal(proxy.FAIL(constants)) {
			t.Fatalf("wrong response body, got %v, expected %v", val.(distsys.TLAValue), proxy.FAIL(constants))
		}
	}
}
