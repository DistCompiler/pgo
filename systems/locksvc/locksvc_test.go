package locksvc_test

import (
	"fmt"
	"log"
	"sync"
	"testing"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/resources"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/DistCompiler/pgo/systems/locksvc"
)

func addressFn(myIdx tla.Value) func(idx tla.Value) (resources.MailboxKind, string) {
	return func(idx tla.Value) (kind resources.MailboxKind, addr string) {
		addr = fmt.Sprintf("localhost:%d", idx.AsNumber()+8000)
		if myIdx.Equal(idx) {
			kind = resources.MailboxesLocal
		} else {
			kind = resources.MailboxesRemote
		}
		return
	}
}

func runOrPanic(ctx *distsys.MPCalContext) {
	err := (*distsys.MPCalContext)(ctx).Run()
	if err != nil {
		panic(err.Error())
	}
}

type matcherResource struct {
	distsys.ArchetypeResourceLeafMixin
	expectedValue tla.Value
	onMatch       chan struct{}
	lock          sync.Mutex
}

func (m *matcherResource) Abort(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (m *matcherResource) Close() error {
	m.lock.Lock()
	defer m.lock.Unlock()

	if m.onMatch != nil {
		panic("stopped archetype resource while matcher resource was waiting")
	}

	return nil
}

func (m *matcherResource) Commit(distsys.ArchetypeInterface) chan struct{} {
	m.lock.Lock()
	defer m.lock.Unlock()

	close(m.onMatch)
	m.onMatch = nil
	m.expectedValue = tla.Value{}
	return nil
}

func (m *matcherResource) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (m *matcherResource) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	panic("shouldn't be reading a matcher resource")
}

func (m *matcherResource) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	m.lock.Lock()
	defer m.lock.Unlock()

	if m.onMatch == nil {
		return distsys.ErrCriticalSectionAborted
	}

	if m.expectedValue.Equal(value) {
		return nil
	} else {
		return distsys.ErrCriticalSectionAborted
	}
}

func (m *matcherResource) AwaitValue(value tla.Value) chan struct{} {
	m.lock.Lock()
	defer m.lock.Unlock()

	if m.onMatch != nil {
		panic("tried to await a matcherResource that's already being awaited")
	}

	m.onMatch = make(chan struct{})
	m.expectedValue = value
	return m.onMatch
}

func whileHoldingLock(clientId tla.Value, body func()) {
	matcher := &matcherResource{}

	ctx := distsys.NewMPCalContext(clientId, locksvc.AClient,
		distsys.EnsureArchetypeRefParam("network", resources.NewRelaxedMailboxes(addressFn(clientId))),
		distsys.EnsureArchetypeRefParam("hasLock", resources.NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
			if !index.Equal(clientId) {
				panic(fmt.Errorf("Not indexed at clientId %v, got index %v instead", clientId, index))
			}
			return matcher
		})),
	)
	defer ctx.Stop()
	go runOrPanic(ctx)

	<-matcher.AwaitValue(tla.MakeBool(true))
	body()
	<-matcher.AwaitValue(tla.MakeBool(false))
}

func testNClients(t *testing.T, clientCount int) {
	// because it takes a moment for previous tests to settle sometimes
	log.Printf("waiting 3 seconds...")
	time.Sleep(3 * time.Second)

	srvId := tla.MakeNumber(0)
	srvCtx := distsys.NewMPCalContext(srvId, locksvc.AServer,
		// distsys.SetTraceRecorder(trace.MakeLocalFileRecorder("server.log")),
		distsys.EnsureArchetypeRefParam("network", resources.NewRelaxedMailboxes(addressFn(srvId))),
	)
	defer srvCtx.Stop()
	go runOrPanic(srvCtx)

	completionCh := make(chan struct{})
	counter := 0
	for i := 0; i < clientCount; i++ {
		go whileHoldingLock(tla.MakeNumber(int32(i+1)), func() {
			counter++
			completionCh <- struct{}{}
		})
	}

	for i := 0; i < clientCount; i++ {
		<-completionCh
	}
	close(completionCh)

	finalCounter := counter
	if finalCounter != clientCount {
		t.Errorf("Wrong counter at end. Got %d, expected %d", finalCounter, clientCount)
	} else {
		log.Printf("Ended with counter %d", finalCounter)
	}
}

func Test1Client(t *testing.T) {
	testNClients(t, 1)
}

func Test5Clients(t *testing.T) {
	testNClients(t, 5)
}

func Test20Clients(t *testing.T) {
	testNClients(t, 20)
}

// func Test1000Clients(t *testing.T) {
// 	testNClients(t, 1000)
// }
