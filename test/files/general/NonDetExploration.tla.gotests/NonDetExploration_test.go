package nondetexploration

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
	"time"
)

func TestCoverage(t *testing.T) {
	errCh := make(chan error, 1)
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), ACoverage)
	go func() {
		errCh <- ctx.Run()
	}()

	select {
	case err := <-errCh:
		if err != nil {
			panic(err)
		}
	case <-time.After(5 * time.Second):
		t.Fatalf("timeout: ACoverage should eventually (within 5 seconds) terminate")
	}
}

func TestCoincidence(t *testing.T) {
	errCh := make(chan error, 1)
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), ACoincidence)
	go func() {
		errCh <- ctx.Run()
	}()

	select {
	case err := <-errCh:
		if err != nil {
			panic(err)
		}
	case <-time.After(5 * time.Second):
		t.Fatalf("timeout: ACoincidence should eventually (within 5 seconds) terminate")
	}
}
