package nondetexploration

import (
	"testing"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

func TestCoverage(t *testing.T) {
	errCh := make(chan error, 1)
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), ACoverage)
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
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), ACoincidence)
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

func TestComplex(t *testing.T) {
	errCh := make(chan error, 1)
	ctx := distsys.NewMPCalContext(tla.MakeString("self"), AComplex)
	go func() {
		errCh <- ctx.Run()
	}()

	select {
	case err := <-errCh:
		if err != nil {
			panic(err)
		}
	case <-time.After(5 * time.Second):
		t.Fatalf("timeout: AComplex should eventually (within 5 seconds) terminate")
	}
}
