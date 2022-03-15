package branchscheduling

import (
	"testing"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

//run gogen -s test/files/general/BranchScheduling.tla -o test/files/general/BranchScheduling.tla.gotests/BranchScheduling.go

func TestBasic(t *testing.T) {
	errCh := make(chan error, 1)
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), ABranch)
	go func() {
		errCh <- ctx.Run()
	}()

	select {
	case err := <-errCh:
		if err != nil {
			panic(err)
		}
	case <-time.After(2 * time.Second):
		t.Fatalf("timeout: ABranch should eventually (within 5 seconds) terminate")
	}
}
