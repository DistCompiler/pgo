package branchscheduling

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
)

//run gogen -s test/files/general/BranchScheduling.tla -o test/files/general/BranchScheduling.tla.gotests/BranchScheduling.go

func TestBasic(t *testing.T) {
	errCh := make(chan error, 1)
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), ABranch)
	go func() {
		errCh <- ctx.Run()
		fmt.Println(ctx.ReadArchetypeResourceLocal("ABranch.i"))
		fmt.Println(ctx.ReadArchetypeResourceLocal("ABranch.j"))
		fmt.Println(ctx.ReadArchetypeResourceLocal("ABranch.k"))
	}()

	select {
	case err := <-errCh:
		if err != nil {
			panic(err)
		}
		//case <-time.After(2 * time.Second):
		//	t.Fatalf("timeout: ABranch should eventually (within 5 seconds) terminate")
	}
}
