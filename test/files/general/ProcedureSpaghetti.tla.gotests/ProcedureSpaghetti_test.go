package procedurespaghetti

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"testing"
)

func TestArch1(t *testing.T) {
	ctx := distsys.NewMPCalContext(tla.MakeTLAString("self"), Arch1,
		distsys.EnsureArchetypeRefParam("e", distsys.LocalArchetypeResourceMaker(tla.MakeTLANumber(13))),
		distsys.EnsureArchetypeValueParam("f", tla.MakeTLANumber(21)))

	err := ctx.Run()
	if err != nil {
		panic(err)
	}

	eVal := ctx.IFace().ReadArchetypeResourceLocal("&Arch1.e")
	fVal := ctx.IFace().ReadArchetypeResourceLocal("Arch1.f")

	if !eVal.Equal(tla.MakeTLANumber(35)) {
		t.Errorf("eVal did not equal expected value 35, was %v instead", eVal)
	}
	if !fVal.Equal(tla.MakeTLANumber(21)) {
		t.Errorf("fVal did not equal expected value 21 (same as start), was %v instead", fVal)
	}
}
