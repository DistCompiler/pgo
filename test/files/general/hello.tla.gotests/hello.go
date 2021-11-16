package hello

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func HELLO(iface distsys.ArchetypeInterface) tla.TLAValue {
	return iface.GetConstant("MK_HELLO")(tla.MakeTLAString("hell"), tla.MakeTLAString("o"))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AHello.lbl",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			out, err := iface.RequireArchetypeResourceRef("AHello.out")
			if err != nil {
				return err
			}
			err = iface.Write(out, []tla.TLAValue{}, HELLO(iface))
			if err != nil {
				return err
			}
			return iface.Goto("AHello.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AHello.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AHello = distsys.MPCalArchetype{
	Name:              "AHello",
	Label:             "AHello.lbl",
	RequiredRefParams: []string{"AHello.out"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
