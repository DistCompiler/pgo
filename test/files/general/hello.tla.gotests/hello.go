package hello

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

func HELLO(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return iface.GetConstant("MK_HELLO")(distsys.NewTLAString("hell"), distsys.NewTLAString("o"))
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
			err = iface.Write(out, []distsys.TLAValue{}, HELLO(iface))
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
