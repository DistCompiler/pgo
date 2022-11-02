package shcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func NODE_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_DotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NUM_NODES")())
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.update",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			cntr, err := iface.RequireArchetypeResourceRef("ANode.cntr")
			if err != nil {
				return err
			}
			var exprRead tla.Value
			exprRead, err = iface.Read(cntr, nil)
			if err != nil {
				return err
			}
			err = iface.Write(cntr, nil, tla.Symbol_PlusSymbol(exprRead, tla.MakeNumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.wait")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.wait",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			cntr1, err := iface.RequireArchetypeResourceRef("ANode.cntr")
			if err != nil {
				return err
			}
			var condition tla.Value
			condition, err = iface.Read(cntr1, nil)
			if err != nil {
				return err
			}
			if !tla.Symbol_EqualsSymbol(condition, iface.GetConstant("NUM_NODES")()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("ANode.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ANode = distsys.MPCalArchetype{
	Name:              "ANode",
	Label:             "ANode.update",
	RequiredRefParams: []string{"ANode.cntr"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
