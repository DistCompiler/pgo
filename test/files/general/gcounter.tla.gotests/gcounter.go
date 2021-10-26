package gcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrContextClosed
var _ = tla.TLAValue{} // same, for tla

func SUM(iface distsys.ArchetypeInterface, f tla.TLAValue) tla.TLAValue {
	return tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(f.ApplyFunction(tla.MakeTLANumber(1)), f.ApplyFunction(tla.MakeTLANumber(2))), f.ApplyFunction(tla.MakeTLANumber(3)))
}
func NUM_NODES(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), NUM_NODES(iface))
}
func MAX(iface distsys.ArchetypeInterface, a tla.TLAValue, b tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_GreaterThanSymbol(a, b).AsBool() {
			return a
		} else {
			return b
		}
	}()
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
			err = iface.Write(cntr, []tla.TLAValue{iface.Self()}, tla.MakeTLANumber(1))
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
			cntr0, err := iface.RequireArchetypeResourceRef("ANode.cntr")
			if err != nil {
				return err
			}
			var condition tla.TLAValue
			condition, err = iface.Read(cntr0, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition, NUM_NODES(iface)).AsBool() {
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
