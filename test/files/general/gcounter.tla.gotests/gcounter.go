package gcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrContextClosed
var _ = tla.TLAValue{} // same, for tla

func SUM(iface distsys.ArchetypeInterface, f tla.TLAValue, d tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_EqualsSymbol(d, tla.MakeTLASet()).AsBool() {
			return tla.MakeTLANumber(0)
		} else {
			return func() tla.TLAValue {
				var x tla.TLAValue = tla.TLAChoose(d, func(element tla.TLAValue) bool {
					var x0 tla.TLAValue = element
					_ = x0
					return tla.TLA_TRUE.AsBool()
				})
				_ = x
				return tla.TLA_PlusSymbol(f.ApplyFunction(x), SUM(iface, f, tla.TLA_BackslashSymbol(d, tla.MakeTLASet(x))))
			}()
		}
	}()
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NUM_NODES")())
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
			if !tla.TLA_EqualsSymbol(condition, iface.GetConstant("NUM_NODES")()).AsBool() {
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
