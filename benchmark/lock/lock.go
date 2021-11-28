package lock

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumNodes")())
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.aquireLock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			lock, err := iface.RequireArchetypeResourceRef("ANode.lock")
			if err != nil {
				return err
			}
			var condition tla.TLAValue
			condition, err = iface.Read(lock, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_LogicalNotSymbol(condition).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			err = iface.Write(lock, []tla.TLAValue{}, tla.TLA_TRUE)
			if err != nil {
				return err
			}
			return iface.Goto("ANode.criticalSection")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.criticalSection",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			lock1, err := iface.RequireArchetypeResourceRef("ANode.lock")
			if err != nil {
				return err
			}
			tla.MakeTLATuple(tla.MakeTLAString("in critical section: "), iface.Self()).PCalPrint()
			err = iface.Write(lock1, []tla.TLAValue{}, tla.TLA_FALSE)
			if err != nil {
				return err
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
	Label:             "ANode.aquireLock",
	RequiredRefParams: []string{"ANode.lock"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
