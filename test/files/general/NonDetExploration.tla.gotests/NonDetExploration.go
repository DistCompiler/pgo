package nondetexploration

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func TheSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(tla.MakeTLANumber(1), tla.MakeTLANumber(2))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ACoverage.l1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			var aRead = TheSet(iface)
			if aRead.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a tla.TLAValue = aRead.SelectElement(iface.NextFairnessCounter("ACoverage.l1.0", uint(aRead.AsSet().Len())))
			_ = a
			var bRead = TheSet(iface)
			if bRead.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var b tla.TLAValue = bRead.SelectElement(iface.NextFairnessCounter("ACoverage.l1.1", uint(bRead.AsSet().Len())))
			_ = b
			if !tla.MakeTLABool(tla.TLA_EqualsSymbol(a, tla.MakeTLANumber(1)).AsBool() && tla.TLA_EqualsSymbol(b, tla.MakeTLANumber(1)).AsBool()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("ACoverage.l2")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACoverage.l2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			var aRead0 = TheSet(iface)
			if aRead0.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a0 tla.TLAValue = aRead0.SelectElement(iface.NextFairnessCounter("ACoverage.l2.0", uint(aRead0.AsSet().Len())))
			_ = a0
			var bRead0 = TheSet(iface)
			if bRead0.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var b0 tla.TLAValue = bRead0.SelectElement(iface.NextFairnessCounter("ACoverage.l2.1", uint(bRead0.AsSet().Len())))
			_ = b0
			if !tla.MakeTLABool(tla.TLA_EqualsSymbol(a0, tla.MakeTLANumber(1)).AsBool() && tla.TLA_EqualsSymbol(b0, tla.MakeTLANumber(2)).AsBool()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("ACoverage.l3")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACoverage.l3",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			var aRead1 = TheSet(iface)
			if aRead1.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a1 tla.TLAValue = aRead1.SelectElement(iface.NextFairnessCounter("ACoverage.l3.0", uint(aRead1.AsSet().Len())))
			_ = a1
			var bRead1 = TheSet(iface)
			if bRead1.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var b1 tla.TLAValue = bRead1.SelectElement(iface.NextFairnessCounter("ACoverage.l3.1", uint(bRead1.AsSet().Len())))
			_ = b1
			if !tla.MakeTLABool(tla.TLA_EqualsSymbol(a1, tla.MakeTLANumber(2)).AsBool() && tla.TLA_EqualsSymbol(b1, tla.MakeTLANumber(1)).AsBool()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("ACoverage.l4")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACoverage.l4",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			var aRead2 = TheSet(iface)
			if aRead2.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a2 tla.TLAValue = aRead2.SelectElement(iface.NextFairnessCounter("ACoverage.l4.0", uint(aRead2.AsSet().Len())))
			_ = a2
			var bRead2 = TheSet(iface)
			if bRead2.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var b2 tla.TLAValue = bRead2.SelectElement(iface.NextFairnessCounter("ACoverage.l4.1", uint(bRead2.AsSet().Len())))
			_ = b2
			if !tla.MakeTLABool(tla.TLA_EqualsSymbol(a2, tla.MakeTLANumber(2)).AsBool() && tla.TLA_EqualsSymbol(b2, tla.MakeTLANumber(2)).AsBool()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("ACoverage.Done")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACoverage.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACoincidence.lbl",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			var aRead3 = TheSet(iface)
			if aRead3.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a3 tla.TLAValue = aRead3.SelectElement(iface.NextFairnessCounter("ACoincidence.lbl.0", uint(aRead3.AsSet().Len())))
			_ = a3
			var bRead3 = TheSet(iface)
			if bRead3.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var b3 tla.TLAValue = bRead3.SelectElement(iface.NextFairnessCounter("ACoincidence.lbl.1", uint(bRead3.AsSet().Len())))
			_ = b3
			if !tla.MakeTLABool(tla.TLA_EqualsSymbol(a3, tla.MakeTLANumber(1)).AsBool() && tla.TLA_EqualsSymbol(b3, tla.MakeTLANumber(1)).AsBool()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			// no statements
			var aRead4 = TheSet(iface)
			if aRead4.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a4 tla.TLAValue = aRead4.SelectElement(iface.NextFairnessCounter("ACoincidence.lbl.2", uint(aRead4.AsSet().Len())))
			_ = a4
			var bRead4 = TheSet(iface)
			if bRead4.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var b4 tla.TLAValue = bRead4.SelectElement(iface.NextFairnessCounter("ACoincidence.lbl.3", uint(bRead4.AsSet().Len())))
			_ = b4
			if !tla.MakeTLABool(tla.TLA_EqualsSymbol(a4, tla.MakeTLANumber(2)).AsBool() && tla.TLA_EqualsSymbol(b4, tla.MakeTLANumber(2)).AsBool()).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("ACoincidence.Done")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACoincidence.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ACoverage = distsys.MPCalArchetype{
	Name:              "ACoverage",
	Label:             "ACoverage.l1",
	RequiredRefParams: []string{},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var ACoincidence = distsys.MPCalArchetype{
	Name:              "ACoincidence",
	Label:             "ACoincidence.lbl",
	RequiredRefParams: []string{},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
