package indexinglocals

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), tla.MakeTLANumber(1))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.logWrite",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			log := iface.RequireArchetypeResource("ANode.log")
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(log, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(log, []tla.TLAValue{}, tla.TLA_Append(exprRead, tla.MakeTLANumber(68)))
			if err != nil {
				return err
			}
			var exprRead0 tla.TLAValue
			exprRead0, err = iface.Read(log, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(log, []tla.TLAValue{}, tla.TLA_Append(exprRead0, tla.MakeTLANumber(5)))
			if err != nil {
				return err
			}
			err = iface.Write(log, []tla.TLAValue{tla.MakeTLANumber(2)}, tla.MakeTLANumber(21))
			if err != nil {
				return err
			}
			var exprRead1 tla.TLAValue
			exprRead1, err = iface.Read(log, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(log, []tla.TLAValue{}, tla.TLA_Append(exprRead1, tla.MakeTLANumber(999)))
			if err != nil {
				return err
			}
			var exprRead2 tla.TLAValue
			exprRead2, err = iface.Read(log, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(log, []tla.TLAValue{}, tla.TLA_Append(exprRead2, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("foo"), tla.MakeTLANumber(42)},
			})))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.logUpdate")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.logUpdate",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			log8 := iface.RequireArchetypeResource("ANode.log")
			err = iface.Write(log8, []tla.TLAValue{tla.MakeTLANumber(1)}, tla.MakeTLANumber(3))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.logRead")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.logRead",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			p := iface.RequireArchetypeResource("ANode.p")
			log9 := iface.RequireArchetypeResource("ANode.log")
			var exprRead3 tla.TLAValue
			exprRead3, err = iface.Read(log9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(p, []tla.TLAValue{}, exprRead3.ApplyFunction(tla.MakeTLANumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.multiWrite")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.multiWrite",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			log10 := iface.RequireArchetypeResource("ANode.log")
			err = iface.Write(log10, []tla.TLAValue{tla.MakeTLANumber(4), tla.MakeTLAString("foo")}, tla.MakeTLANumber(43))
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
	Label:             "ANode.logWrite",
	RequiredRefParams: []string{},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ANode.log", tla.MakeTLATuple())
		iface.EnsureArchetypeResourceLocal("ANode.p", tla.TLAValue{})
	},
}
