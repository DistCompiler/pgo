package indexinglocals

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func NodeSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_DotDotSymbol(tla.MakeNumber(1), tla.MakeNumber(1))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.logWrite",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			log := iface.RequireArchetypeResource("ANode.log")
			var exprRead tla.Value
			exprRead, err = iface.Read(log, nil)
			if err != nil {
				return err
			}
			err = iface.Write(log, nil, tla.Symbol_Append(exprRead, tla.MakeNumber(68)))
			if err != nil {
				return err
			}
			var exprRead0 tla.Value
			exprRead0, err = iface.Read(log, nil)
			if err != nil {
				return err
			}
			err = iface.Write(log, nil, tla.Symbol_Append(exprRead0, tla.MakeNumber(5)))
			if err != nil {
				return err
			}
			err = iface.Write(log, []tla.Value{tla.MakeNumber(2)}, tla.MakeNumber(21))
			if err != nil {
				return err
			}
			var exprRead1 tla.Value
			exprRead1, err = iface.Read(log, nil)
			if err != nil {
				return err
			}
			err = iface.Write(log, nil, tla.Symbol_Append(exprRead1, tla.MakeNumber(999)))
			if err != nil {
				return err
			}
			var exprRead2 tla.Value
			exprRead2, err = iface.Read(log, nil)
			if err != nil {
				return err
			}
			err = iface.Write(log, nil, tla.Symbol_Append(exprRead2, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("foo"), tla.MakeNumber(42)},
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
			err = iface.Write(log8, []tla.Value{tla.MakeNumber(1)}, tla.MakeNumber(3))
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
			var exprRead3 tla.Value
			exprRead3, err = iface.Read(log9, nil)
			if err != nil {
				return err
			}
			err = iface.Write(p, nil, exprRead3.ApplyFunction(tla.MakeNumber(1)))
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
			err = iface.Write(log10, []tla.Value{tla.MakeNumber(4), tla.MakeString("foo")}, tla.MakeNumber(43))
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
		iface.EnsureArchetypeResourceLocal("ANode.log", tla.MakeTuple())
		iface.EnsureArchetypeResourceLocal("ANode.p", tla.Value{})
	},
}
