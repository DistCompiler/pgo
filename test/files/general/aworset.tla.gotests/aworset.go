package aworset

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NUM_NODES")())
}
func NULL(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAFunction([]tla.TLAValue{NODE_SET(iface)}, func(args []tla.TLAValue) tla.TLAValue {
		var n tla.TLAValue = args[0]
		_ = n
		return tla.MakeTLANumber(0)
	})
}
func ELEM1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("1")
}
func ELEM2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("2")
}
func ELEM3(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("3")
}
func ELEM_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(ELEM1(iface), ELEM2(iface))
}
func AddCmd(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func RemoveCmd(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func Max(iface distsys.ArchetypeInterface, a tla.TLAValue, b tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_GreaterThanSymbol(a, b).AsBool() {
			return a
		} else {
			return b
		}
	}()
}
func MergeVectorClock(iface distsys.ArchetypeInterface, v1 tla.TLAValue, v2 tla.TLAValue) tla.TLAValue {
	return tla.MakeTLAFunction([]tla.TLAValue{tla.TLA_DomainSymbol(v1)}, func(args0 []tla.TLAValue) tla.TLAValue {
		var i tla.TLAValue = args0[0]
		_ = i
		return Max(iface, v1.ApplyFunction(i), v2.ApplyFunction(i))
	})
}
func CompareVectorClock(iface distsys.ArchetypeInterface, v10 tla.TLAValue, v20 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLAQuantifiedUniversal([]tla.TLAValue{tla.TLA_DomainSymbol(v10)}, func(args1 []tla.TLAValue) bool {
			var i0 tla.TLAValue = args1[0]
			_ = i0
			return tla.TLA_LessThanOrEqualSymbol(v10.ApplyFunction(i0), v20.ApplyFunction(i0)).AsBool()
		}).AsBool() {
			return tla.TLA_TRUE
		} else {
			return tla.TLA_FALSE
		}
	}()
}
func MergeKeys(iface distsys.ArchetypeInterface, a0 tla.TLAValue, b0 tla.TLAValue) tla.TLAValue {
	return tla.MakeTLAFunction([]tla.TLAValue{tla.TLA_DomainSymbol(a0)}, func(args2 []tla.TLAValue) tla.TLAValue {
		var k tla.TLAValue = args2[0]
		_ = k
		return MergeVectorClock(iface, a0.ApplyFunction(k), b0.ApplyFunction(k))
	})
}
func QUERY(iface distsys.ArchetypeInterface, r tla.TLAValue) tla.TLAValue {
	return tla.TLASetRefinement(tla.TLA_DomainSymbol(r.ApplyFunction(tla.MakeTLAString("addMap"))), func(elem tla.TLAValue) bool {
		var elem0 tla.TLAValue = elem
		_ = elem0
		return tla.TLA_LogicalNotSymbol(CompareVectorClock(iface, r.ApplyFunction(tla.MakeTLAString("addMap")).ApplyFunction(elem0), r.ApplyFunction(tla.MakeTLAString("remMap")).ApplyFunction(elem0))).AsBool()
	})
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.addItem1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt, err := iface.RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return err
			}
			err = iface.Write(crdt, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("cmd"), AddCmd(iface)},
				{tla.MakeTLAString("elem"), ELEM1(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.removeItem1")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.removeItem1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt0, err := iface.RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return err
			}
			err = iface.Write(crdt0, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("cmd"), RemoveCmd(iface)},
				{tla.MakeTLAString("elem"), ELEM1(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.addItem2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.addItem2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt1, err := iface.RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return err
			}
			err = iface.Write(crdt1, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("cmd"), AddCmd(iface)},
				{tla.MakeTLAString("elem"), ELEM2(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ANode.removeItem2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.removeItem2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt2, err := iface.RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return err
			}
			err = iface.Write(crdt2, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("cmd"), RemoveCmd(iface)},
				{tla.MakeTLAString("elem"), ELEM2(iface)},
			}))
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
	Label:             "ANode.addItem1",
	RequiredRefParams: []string{"ANode.crdt"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
