package shopcart

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
func BenchElemSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLASetComprehension([]tla.TLAValue{NodeSet(iface), tla.TLA_DotDotSymbol(tla.MakeTLANumber(0), iface.GetConstant("BenchNumRounds")())}, func(args []tla.TLAValue) tla.TLAValue {
		var x tla.TLAValue = args[0]
		_ = x
		var y tla.TLAValue = args[1]
		_ = y
		return tla.MakeTLATuple(x, y)
	})
}
func Null(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAFunction([]tla.TLAValue{NodeSet(iface)}, func(args0 []tla.TLAValue) tla.TLAValue {
		var n tla.TLAValue = args0[0]
		_ = n
		return tla.MakeTLANumber(0)
	})
}
func Elem1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("1")
}
func Elem2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("2")
}
func Elem3(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("3")
}
func AddCmd(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func RemoveCmd(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func AddStart(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
}
func AddFinish(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
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
	return tla.MakeTLAFunction([]tla.TLAValue{tla.TLA_DomainSymbol(v1)}, func(args1 []tla.TLAValue) tla.TLAValue {
		var i tla.TLAValue = args1[0]
		_ = i
		return Max(iface, v1.ApplyFunction(i), v2.ApplyFunction(i))
	})
}
func CompareVectorClock(iface distsys.ArchetypeInterface, v10 tla.TLAValue, v20 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLAQuantifiedUniversal([]tla.TLAValue{tla.TLA_DomainSymbol(v10)}, func(args2 []tla.TLAValue) bool {
			var i0 tla.TLAValue = args2[0]
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
	return tla.MakeTLAFunction([]tla.TLAValue{tla.TLA_DomainSymbol(a0)}, func(args3 []tla.TLAValue) tla.TLAValue {
		var k tla.TLAValue = args3[0]
		_ = k
		return MergeVectorClock(iface, a0.ApplyFunction(k), b0.ApplyFunction(k))
	})
}
func Query(iface distsys.ArchetypeInterface, r tla.TLAValue) tla.TLAValue {
	return tla.TLASetRefinement(tla.TLA_DomainSymbol(r.ApplyFunction(tla.MakeTLAString("addMap"))), func(elem tla.TLAValue) bool {
		var elem0 tla.TLAValue = elem
		_ = elem0
		return tla.TLA_LogicalNotSymbol(CompareVectorClock(iface, r.ApplyFunction(tla.MakeTLAString("addMap")).ApplyFunction(elem0), r.ApplyFunction(tla.MakeTLAString("remMap")).ApplyFunction(elem0))).AsBool()
	})
}
func GetVal(iface distsys.ArchetypeInterface, n0 tla.TLAValue, round tla.TLAValue) tla.TLAValue {
	return tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(round, iface.GetConstant("NumNodes")()), tla.TLA_MinusSymbol(n0, tla.MakeTLANumber(1)))
}
func IsOKSet(iface distsys.ArchetypeInterface, xset tla.TLAValue, round0 tla.TLAValue) tla.TLAValue {
	return tla.TLAQuantifiedUniversal([]tla.TLAValue{NodeSet(iface)}, func(args4 []tla.TLAValue) bool {
		var i1 tla.TLAValue = args4[0]
		_ = i1
		return tla.TLA_InSymbol(GetVal(iface, i1, round0), xset).AsBool()
	})
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.nodeLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			in, err := iface.RequireArchetypeResourceRef("ANode.in")
			if err != nil {
				return err
			}
			crdt, err := iface.RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var reqRead tla.TLAValue
				reqRead, err = iface.Read(in, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var req tla.TLAValue = reqRead
				_ = req
				if tla.TLA_EqualsSymbol(req.ApplyFunction(tla.MakeTLAString("cmd")), AddCmd(iface)).AsBool() {
					err = iface.Write(crdt, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("cmd"), AddCmd(iface)},
						{tla.MakeTLAString("elem"), req.ApplyFunction(tla.MakeTLAString("elem"))},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("ANode.rcvResp")
				} else {
					if tla.TLA_EqualsSymbol(req.ApplyFunction(tla.MakeTLAString("cmd")), RemoveCmd(iface)).AsBool() {
						err = iface.Write(crdt, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("cmd"), RemoveCmd(iface)},
							{tla.MakeTLAString("elem"), req.ApplyFunction(tla.MakeTLAString("elem"))},
						}))
						if err != nil {
							return err
						}
						return iface.Goto("ANode.rcvResp")
					} else {
						return iface.Goto("ANode.rcvResp")
					}
					// no statements
				}
				// no statements
				// no statements
			} else {
				return iface.Goto("ANode.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.rcvResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			out, err := iface.RequireArchetypeResourceRef("ANode.out")
			if err != nil {
				return err
			}
			crdt1, err := iface.RequireArchetypeResourceRef("ANode.crdt")
			if err != nil {
				return err
			}
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(crdt1, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(out, []tla.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("ANode.nodeLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.nodeBenchLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			r0 := iface.RequireArchetypeResource("ANodeBench.r")
			var condition tla.TLAValue
			condition, err = iface.Read(r0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition, iface.GetConstant("BenchNumRounds")()).AsBool() {
				return iface.Goto("ANodeBench.add")
			} else {
				return iface.Goto("ANodeBench.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.add",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt2, err := iface.RequireArchetypeResourceRef("ANodeBench.crdt")
			if err != nil {
				return err
			}
			r1 := iface.RequireArchetypeResource("ANodeBench.r")
			c, err := iface.RequireArchetypeResourceRef("ANodeBench.c")
			if err != nil {
				return err
			}
			out0, err := iface.RequireArchetypeResourceRef("ANodeBench.out")
			if err != nil {
				return err
			}
			var exprRead0 tla.TLAValue
			exprRead0, err = iface.Read(r1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(crdt2, []tla.TLAValue{iface.Self()}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("cmd"), AddCmd(iface)},
				{tla.MakeTLAString("elem"), GetVal(iface, iface.Self(), exprRead0)},
			}))
			if err != nil {
				return err
			}
			var exprRead1 tla.TLAValue
			exprRead1, err = iface.Read(c, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			var exprRead2 tla.TLAValue
			exprRead2, err = iface.Read(r1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(c, []tla.TLAValue{iface.Self()}, tla.TLA_UnionSymbol(exprRead1, tla.MakeTLASet(tla.MakeTLATuple(AddCmd(iface), GetVal(iface, iface.Self(), exprRead2)))))
			if err != nil {
				return err
			}
			err = iface.Write(out0, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("node"), iface.Self()},
				{tla.MakeTLAString("event"), AddStart(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ANodeBench.waitAdd")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.waitAdd",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt3, err := iface.RequireArchetypeResourceRef("ANodeBench.crdt")
			if err != nil {
				return err
			}
			r3 := iface.RequireArchetypeResource("ANodeBench.r")
			out1, err := iface.RequireArchetypeResourceRef("ANodeBench.out")
			if err != nil {
				return err
			}
			var condition0 tla.TLAValue
			condition0, err = iface.Read(crdt3, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			var condition1 tla.TLAValue
			condition1, err = iface.Read(r3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !IsOKSet(iface, condition0, condition1).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			err = iface.Write(out1, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("node"), iface.Self()},
				{tla.MakeTLAString("event"), AddFinish(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead3 tla.TLAValue
			exprRead3, err = iface.Read(r3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(r3, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead3, tla.MakeTLANumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("ANodeBench.nodeBenchLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ANode = distsys.MPCalArchetype{
	Name:              "ANode",
	Label:             "ANode.nodeLoop",
	RequiredRefParams: []string{"ANode.crdt", "ANode.in", "ANode.out"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var ANodeBench = distsys.MPCalArchetype{
	Name:              "ANodeBench",
	Label:             "ANodeBench.nodeBenchLoop",
	RequiredRefParams: []string{"ANodeBench.crdt", "ANodeBench.out", "ANodeBench.c"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ANodeBench.r", tla.MakeTLANumber(0))
	},
}
