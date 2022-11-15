package shopcart

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func NodeSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NumNodes")())
}
func BenchElemSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.SetComprehension([]tla.Value{NodeSet(iface), tla.ModuleDotDotSymbol(tla.MakeNumber(0), iface.GetConstant("BenchNumRounds")())}, func(args []tla.Value) tla.Value {
		var x tla.Value = args[0]
		_ = x
		var y tla.Value = args[1]
		_ = y
		return tla.MakeTuple(x, y)
	})
}
func Null(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeFunction([]tla.Value{NodeSet(iface)}, func(args0 []tla.Value) tla.Value {
		var n tla.Value = args0[0]
		_ = n
		return tla.MakeNumber(0)
	})
}
func Elem1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("1")
}
func Elem2(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("2")
}
func Elem3(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("3")
}
func AddCmd(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func RemoveCmd(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func AddStart(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func AddFinish(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func Max(iface distsys.ArchetypeInterface, a tla.Value, b tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleGreaterThanSymbol(a, b).AsBool() {
			return a
		} else {
			return b
		}
	}()
}
func MergeVectorClock(iface distsys.ArchetypeInterface, v1 tla.Value, v2 tla.Value) tla.Value {
	return tla.MakeFunction([]tla.Value{tla.ModuleDomainSymbol(v1)}, func(args1 []tla.Value) tla.Value {
		var i tla.Value = args1[0]
		_ = i
		return Max(iface, v1.ApplyFunction(i), v2.ApplyFunction(i))
	})
}
func CompareVectorClock(iface distsys.ArchetypeInterface, v10 tla.Value, v20 tla.Value) tla.Value {
	return func() tla.Value {
		if tla.QuantifiedUniversal([]tla.Value{tla.ModuleDomainSymbol(v10)}, func(args2 []tla.Value) bool {
			var i0 tla.Value = args2[0]
			_ = i0
			return tla.ModuleLessThanOrEqualSymbol(v10.ApplyFunction(i0), v20.ApplyFunction(i0)).AsBool()
		}).AsBool() {
			return tla.ModuleTRUE
		} else {
			return tla.ModuleFALSE
		}
	}()
}
func MergeKeys(iface distsys.ArchetypeInterface, a0 tla.Value, b0 tla.Value) tla.Value {
	return tla.MakeFunction([]tla.Value{tla.ModuleDomainSymbol(a0)}, func(args3 []tla.Value) tla.Value {
		var k tla.Value = args3[0]
		_ = k
		return MergeVectorClock(iface, a0.ApplyFunction(k), b0.ApplyFunction(k))
	})
}
func Query(iface distsys.ArchetypeInterface, r tla.Value) tla.Value {
	return tla.SetRefinement(tla.ModuleDomainSymbol(r.ApplyFunction(tla.MakeString("addMap"))), func(elem tla.Value) bool {
		var elem0 tla.Value = elem
		_ = elem0
		return tla.ModuleLogicalNotSymbol(CompareVectorClock(iface, r.ApplyFunction(tla.MakeString("addMap")).ApplyFunction(elem0), r.ApplyFunction(tla.MakeString("remMap")).ApplyFunction(elem0))).AsBool()
	})
}
func GetVal(iface distsys.ArchetypeInterface, n0 tla.Value, round tla.Value) tla.Value {
	return tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(round, iface.GetConstant("NumNodes")()), tla.ModuleMinusSymbol(n0, tla.MakeNumber(1)))
}
func IsOKSet(iface distsys.ArchetypeInterface, xset tla.Value, round0 tla.Value) tla.Value {
	return tla.QuantifiedUniversal([]tla.Value{NodeSet(iface)}, func(args4 []tla.Value) bool {
		var i1 tla.Value = args4[0]
		_ = i1
		return tla.ModuleInSymbol(GetVal(iface, i1, round0), xset).AsBool()
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
			if tla.ModuleTRUE.AsBool() {
				var reqRead tla.Value
				reqRead, err = iface.Read(in, nil)
				if err != nil {
					return err
				}
				var req tla.Value = reqRead
				_ = req
				if tla.ModuleEqualsSymbol(req.ApplyFunction(tla.MakeString("cmd")), AddCmd(iface)).AsBool() {
					err = iface.Write(crdt, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("cmd"), AddCmd(iface)},
						{tla.MakeString("elem"), req.ApplyFunction(tla.MakeString("elem"))},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("ANode.rcvResp")
				} else {
					if tla.ModuleEqualsSymbol(req.ApplyFunction(tla.MakeString("cmd")), RemoveCmd(iface)).AsBool() {
						err = iface.Write(crdt, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("cmd"), RemoveCmd(iface)},
							{tla.MakeString("elem"), req.ApplyFunction(tla.MakeString("elem"))},
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
			var exprRead tla.Value
			exprRead, err = iface.Read(crdt1, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(out, nil, exprRead)
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
			var condition tla.Value
			condition, err = iface.Read(r0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition, iface.GetConstant("BenchNumRounds")()).AsBool() {
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
			var exprRead0 tla.Value
			exprRead0, err = iface.Read(r1, nil)
			if err != nil {
				return err
			}
			err = iface.Write(crdt2, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("cmd"), AddCmd(iface)},
				{tla.MakeString("elem"), GetVal(iface, iface.Self(), exprRead0)},
			}))
			if err != nil {
				return err
			}
			var exprRead1 tla.Value
			exprRead1, err = iface.Read(c, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			var exprRead2 tla.Value
			exprRead2, err = iface.Read(r1, nil)
			if err != nil {
				return err
			}
			err = iface.Write(c, []tla.Value{iface.Self()}, tla.ModuleUnionSymbol(exprRead1, tla.MakeSet(tla.MakeTuple(AddCmd(iface), GetVal(iface, iface.Self(), exprRead2)))))
			if err != nil {
				return err
			}
			err = iface.Write(out0, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("node"), iface.Self()},
				{tla.MakeString("event"), AddStart(iface)},
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
			var condition0 tla.Value
			condition0, err = iface.Read(crdt3, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			var condition1 tla.Value
			condition1, err = iface.Read(r3, nil)
			if err != nil {
				return err
			}
			if !IsOKSet(iface, condition0, condition1).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			err = iface.Write(out1, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("node"), iface.Self()},
				{tla.MakeString("event"), AddFinish(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead3 tla.Value
			exprRead3, err = iface.Read(r3, nil)
			if err != nil {
				return err
			}
			err = iface.Write(r3, nil, tla.ModulePlusSymbol(exprRead3, tla.MakeNumber(1)))
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
		iface.EnsureArchetypeResourceLocal("ANodeBench.r", tla.MakeNumber(0))
	},
}
