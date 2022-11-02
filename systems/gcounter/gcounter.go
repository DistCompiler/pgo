package gcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func SUM(iface distsys.ArchetypeInterface, f tla.Value, d tla.Value) tla.Value {
	return func() tla.Value {
		if tla.Symbol_EqualsSymbol(d, tla.MakeSet()).AsBool() {
			return tla.MakeNumber(0)
		} else {
			return func() tla.Value {
				var x tla.Value = tla.Choose(d, func(element tla.Value) bool {
					var x0 tla.Value = element
					_ = x0
					return tla.Symbol_TRUE.AsBool()
				})
				_ = x
				return tla.Symbol_PlusSymbol(f.ApplyFunction(x), SUM(iface, f, tla.Symbol_BackslashSymbol(d, tla.MakeSet(x))))
			}()
		}
	}()
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_DotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NUM_NODES")())
}
func MAX(iface distsys.ArchetypeInterface, a tla.Value, b tla.Value) tla.Value {
	return func() tla.Value {
		if tla.Symbol_GreaterThanSymbol(a, b).AsBool() {
			return a
		} else {
			return b
		}
	}()
}
func IncStart(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func IncFinish(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
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
			c, err := iface.RequireArchetypeResourceRef("ANode.c")
			if err != nil {
				return err
			}
			err = iface.Write(cntr, []tla.Value{iface.Self()}, tla.MakeNumber(1))
			if err != nil {
				return err
			}
			err = iface.Write(c, []tla.Value{iface.Self()}, tla.MakeSet(tla.MakeTuple(iface.Self(), tla.MakeNumber(1))))
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
			var condition tla.Value
			condition, err = iface.Read(cntr0, []tla.Value{iface.Self()})
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
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.nodeBenchLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			r := iface.RequireArchetypeResource("ANodeBench.r")
			var condition0 tla.Value
			condition0, err = iface.Read(r, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_LessThanSymbol(condition0, iface.GetConstant("BENCH_NUM_ROUNDS")()).AsBool() {
				return iface.Goto("ANodeBench.inc")
			} else {
				return iface.Goto("ANodeBench.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.inc",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			cntr1, err := iface.RequireArchetypeResourceRef("ANodeBench.cntr")
			if err != nil {
				return err
			}
			out, err := iface.RequireArchetypeResourceRef("ANodeBench.out")
			if err != nil {
				return err
			}
			err = iface.Write(cntr1, []tla.Value{iface.Self()}, tla.MakeNumber(1))
			if err != nil {
				return err
			}
			err = iface.Write(out, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("node"), iface.Self()},
				{tla.MakeString("event"), IncStart(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ANodeBench.waitInc")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.waitInc",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			cntr2, err := iface.RequireArchetypeResourceRef("ANodeBench.cntr")
			if err != nil {
				return err
			}
			r0 := iface.RequireArchetypeResource("ANodeBench.r")
			out0, err := iface.RequireArchetypeResourceRef("ANodeBench.out")
			if err != nil {
				return err
			}
			var condition1 tla.Value
			condition1, err = iface.Read(cntr2, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			var condition2 tla.Value
			condition2, err = iface.Read(r0, nil)
			if err != nil {
				return err
			}
			if !tla.Symbol_GreaterThanOrEqualSymbol(condition1, tla.Symbol_AsteriskSymbol(tla.Symbol_PlusSymbol(condition2, tla.MakeNumber(1)), iface.GetConstant("NUM_NODES")())).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			err = iface.Write(out0, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("node"), iface.Self()},
				{tla.MakeString("event"), IncFinish(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead tla.Value
			exprRead, err = iface.Read(r0, nil)
			if err != nil {
				return err
			}
			err = iface.Write(r0, nil, tla.Symbol_PlusSymbol(exprRead, tla.MakeNumber(1)))
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
	Label:             "ANode.update",
	RequiredRefParams: []string{"ANode.cntr", "ANode.c"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var ANodeBench = distsys.MPCalArchetype{
	Name:              "ANodeBench",
	Label:             "ANodeBench.nodeBenchLoop",
	RequiredRefParams: []string{"ANodeBench.cntr", "ANodeBench.out"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ANodeBench.r", tla.MakeNumber(0))
	},
}
