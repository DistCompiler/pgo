package gcounter

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
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
func IncStart(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
}
func IncFinish(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
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
			err = iface.Write(cntr, []tla.TLAValue{iface.Self()}, tla.MakeTLANumber(1))
			if err != nil {
				return err
			}
			err = iface.Write(c, []tla.TLAValue{iface.Self()}, tla.MakeTLASet(tla.MakeTLATuple(iface.Self(), tla.MakeTLANumber(1))))
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
	distsys.MPCalCriticalSection{
		Name: "ANodeBench.nodeBenchLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			r := iface.RequireArchetypeResource("ANodeBench.r")
			var condition0 tla.TLAValue
			condition0, err = iface.Read(r, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition0, iface.GetConstant("BENCH_NUM_ROUNDS")()).AsBool() {
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
			err = iface.Write(cntr1, []tla.TLAValue{iface.Self()}, tla.MakeTLANumber(1))
			if err != nil {
				return err
			}
			err = iface.Write(out, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("node"), iface.Self()},
				{tla.MakeTLAString("event"), IncStart(iface)},
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
			var condition1 tla.TLAValue
			condition1, err = iface.Read(cntr2, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			var condition2 tla.TLAValue
			condition2, err = iface.Read(r0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_GreaterThanOrEqualSymbol(condition1, tla.TLA_AsteriskSymbol(tla.TLA_PlusSymbol(condition2, tla.MakeTLANumber(1)), iface.GetConstant("NUM_NODES")())).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			err = iface.Write(out0, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("node"), iface.Self()},
				{tla.MakeTLAString("event"), IncFinish(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(r0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(r0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead, tla.MakeTLANumber(1)))
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
		iface.EnsureArchetypeResourceLocal("ANodeBench.r", tla.MakeTLANumber(0))
	},
}
