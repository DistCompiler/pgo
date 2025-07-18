package test

import (
	"fmt"
	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

var procTable = distsys.MakeMPCalProcTable(
	distsys.MPCalProc{
		Name:      "inc",
		Label:     "inc.inc1",
		StateVars: []string{"inc.self_", "inc.counter"},
		PreAmble: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			// no statements
			return nil
		},
	},
)

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "inc.inc1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			counter, err := iface.RequireArchetypeResourceRef("inc.counter")
			if err != nil {
				return err
			}
			var exprRead tla.Value
			exprRead, err = iface.Read(counter, nil)
			if err != nil {
				return err
			}
			err = iface.Write(counter, nil, tla.ModulePlusSymbol(exprRead, tla.MakeNumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("inc.inc2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "inc.inc2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			return iface.Return()
		},
	},
	distsys.MPCalCriticalSection{
		Name: "inc.Error",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrProcedureFallthrough
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Counter.c0",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			value := iface.RequireArchetypeResource("Counter.value")
			err = iface.Write(value, nil, tla.MakeNumber(0))
			if err != nil {
				return err
			}
			return iface.Goto("Counter.c1")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Counter.c1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			return iface.Call("inc", "Counter.c2", iface.Self(), tla.MakeString("Counter.value"))
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Counter.c2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			out, err := iface.RequireArchetypeResourceRef("Counter.out")
			if err != nil {
				return err
			}
			value1 := iface.RequireArchetypeResource("Counter.value")
			var exprRead0 tla.Value
			exprRead0, err = iface.Read(value1, nil)
			if err != nil {
				return err
			}
			err = iface.Write(out, nil, exprRead0)
			if err != nil {
				return err
			}
			return iface.Goto("Counter.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Counter.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var Counter = distsys.MPCalArchetype{
	Name:              "Counter",
	Label:             "Counter.c0",
	RequiredRefParams: []string{"Counter.out"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("Counter.value", tla.Value{})
	},
}
