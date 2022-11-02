package procedurespaghetti

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

var procTable = distsys.MakeMPCalProcTable(
	distsys.MPCalProc{
		Name:      "Proc1",
		Label:     "Proc1.Proc1lbl1",
		StateVars: []string{"Proc1.a", "Proc1.b", "Proc1.c"},
		PreAmble: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			c := iface.RequireArchetypeResource("Proc1.c")
			err = iface.Write(c, nil, tla.Symbol_defaultInitValue)
			if err != nil {
				return err
			}
			// no statements
			return nil
		},
	},
	distsys.MPCalProc{
		Name:      "Proc2",
		Label:     "Proc2.Proc2lbl1",
		StateVars: []string{"Proc2.a_"},
		PreAmble: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			// no statements
			return nil
		},
	},
	distsys.MPCalProc{
		Name:      "RecursiveProcRef",
		Label:     "RecursiveProcRef.RecursiveProclbl1",
		StateVars: []string{"RecursiveProcRef.X"},
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
		Name: "Proc1.Proc1lbl1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			a := iface.ReadArchetypeResourceLocal("Proc1.a")
			return iface.Call("Proc2", "Proc1.Proc1lbl2", a)
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Proc1.Proc1lbl2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			a0, err := iface.RequireArchetypeResourceRef("Proc1.a")
			if err != nil {
				return err
			}
			b := iface.RequireArchetypeResource("Proc1.b")
			var exprRead tla.Value
			exprRead, err = iface.Read(a0, nil)
			if err != nil {
				return err
			}
			var exprRead0 tla.Value
			exprRead0, err = iface.Read(b, nil)
			if err != nil {
				return err
			}
			err = iface.Write(a0, nil, tla.Symbol_PlusSymbol(exprRead, exprRead0))
			if err != nil {
				return err
			}
			return iface.Return()
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Proc1.Error",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrProcedureFallthrough
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Proc2.Proc2lbl1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			a_, err := iface.RequireArchetypeResourceRef("Proc2.a_")
			if err != nil {
				return err
			}
			var exprRead1 tla.Value
			exprRead1, err = iface.Read(a_, nil)
			if err != nil {
				return err
			}
			err = iface.Write(a_, nil, tla.Symbol_PlusSymbol(exprRead1, tla.MakeNumber(1)))
			if err != nil {
				return err
			}
			return iface.Return()
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Proc2.Error",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrProcedureFallthrough
		},
	},
	distsys.MPCalCriticalSection{
		Name: "RecursiveProcRef.RecursiveProclbl1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			X, err := iface.RequireArchetypeResourceRef("RecursiveProcRef.X")
			if err != nil {
				return err
			}
			var toPrint tla.Value
			toPrint, err = iface.Read(X, nil)
			if err != nil {
				return err
			}
			toPrint.PCalPrint()
			X0 := iface.ReadArchetypeResourceLocal("RecursiveProcRef.X")
			return iface.TailCall("RecursiveProcRef", X0)
		},
	},
	distsys.MPCalCriticalSection{
		Name: "RecursiveProcRef.Error",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrProcedureFallthrough
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Arch1.Arch1lbl",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			f := iface.RequireArchetypeResource("Arch1.f")
			e := iface.ReadArchetypeResourceLocal("Arch1.e")
			var resourceRead tla.Value
			resourceRead, err = iface.Read(f, nil)
			if err != nil {
				return err
			}
			return iface.Call("Proc1", "Arch1.Done", e, resourceRead)
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Arch1.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var Arch1 = distsys.MPCalArchetype{
	Name:              "Arch1",
	Label:             "Arch1.Arch1lbl",
	RequiredRefParams: []string{"Arch1.e"},
	RequiredValParams: []string{"Arch1.f"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
