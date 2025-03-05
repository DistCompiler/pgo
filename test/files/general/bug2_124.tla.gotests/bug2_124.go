package bug2

import (
	"fmt"
	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AEchoServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.ModuleTRUE.AsBool() {
				return iface.Goto("AEchoServer.rcvMsg")
			} else {
				return iface.Goto("AEchoServer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AEchoServer.rcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AEchoServer.msg")
			net, err := iface.RequireArchetypeResourceRef("AEchoServer.net")
			if err != nil {
				return err
			}
			var exprRead tla.Value
			exprRead, err = iface.Read(net, []tla.Value{tla.MakeTuple(iface.Self(), tla.MakeNumber(1))})
			if err != nil {
				return err
			}
			err = iface.Write(msg, nil, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("AEchoServer.sndMsg")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AEchoServer.sndMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net0, err := iface.RequireArchetypeResourceRef("AEchoServer.net")
			if err != nil {
				return err
			}
			msg0 := iface.RequireArchetypeResource("AEchoServer.msg")
			var exprRead0 tla.Value
			exprRead0, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			var exprRead1 tla.Value
			exprRead1, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			var exprRead2 tla.Value
			exprRead2, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			var indexRead tla.Value
			indexRead, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			var indexRead0 tla.Value
			indexRead0, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			err = iface.Write(net0, []tla.Value{tla.MakeTuple(indexRead.ApplyFunction(tla.MakeString("from")), indexRead0.ApplyFunction(tla.MakeString("typ")))}, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("to"), exprRead0.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), exprRead1.ApplyFunction(tla.MakeString("body"))},
				{tla.MakeString("typ"), exprRead2.ApplyFunction(tla.MakeString("typ"))},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("AEchoServer.serverLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AEchoServer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AEchoServer = distsys.MPCalArchetype{
	Name:              "AEchoServer",
	Label:             "AEchoServer.serverLoop",
	RequiredRefParams: []string{"AEchoServer.net"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AEchoServer.msg", tla.Value{})
	},
}
