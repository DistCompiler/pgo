package bug2

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AEchoServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
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
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(net, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), tla.MakeTLANumber(1))})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []tla.TLAValue{}, exprRead)
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
			var exprRead0 tla.TLAValue
			exprRead0, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead1 tla.TLAValue
			exprRead1, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead2 tla.TLAValue
			exprRead2, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead tla.TLAValue
			indexRead, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead0 tla.TLAValue
			indexRead0, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net0, []tla.TLAValue{tla.MakeTLATuple(indexRead.ApplyFunction(tla.MakeTLAString("from")), indexRead0.ApplyFunction(tla.MakeTLAString("typ")))}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("to"), exprRead0.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), exprRead1.ApplyFunction(tla.MakeTLAString("body"))},
				{tla.MakeTLAString("typ"), exprRead2.ApplyFunction(tla.MakeTLAString("typ"))},
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
		iface.EnsureArchetypeResourceLocal("AEchoServer.msg", tla.TLAValue{})
	},
}
