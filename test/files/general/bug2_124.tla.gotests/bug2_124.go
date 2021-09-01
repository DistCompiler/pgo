package bug2

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AEchoServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if distsys.TLA_TRUE.AsBool() {
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
			var exprRead distsys.TLAValue
			exprRead, err = iface.Read(net, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), distsys.NewTLANumber(1))})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []distsys.TLAValue{}, exprRead)
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
			var exprRead0 distsys.TLAValue
			exprRead0, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead1 distsys.TLAValue
			exprRead1, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead2 distsys.TLAValue
			exprRead2, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead distsys.TLAValue
			indexRead, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net0, []distsys.TLAValue{distsys.NewTLATuple(indexRead.ApplyFunction(distsys.NewTLAString("from")), indexRead0.ApplyFunction(distsys.NewTLAString("typ")))}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), iface.Self()},
				{distsys.NewTLAString("to"), exprRead0.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead1.ApplyFunction(distsys.NewTLAString("body"))},
				{distsys.NewTLAString("typ"), exprRead2.ApplyFunction(distsys.NewTLAString("typ"))},
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
		iface.EnsureArchetypeResourceLocal("AEchoServer.msg", distsys.TLAValue{})
	},
}
