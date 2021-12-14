package echo

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func ServerID(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func ClientID(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(ServerID(iface), ClientID(iface))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
				return iface.Goto("AServer.serverRcv")
			} else {
				return iface.Goto("AServer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverRcv",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req := iface.RequireArchetypeResource("AServer.req")
			net, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(net, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(req, []tla.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("AServer.serverSnd")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverSnd",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net0, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			req0 := iface.RequireArchetypeResource("AServer.req")
			var exprRead0 tla.TLAValue
			exprRead0, err = iface.Read(req0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead tla.TLAValue
			indexRead, err = iface.Read(req0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net0, []tla.TLAValue{indexRead.ApplyFunction(tla.MakeTLAString("from"))}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("body"), exprRead0.ApplyFunction(tla.MakeTLAString("body"))},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("AServer.serverLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
				return iface.Goto("AClient.clientSnd")
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientSnd",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req2 := iface.RequireArchetypeResource("AClient.req")
			in, err := iface.RequireArchetypeResourceRef("AClient.in")
			if err != nil {
				return err
			}
			net1, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var exprRead1 tla.TLAValue
			exprRead1, err = iface.Read(in, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(req2, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("body"), exprRead1},
			}))
			if err != nil {
				return err
			}
			var exprRead2 tla.TLAValue
			exprRead2, err = iface.Read(req2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net1, []tla.TLAValue{ServerID(iface)}, exprRead2)
			if err != nil {
				return err
			}
			return iface.Goto("AClient.clientRcv")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientRcv",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp := iface.RequireArchetypeResource("AClient.resp")
			net2, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			req4 := iface.RequireArchetypeResource("AClient.req")
			out, err := iface.RequireArchetypeResourceRef("AClient.out")
			if err != nil {
				return err
			}
			var exprRead3 tla.TLAValue
			exprRead3, err = iface.Read(net2, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []tla.TLAValue{}, exprRead3)
			if err != nil {
				return err
			}
			var condition tla.TLAValue
			condition, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition0 tla.TLAValue
			condition0, err = iface.Read(req4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("body")), condition0.ApplyFunction(tla.MakeTLAString("body"))).AsBool() {
				return fmt.Errorf("%w: ((resp).body) = ((req).body)", distsys.ErrAssertionFailed)
			}
			var exprRead4 tla.TLAValue
			exprRead4, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(out, []tla.TLAValue{}, exprRead4.ApplyFunction(tla.MakeTLAString("body")))
			if err != nil {
				return err
			}
			return iface.Goto("AClient.clientLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AServer = distsys.MPCalArchetype{
	Name:              "AServer",
	Label:             "AServer.serverLoop",
	RequiredRefParams: []string{"AServer.net"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.req", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.net", "AClient.in", "AClient.out"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
	},
}
