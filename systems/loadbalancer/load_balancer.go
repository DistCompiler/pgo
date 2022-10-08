package loadbalancer

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func NUM_NODES(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_CLIENTS")(), iface.GetConstant("NUM_SERVERS")()), tla.MakeTLANumber(1))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ALoadBalancer.main",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
				return iface.Goto("ALoadBalancer.rcvMsg")
			} else {
				return iface.Goto("ALoadBalancer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ALoadBalancer.rcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("ALoadBalancer.msg")
			mailboxes, err := iface.RequireArchetypeResourceRef("ALoadBalancer.mailboxes")
			if err != nil {
				return err
			}
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(mailboxes, []tla.TLAValue{iface.GetConstant("LoadBalancerId")()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []tla.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			var condition tla.TLAValue
			condition, err = iface.Read(msg, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("message_type")), iface.GetConstant("GET_PAGE")()).AsBool() {
				return fmt.Errorf("%w: ((msg).message_type) = (GET_PAGE)", distsys.ErrAssertionFailed)
			}
			return iface.Goto("ALoadBalancer.sendServer")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ALoadBalancer.sendServer",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			next := iface.RequireArchetypeResource("ALoadBalancer.next")
			mailboxes0, err := iface.RequireArchetypeResourceRef("ALoadBalancer.mailboxes")
			if err != nil {
				return err
			}
			msg1 := iface.RequireArchetypeResource("ALoadBalancer.msg")
			var exprRead0 tla.TLAValue
			exprRead0, err = iface.Read(next, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(next, []tla.TLAValue{}, tla.TLA_PlusSymbol(tla.TLA_PercentSymbol(exprRead0, iface.GetConstant("NUM_SERVERS")()), tla.MakeTLANumber(1)))
			if err != nil {
				return err
			}
			var exprRead1 tla.TLAValue
			exprRead1, err = iface.Read(next, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead2 tla.TLAValue
			exprRead2, err = iface.Read(msg1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead3 tla.TLAValue
			exprRead3, err = iface.Read(msg1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead tla.TLAValue
			indexRead, err = iface.Read(next, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mailboxes0, []tla.TLAValue{indexRead}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("message_id"), exprRead1},
				{tla.MakeTLAString("client_id"), exprRead2.ApplyFunction(tla.MakeTLAString("client_id"))},
				{tla.MakeTLAString("path"), exprRead3.ApplyFunction(tla.MakeTLAString("path"))},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ALoadBalancer.main")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ALoadBalancer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
				return iface.Goto("AServer.rcvReq")
			} else {
				return iface.Goto("AServer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.rcvReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg3 := iface.RequireArchetypeResource("AServer.msg")
			mailboxes1, err := iface.RequireArchetypeResourceRef("AServer.mailboxes")
			if err != nil {
				return err
			}
			var exprRead4 tla.TLAValue
			exprRead4, err = iface.Read(mailboxes1, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg3, []tla.TLAValue{}, exprRead4)
			if err != nil {
				return err
			}
			return iface.Goto("AServer.sendPage")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.sendPage",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			mailboxes2, err := iface.RequireArchetypeResourceRef("AServer.mailboxes")
			if err != nil {
				return err
			}
			msg4 := iface.RequireArchetypeResource("AServer.msg")
			file_system, err := iface.RequireArchetypeResourceRef("AServer.file_system")
			if err != nil {
				return err
			}
			var exprRead5 tla.TLAValue
			exprRead5, err = iface.Read(msg4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead6 tla.TLAValue
			exprRead6, err = iface.Read(file_system, []tla.TLAValue{exprRead5.ApplyFunction(tla.MakeTLAString("path"))})
			if err != nil {
				return err
			}
			var indexRead0 tla.TLAValue
			indexRead0, err = iface.Read(msg4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mailboxes2, []tla.TLAValue{indexRead0.ApplyFunction(tla.MakeTLAString("client_id"))}, exprRead6)
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
				return iface.Goto("AClient.clientRequest")
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req := iface.RequireArchetypeResource("AClient.req")
			instream, err := iface.RequireArchetypeResourceRef("AClient.instream")
			if err != nil {
				return err
			}
			mailboxes3, err := iface.RequireArchetypeResourceRef("AClient.mailboxes")
			if err != nil {
				return err
			}
			var exprRead7 tla.TLAValue
			exprRead7, err = iface.Read(instream, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(req, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("message_type"), iface.GetConstant("GET_PAGE")()},
				{tla.MakeTLAString("client_id"), iface.Self()},
				{tla.MakeTLAString("path"), exprRead7},
			}))
			if err != nil {
				return err
			}
			var exprRead8 tla.TLAValue
			exprRead8, err = iface.Read(req, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mailboxes3, []tla.TLAValue{iface.GetConstant("LoadBalancerId")()}, exprRead8)
			if err != nil {
				return err
			}
			return iface.Goto("AClient.clientReceive")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientReceive",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp := iface.RequireArchetypeResource("AClient.resp")
			mailboxes4, err := iface.RequireArchetypeResourceRef("AClient.mailboxes")
			if err != nil {
				return err
			}
			outstream, err := iface.RequireArchetypeResourceRef("AClient.outstream")
			if err != nil {
				return err
			}
			var exprRead9 tla.TLAValue
			exprRead9, err = iface.Read(mailboxes4, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []tla.TLAValue{}, exprRead9)
			if err != nil {
				return err
			}
			var exprRead10 tla.TLAValue
			exprRead10, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(outstream, []tla.TLAValue{}, exprRead10)
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

var ALoadBalancer = distsys.MPCalArchetype{
	Name:              "ALoadBalancer",
	Label:             "ALoadBalancer.main",
	RequiredRefParams: []string{"ALoadBalancer.mailboxes"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ALoadBalancer.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("ALoadBalancer.next", tla.MakeTLANumber(0))
	},
}

var AServer = distsys.MPCalArchetype{
	Name:              "AServer",
	Label:             "AServer.serverLoop",
	RequiredRefParams: []string{"AServer.mailboxes", "AServer.file_system"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.msg", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.mailboxes", "AClient.instream", "AClient.outstream"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
	},
}
