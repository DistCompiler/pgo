package loadbalancer

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

func NUM_NODES(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(distsys.TLA_PlusSymbol(iface.GetConstant("NUM_CLIENTS")(), iface.GetConstant("NUM_SERVERS")()), distsys.NewTLANumber(1))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ALoadBalancer.main",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if distsys.TLA_TRUE.AsBool() {
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
			var exprRead distsys.TLAValue
			exprRead, err = iface.Read(mailboxes, []distsys.TLAValue{iface.GetConstant("LoadBalancerId")()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []distsys.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			var condition distsys.TLAValue
			condition, err = iface.Read(msg, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if !distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("message_type")), iface.GetConstant("GET_PAGE")()).AsBool() {
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
			var exprRead0 distsys.TLAValue
			exprRead0, err = iface.Read(next, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(next, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(distsys.TLA_PercentSymbol(exprRead0, iface.GetConstant("NUM_SERVERS")()), distsys.NewTLANumber(1)))
			if err != nil {
				return err
			}
			var exprRead1 distsys.TLAValue
			exprRead1, err = iface.Read(next, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead2 distsys.TLAValue
			exprRead2, err = iface.Read(msg1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead3 distsys.TLAValue
			exprRead3, err = iface.Read(msg1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead distsys.TLAValue
			indexRead, err = iface.Read(next, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mailboxes0, []distsys.TLAValue{indexRead}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("message_id"), exprRead1},
				{distsys.NewTLAString("client_id"), exprRead2.ApplyFunction(distsys.NewTLAString("client_id"))},
				{distsys.NewTLAString("path"), exprRead3.ApplyFunction(distsys.NewTLAString("path"))},
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
			if distsys.TLA_TRUE.AsBool() {
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
			var exprRead4 distsys.TLAValue
			exprRead4, err = iface.Read(mailboxes1, []distsys.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg3, []distsys.TLAValue{}, exprRead4)
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
			var exprRead5 distsys.TLAValue
			exprRead5, err = iface.Read(msg4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead6 distsys.TLAValue
			exprRead6, err = iface.Read(file_system, []distsys.TLAValue{exprRead5.ApplyFunction(distsys.NewTLAString("path"))})
			if err != nil {
				return err
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err = iface.Read(msg4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mailboxes2, []distsys.TLAValue{indexRead0.ApplyFunction(distsys.NewTLAString("client_id"))}, exprRead6)
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
			if distsys.TLA_TRUE.AsBool() {
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
			var exprRead7 distsys.TLAValue
			exprRead7, err = iface.Read(instream, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("message_type"), iface.GetConstant("GET_PAGE")()},
				{distsys.NewTLAString("client_id"), iface.Self()},
				{distsys.NewTLAString("path"), exprRead7},
			}))
			if err != nil {
				return err
			}
			var exprRead8 distsys.TLAValue
			exprRead8, err = iface.Read(req, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mailboxes3, []distsys.TLAValue{iface.GetConstant("LoadBalancerId")()}, exprRead8)
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
			var exprRead9 distsys.TLAValue
			exprRead9, err = iface.Read(mailboxes4, []distsys.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []distsys.TLAValue{}, exprRead9)
			if err != nil {
				return err
			}
			var exprRead10 distsys.TLAValue
			exprRead10, err = iface.Read(resp, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(outstream, []distsys.TLAValue{}, exprRead10)
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
		iface.EnsureArchetypeResourceLocal("ALoadBalancer.msg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("ALoadBalancer.next", distsys.NewTLANumber(0))
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
		iface.EnsureArchetypeResourceLocal("AServer.msg", distsys.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("AClient.req", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", distsys.TLAValue{})
	},
}
