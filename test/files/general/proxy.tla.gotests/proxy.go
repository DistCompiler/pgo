package proxy

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

func FAIL(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(100)
}
func NUM_NODES(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(distsys.TLA_PlusSymbol(iface.GetConstant("NUM_SERVERS")(), iface.GetConstant("NUM_CLIENTS")()), distsys.NewTLANumber(1))
}
func ProxyID(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return NUM_NODES(iface)
}
func REQ_MSG_TYP(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}
func RESP_MSG_TYP(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}
func PROXY_REQ_MSG_TYP(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}
func PROXY_RESP_MSG_TYP(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(4)
}
func NODE_SET(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.NewTLANumber(1), NUM_NODES(iface))
}
func SERVER_SET(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.NewTLANumber(1), iface.GetConstant("NUM_SERVERS")())
}
func CLIENT_SET(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(iface.GetConstant("NUM_SERVERS")(), distsys.NewTLANumber(1)), distsys.TLA_PlusSymbol(iface.GetConstant("NUM_SERVERS")(), iface.GetConstant("NUM_CLIENTS")()))
}
func MSG_TYP_SET(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLASet(REQ_MSG_TYP(iface), RESP_MSG_TYP(iface), PROXY_REQ_MSG_TYP(iface), PROXY_RESP_MSG_TYP(iface))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AProxy.proxyLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if distsys.TLA_TRUE.AsBool() {
				return iface.Goto("AProxy.rcvMsgFromClient")
			} else {
				return iface.Goto("AProxy.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.rcvMsgFromClient",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AProxy.msg")
			net, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			var exprRead distsys.TLAValue
			exprRead, err = iface.Read(net, []distsys.TLAValue{distsys.NewTLATuple(ProxyID(iface), REQ_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []distsys.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("AProxy.proxyMsg")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.proxyMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg0 := iface.RequireArchetypeResource("AProxy.msg")
			proxyResp := iface.RequireArchetypeResource("AProxy.proxyResp")
			idx := iface.RequireArchetypeResource("AProxy.idx")
			var condition distsys.TLAValue
			condition, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition0 distsys.TLAValue
			condition0, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if !distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("to")), ProxyID(iface)), distsys.TLA_EqualsSymbol(condition0.ApplyFunction(distsys.NewTLAString("typ")), REQ_MSG_TYP(iface))).AsBool() {
				return fmt.Errorf("%w: (((msg).to) = (ProxyID)) /\\ (((msg).typ) = (REQ_MSG_TYP))", distsys.ErrAssertionFailed)
			}
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
			err = iface.Write(proxyResp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), ProxyID(iface)},
				{distsys.NewTLAString("to"), exprRead0.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), FAIL(iface)},
				{distsys.NewTLAString("id"), exprRead1.ApplyFunction(distsys.NewTLAString("id"))},
				{distsys.NewTLAString("typ"), PROXY_RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			err = iface.Write(idx, []distsys.TLAValue{}, distsys.NewTLANumber(1))
			if err != nil {
				return err
			}
			return iface.Goto("AProxy.serversLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.serversLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx0 := iface.RequireArchetypeResource("AProxy.idx")
			var condition1 distsys.TLAValue
			condition1, err = iface.Read(idx0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition1, iface.GetConstant("NUM_SERVERS")()).AsBool() {
				return iface.Goto("AProxy.proxySendMsg")
			} else {
				return iface.Goto("AProxy.sendMsgToClient")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.proxySendMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			proxyMsg := iface.RequireArchetypeResource("AProxy.proxyMsg")
			idx1 := iface.RequireArchetypeResource("AProxy.idx")
			msg4 := iface.RequireArchetypeResource("AProxy.msg")
			net0, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AProxy.fd")
			if err != nil {
				return err
			}
			switch iface.Fairness("AProxy.proxySendMsg.0", 2) {
			case 0:
				var exprRead2 distsys.TLAValue
				exprRead2, err = iface.Read(idx1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead3 distsys.TLAValue
				exprRead3, err = iface.Read(msg4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead4 distsys.TLAValue
				exprRead4, err = iface.Read(msg4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(proxyMsg, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), ProxyID(iface)},
					{distsys.NewTLAString("to"), exprRead2},
					{distsys.NewTLAString("body"), exprRead3.ApplyFunction(distsys.NewTLAString("body"))},
					{distsys.NewTLAString("id"), exprRead4.ApplyFunction(distsys.NewTLAString("id"))},
					{distsys.NewTLAString("typ"), PROXY_REQ_MSG_TYP(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead5 distsys.TLAValue
				exprRead5, err = iface.Read(proxyMsg, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead distsys.TLAValue
				indexRead, err = iface.Read(proxyMsg, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net0, []distsys.TLAValue{distsys.NewTLATuple(indexRead.ApplyFunction(distsys.NewTLAString("to")), PROXY_REQ_MSG_TYP(iface))}, exprRead5)
				if err != nil {
					return err
				}
				return iface.Goto("AProxy.proxyRcvMsg")
			case 1:
				var condition2 distsys.TLAValue
				condition2, err = iface.Read(idx1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition3 distsys.TLAValue
				condition3, err = iface.Read(fd, []distsys.TLAValue{condition2})
				if err != nil {
					return err
				}
				if !condition3.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var exprRead6 distsys.TLAValue
				exprRead6, err = iface.Read(idx1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx1, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead6, distsys.NewTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AProxy.serversLoop")
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.proxyRcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			proxyResp0 := iface.RequireArchetypeResource("AProxy.proxyResp")
			net1, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			idx5 := iface.RequireArchetypeResource("AProxy.idx")
			msg6 := iface.RequireArchetypeResource("AProxy.msg")
			fd0, err := iface.RequireArchetypeResourceRef("AProxy.fd")
			if err != nil {
				return err
			}
			switch iface.Fairness("AProxy.proxyRcvMsg.0", 2) {
			case 0:
				var exprRead7 distsys.TLAValue
				exprRead7, err = iface.Read(net1, []distsys.TLAValue{distsys.NewTLATuple(ProxyID(iface), PROXY_RESP_MSG_TYP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(proxyResp0, []distsys.TLAValue{}, exprRead7)
				if err != nil {
					return err
				}
				var condition4 distsys.TLAValue
				condition4, err = iface.Read(proxyResp0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition5 distsys.TLAValue
				condition5, err = iface.Read(proxyResp0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition6 distsys.TLAValue
				condition6, err = iface.Read(idx5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition7 distsys.TLAValue
				condition7, err = iface.Read(proxyResp0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition8 distsys.TLAValue
				condition8, err = iface.Read(msg6, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition9 distsys.TLAValue
				condition9, err = iface.Read(proxyResp0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition4.ApplyFunction(distsys.NewTLAString("to")), ProxyID(iface)), distsys.TLA_EqualsSymbol(condition5.ApplyFunction(distsys.NewTLAString("from")), condition6)), distsys.TLA_EqualsSymbol(condition7.ApplyFunction(distsys.NewTLAString("id")), condition8.ApplyFunction(distsys.NewTLAString("id")))), distsys.TLA_EqualsSymbol(condition9.ApplyFunction(distsys.NewTLAString("typ")), PROXY_RESP_MSG_TYP(iface))).AsBool() {
					return fmt.Errorf("%w: (((((proxyResp).to) = (ProxyID)) /\\ (((proxyResp).from) = (idx))) /\\ (((proxyResp).id) = ((msg).id))) /\\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP))", distsys.ErrAssertionFailed)
				}
				return iface.Goto("AProxy.sendMsgToClient")
			case 1:
				var condition10 distsys.TLAValue
				condition10, err = iface.Read(idx5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition11 distsys.TLAValue
				condition11, err = iface.Read(fd0, []distsys.TLAValue{condition10})
				if err != nil {
					return err
				}
				if !condition11.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var exprRead8 distsys.TLAValue
				exprRead8, err = iface.Read(idx5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx5, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead8, distsys.NewTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AProxy.serversLoop")
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.sendMsgToClient",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp := iface.RequireArchetypeResource("AProxy.resp")
			msg7 := iface.RequireArchetypeResource("AProxy.msg")
			proxyResp5 := iface.RequireArchetypeResource("AProxy.proxyResp")
			net2, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			var exprRead9 distsys.TLAValue
			exprRead9, err = iface.Read(msg7, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead10 distsys.TLAValue
			exprRead10, err = iface.Read(proxyResp5, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead11 distsys.TLAValue
			exprRead11, err = iface.Read(proxyResp5, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), ProxyID(iface)},
				{distsys.NewTLAString("to"), exprRead9.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead10.ApplyFunction(distsys.NewTLAString("body"))},
				{distsys.NewTLAString("id"), exprRead11.ApplyFunction(distsys.NewTLAString("id"))},
				{distsys.NewTLAString("typ"), RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead12 distsys.TLAValue
			exprRead12, err = iface.Read(resp, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err = iface.Read(resp, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead1 distsys.TLAValue
			indexRead1, err = iface.Read(resp, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net2, []distsys.TLAValue{distsys.NewTLATuple(indexRead0.ApplyFunction(distsys.NewTLAString("to")), indexRead1.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead12)
			if err != nil {
				return err
			}
			return iface.Goto("AProxy.proxyLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			if distsys.TLA_TRUE.AsBool() {
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.Fairness("AServer.serverLoop.0", 2) {
					case 0:
						// skip
						return iface.Goto("AServer.serverRcvMsg")
					case 1:
						err = iface.Write(netEnabled, []distsys.TLAValue{iface.Self()}, distsys.TLA_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AServer.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AServer.serverRcvMsg")
				}
				// no statements
			} else {
				return iface.Goto("AServer.failLabel")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverRcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg8 := iface.RequireArchetypeResource("AServer.msg")
			net3, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			netEnabled0, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			var exprRead13 distsys.TLAValue
			exprRead13, err = iface.Read(net3, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(msg8, []distsys.TLAValue{}, exprRead13)
			if err != nil {
				return err
			}
			var condition12 distsys.TLAValue
			condition12, err = iface.Read(msg8, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition13 distsys.TLAValue
			condition13, err = iface.Read(msg8, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition14 distsys.TLAValue
			condition14, err = iface.Read(msg8, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if !distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition12.ApplyFunction(distsys.NewTLAString("to")), iface.Self()), distsys.TLA_EqualsSymbol(condition13.ApplyFunction(distsys.NewTLAString("from")), ProxyID(iface))), distsys.TLA_EqualsSymbol(condition14.ApplyFunction(distsys.NewTLAString("typ")), PROXY_REQ_MSG_TYP(iface))).AsBool() {
				return fmt.Errorf("%w: ((((msg).to) = (self)) /\\ (((msg).from) = (ProxyID))) /\\ (((msg).typ) = (PROXY_REQ_MSG_TYP))", distsys.ErrAssertionFailed)
			}
			if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
				switch iface.Fairness("AServer.serverRcvMsg.0", 2) {
				case 0:
					// skip
					return iface.Goto("AServer.serverSendMsg")
				case 1:
					err = iface.Write(netEnabled0, []distsys.TLAValue{iface.Self()}, distsys.TLA_FALSE)
					if err != nil {
						return err
					}
					return iface.Goto("AServer.failLabel")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AServer.serverSendMsg")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverSendMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp3 := iface.RequireArchetypeResource("AServer.resp")
			msg12 := iface.RequireArchetypeResource("AServer.msg")
			net4, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			netEnabled1, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			var exprRead14 distsys.TLAValue
			exprRead14, err = iface.Read(msg12, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead15 distsys.TLAValue
			exprRead15, err = iface.Read(msg12, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp3, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), iface.Self()},
				{distsys.NewTLAString("to"), exprRead14.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), iface.Self()},
				{distsys.NewTLAString("id"), exprRead15.ApplyFunction(distsys.NewTLAString("id"))},
				{distsys.NewTLAString("typ"), PROXY_RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead16 distsys.TLAValue
			exprRead16, err = iface.Read(resp3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead2 distsys.TLAValue
			indexRead2, err = iface.Read(resp3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead3 distsys.TLAValue
			indexRead3, err = iface.Read(resp3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net4, []distsys.TLAValue{distsys.NewTLATuple(indexRead2.ApplyFunction(distsys.NewTLAString("to")), indexRead3.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead16)
			if err != nil {
				return err
			}
			if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
				switch iface.Fairness("AServer.serverSendMsg.0", 2) {
				case 0:
					// skip
					return iface.Goto("AServer.serverLoop")
				case 1:
					err = iface.Write(netEnabled1, []distsys.TLAValue{iface.Self()}, distsys.TLA_FALSE)
					if err != nil {
						return err
					}
					return iface.Goto("AServer.failLabel")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AServer.serverLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.failLabel",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd1, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			err = iface.Write(fd1, []distsys.TLAValue{iface.Self()}, distsys.TLA_TRUE)
			if err != nil {
				return err
			}
			return iface.Goto("AServer.Done")
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
				return iface.Goto("AClient.clientSendReq")
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientSendReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req := iface.RequireArchetypeResource("AClient.req")
			net5, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			err = iface.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), iface.Self()},
				{distsys.NewTLAString("to"), ProxyID(iface)},
				{distsys.NewTLAString("body"), iface.Self()},
				{distsys.NewTLAString("id"), distsys.NewTLANumber(0)},
				{distsys.NewTLAString("typ"), REQ_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead17 distsys.TLAValue
			exprRead17, err = iface.Read(req, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead4 distsys.TLAValue
			indexRead4, err = iface.Read(req, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead5 distsys.TLAValue
			indexRead5, err = iface.Read(req, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net5, []distsys.TLAValue{distsys.NewTLATuple(indexRead4.ApplyFunction(distsys.NewTLAString("to")), indexRead5.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead17)
			if err != nil {
				return err
			}
			var toPrint distsys.TLAValue
			toPrint, err = iface.Read(req, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			distsys.NewTLATuple(distsys.NewTLAString("CLIENT START"), toPrint).PCalPrint()
			return iface.Goto("AClient.clientRcvResp")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientRcvResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp7 := iface.RequireArchetypeResource("AClient.resp")
			net6, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var exprRead18 distsys.TLAValue
			exprRead18, err = iface.Read(net6, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), RESP_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(resp7, []distsys.TLAValue{}, exprRead18)
			if err != nil {
				return err
			}
			var condition15 distsys.TLAValue
			condition15, err = iface.Read(resp7, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition16 distsys.TLAValue
			condition16, err = iface.Read(resp7, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition17 distsys.TLAValue
			condition17, err = iface.Read(resp7, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if !distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition15.ApplyFunction(distsys.NewTLAString("to")), iface.Self()), distsys.TLA_EqualsSymbol(condition16.ApplyFunction(distsys.NewTLAString("id")), distsys.NewTLANumber(0))), distsys.TLA_EqualsSymbol(condition17.ApplyFunction(distsys.NewTLAString("typ")), RESP_MSG_TYP(iface))).AsBool() {
				return fmt.Errorf("%w: ((((resp).to) = (self)) /\\ (((resp).id) = (0))) /\\ (((resp).typ) = (RESP_MSG_TYP))", distsys.ErrAssertionFailed)
			}
			var toPrint0 distsys.TLAValue
			toPrint0, err = iface.Read(resp7, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			distsys.NewTLATuple(distsys.NewTLAString("CLIENT RESP"), toPrint0).PCalPrint()
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

var AProxy = distsys.MPCalArchetype{
	Name:              "AProxy",
	Label:             "AProxy.proxyLoop",
	RequiredRefParams: []string{"AProxy.net", "AProxy.fd"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AProxy.msg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.proxyMsg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.idx", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.resp", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.proxyResp", distsys.TLAValue{})
	},
}

var AServer = distsys.MPCalArchetype{
	Name:              "AServer",
	Label:             "AServer.serverLoop",
	RequiredRefParams: []string{"AServer.net", "AServer.netEnabled", "AServer.fd"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.msg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AServer.resp", distsys.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.net"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", distsys.TLAValue{})
	},
}
