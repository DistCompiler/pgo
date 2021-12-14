package proxy

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func FAIL(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(100)
}
func NUM_NODES(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_SERVERS")(), iface.GetConstant("NUM_CLIENTS")()), tla.MakeTLANumber(1))
}
func ProxyID(iface distsys.ArchetypeInterface) tla.TLAValue {
	return NUM_NODES(iface)
}
func REQ_MSG_TYP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func RESP_MSG_TYP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func PROXY_REQ_MSG_TYP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func PROXY_RESP_MSG_TYP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(4)
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), NUM_NODES(iface))
}
func SERVER_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NUM_SERVERS")())
}
func CLIENT_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_SERVERS")(), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(iface.GetConstant("NUM_SERVERS")(), iface.GetConstant("NUM_CLIENTS")()))
}
func MSG_TYP_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(REQ_MSG_TYP(iface), RESP_MSG_TYP(iface), PROXY_REQ_MSG_TYP(iface), PROXY_RESP_MSG_TYP(iface))
}
func MSG_ID_BOUND(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AProxy.proxyLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AProxy.msg")
			net, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			proxyResp := iface.RequireArchetypeResource("AProxy.proxyResp")
			idx := iface.RequireArchetypeResource("AProxy.idx")
			if tla.TLA_TRUE.AsBool() {
				var exprRead tla.TLAValue
				exprRead, err = iface.Read(net, []tla.TLAValue{tla.MakeTLATuple(ProxyID(iface), REQ_MSG_TYP(iface))})
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
				var condition0 tla.TLAValue
				condition0, err = iface.Read(msg, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("to")), ProxyID(iface)).AsBool() && tla.TLA_EqualsSymbol(condition0.ApplyFunction(tla.MakeTLAString("typ")), REQ_MSG_TYP(iface)).AsBool()).AsBool() {
					return fmt.Errorf("%w: (((msg).to) = (ProxyID)) /\\ (((msg).typ) = (REQ_MSG_TYP))", distsys.ErrAssertionFailed)
				}
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(msg, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(msg, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(proxyResp, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("from"), ProxyID(iface)},
					{tla.MakeTLAString("to"), exprRead0.ApplyFunction(tla.MakeTLAString("from"))},
					{tla.MakeTLAString("body"), FAIL(iface)},
					{tla.MakeTLAString("id"), exprRead1.ApplyFunction(tla.MakeTLAString("id"))},
					{tla.MakeTLAString("typ"), PROXY_RESP_MSG_TYP(iface)},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(idx, []tla.TLAValue{}, tla.MakeTLANumber(1))
				if err != nil {
					return err
				}
				return iface.Goto("AProxy.serversLoop")
			} else {
				return iface.Goto("AProxy.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.serversLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx0 := iface.RequireArchetypeResource("AProxy.idx")
			proxyMsg := iface.RequireArchetypeResource("AProxy.proxyMsg")
			msg4 := iface.RequireArchetypeResource("AProxy.msg")
			net0, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AProxy.fd")
			if err != nil {
				return err
			}
			var condition1 tla.TLAValue
			condition1, err = iface.Read(idx0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition1, iface.GetConstant("NUM_SERVERS")()).AsBool() {
				switch iface.NextFairnessCounter("AProxy.serversLoop.0", 2) {
				case 0:
					var exprRead2 tla.TLAValue
					exprRead2, err = iface.Read(idx0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead3 tla.TLAValue
					exprRead3, err = iface.Read(msg4, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead4 tla.TLAValue
					exprRead4, err = iface.Read(msg4, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(proxyMsg, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("from"), ProxyID(iface)},
						{tla.MakeTLAString("to"), exprRead2},
						{tla.MakeTLAString("body"), exprRead3.ApplyFunction(tla.MakeTLAString("body"))},
						{tla.MakeTLAString("id"), exprRead4.ApplyFunction(tla.MakeTLAString("id"))},
						{tla.MakeTLAString("typ"), PROXY_REQ_MSG_TYP(iface)},
					}))
					if err != nil {
						return err
					}
					var exprRead5 tla.TLAValue
					exprRead5, err = iface.Read(proxyMsg, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead tla.TLAValue
					indexRead, err = iface.Read(proxyMsg, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.TLAValue{tla.MakeTLATuple(indexRead.ApplyFunction(tla.MakeTLAString("to")), PROXY_REQ_MSG_TYP(iface))}, exprRead5)
					if err != nil {
						return err
					}
					return iface.Goto("AProxy.proxyRcvMsg")
				case 1:
					var condition2 tla.TLAValue
					condition2, err = iface.Read(idx0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition3 tla.TLAValue
					condition3, err = iface.Read(fd, []tla.TLAValue{condition2})
					if err != nil {
						return err
					}
					if !condition3.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var exprRead6 tla.TLAValue
					exprRead6, err = iface.Read(idx0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(idx0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead6, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					return iface.Goto("AProxy.serversLoop")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AProxy.sendMsgToClient")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProxy.proxyRcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net1, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			idx5 := iface.RequireArchetypeResource("AProxy.idx")
			msg6 := iface.RequireArchetypeResource("AProxy.msg")
			proxyResp0 := iface.RequireArchetypeResource("AProxy.proxyResp")
			fd0, err := iface.RequireArchetypeResourceRef("AProxy.fd")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AProxy.proxyRcvMsg.0", 2) {
			case 0:
				var tmpRead tla.TLAValue
				tmpRead, err = iface.Read(net1, []tla.TLAValue{tla.MakeTLATuple(ProxyID(iface), PROXY_RESP_MSG_TYP(iface))})
				if err != nil {
					return err
				}
				var tmp tla.TLAValue = tmpRead
				_ = tmp
				var condition4 tla.TLAValue
				condition4, err = iface.Read(idx5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition5 tla.TLAValue
				condition5, err = iface.Read(msg6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.MakeTLABool(tla.TLA_NotEqualsSymbol(tmp.ApplyFunction(tla.MakeTLAString("from")), condition4).AsBool() || tla.TLA_NotEqualsSymbol(tmp.ApplyFunction(tla.MakeTLAString("id")), condition5.ApplyFunction(tla.MakeTLAString("id"))).AsBool()).AsBool() {
					return iface.Goto("AProxy.proxyRcvMsg")
				} else {
					err = iface.Write(proxyResp0, []tla.TLAValue{}, tmp)
					if err != nil {
						return err
					}
					var condition6 tla.TLAValue
					condition6, err = iface.Read(proxyResp0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition7 tla.TLAValue
					condition7, err = iface.Read(proxyResp0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition8 tla.TLAValue
					condition8, err = iface.Read(idx5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition9 tla.TLAValue
					condition9, err = iface.Read(proxyResp0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition10 tla.TLAValue
					condition10, err = iface.Read(msg6, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition11 tla.TLAValue
					condition11, err = iface.Read(proxyResp0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition6.ApplyFunction(tla.MakeTLAString("to")), ProxyID(iface)).AsBool() && tla.TLA_EqualsSymbol(condition7.ApplyFunction(tla.MakeTLAString("from")), condition8).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition9.ApplyFunction(tla.MakeTLAString("id")), condition10.ApplyFunction(tla.MakeTLAString("id"))).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition11.ApplyFunction(tla.MakeTLAString("typ")), PROXY_RESP_MSG_TYP(iface)).AsBool()).AsBool() {
						return fmt.Errorf("%w: (((((proxyResp).to) = (ProxyID)) /\\ (((proxyResp).from) = (idx))) /\\ (((proxyResp).id) = ((msg).id))) /\\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP))", distsys.ErrAssertionFailed)
					}
					return iface.Goto("AProxy.sendMsgToClient")
				}
				// no statements
				// no statements
			case 1:
				var condition12 tla.TLAValue
				condition12, err = iface.Read(idx5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition13 tla.TLAValue
				condition13, err = iface.Read(fd0, []tla.TLAValue{condition12})
				if err != nil {
					return err
				}
				if !condition13.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var exprRead7 tla.TLAValue
				exprRead7, err = iface.Read(idx5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx5, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead7, tla.MakeTLANumber(1)))
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
			msg8 := iface.RequireArchetypeResource("AProxy.msg")
			proxyResp5 := iface.RequireArchetypeResource("AProxy.proxyResp")
			net2, err := iface.RequireArchetypeResourceRef("AProxy.net")
			if err != nil {
				return err
			}
			var exprRead8 tla.TLAValue
			exprRead8, err = iface.Read(msg8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead9 tla.TLAValue
			exprRead9, err = iface.Read(proxyResp5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead10 tla.TLAValue
			exprRead10, err = iface.Read(msg8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), ProxyID(iface)},
				{tla.MakeTLAString("to"), exprRead8.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), exprRead9.ApplyFunction(tla.MakeTLAString("body"))},
				{tla.MakeTLAString("id"), exprRead10.ApplyFunction(tla.MakeTLAString("id"))},
				{tla.MakeTLAString("typ"), RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead11 tla.TLAValue
			exprRead11, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead0 tla.TLAValue
			indexRead0, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead1 tla.TLAValue
			indexRead1, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net2, []tla.TLAValue{tla.MakeTLATuple(indexRead0.ApplyFunction(tla.MakeTLAString("to")), indexRead1.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead11)
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
			if tla.TLA_TRUE.AsBool() {
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AServer.serverLoop.0", 2) {
					case 0:
						// skip
						return iface.Goto("AServer.serverRcvMsg")
					case 1:
						err = iface.Write(netEnabled, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))}, tla.TLA_FALSE)
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
			msg10 := iface.RequireArchetypeResource("AServer.msg")
			net3, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			netEnabled0, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			var exprRead12 tla.TLAValue
			exprRead12, err = iface.Read(net3, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(msg10, []tla.TLAValue{}, exprRead12)
			if err != nil {
				return err
			}
			var condition14 tla.TLAValue
			condition14, err = iface.Read(msg10, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition15 tla.TLAValue
			condition15, err = iface.Read(msg10, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition16 tla.TLAValue
			condition16, err = iface.Read(msg10, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition14.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition15.ApplyFunction(tla.MakeTLAString("from")), ProxyID(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition16.ApplyFunction(tla.MakeTLAString("typ")), PROXY_REQ_MSG_TYP(iface)).AsBool()).AsBool() {
				return fmt.Errorf("%w: ((((msg).to) = (self)) /\\ (((msg).from) = (ProxyID))) /\\ (((msg).typ) = (PROXY_REQ_MSG_TYP))", distsys.ErrAssertionFailed)
			}
			if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
				switch iface.NextFairnessCounter("AServer.serverRcvMsg.0", 2) {
				case 0:
					// skip
					return iface.Goto("AServer.serverSendMsg")
				case 1:
					err = iface.Write(netEnabled0, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))}, tla.TLA_FALSE)
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
			msg14 := iface.RequireArchetypeResource("AServer.msg")
			net4, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			netEnabled1, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			var exprRead13 tla.TLAValue
			exprRead13, err = iface.Read(msg14, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead14 tla.TLAValue
			exprRead14, err = iface.Read(msg14, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp3, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("to"), exprRead13.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), iface.Self()},
				{tla.MakeTLAString("id"), exprRead14.ApplyFunction(tla.MakeTLAString("id"))},
				{tla.MakeTLAString("typ"), PROXY_RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead15 tla.TLAValue
			exprRead15, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead2 tla.TLAValue
			indexRead2, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead3 tla.TLAValue
			indexRead3, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net4, []tla.TLAValue{tla.MakeTLATuple(indexRead2.ApplyFunction(tla.MakeTLAString("to")), indexRead3.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead15)
			if err != nil {
				return err
			}
			if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
				switch iface.NextFairnessCounter("AServer.serverSendMsg.0", 2) {
				case 0:
					// skip
					return iface.Goto("AServer.serverLoop")
				case 1:
					err = iface.Write(netEnabled1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))}, tla.TLA_FALSE)
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
			err = iface.Write(fd1, []tla.TLAValue{iface.Self()}, tla.TLA_TRUE)
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
			req := iface.RequireArchetypeResource("AClient.req")
			input, err := iface.RequireArchetypeResourceRef("AClient.input")
			if err != nil {
				return err
			}
			reqId := iface.RequireArchetypeResource("AClient.reqId")
			net5, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			if iface.GetConstant("CLIENT_RUN")().AsBool() {
				var exprRead16 tla.TLAValue
				exprRead16, err = iface.Read(input, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead17 tla.TLAValue
				exprRead17, err = iface.Read(reqId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("from"), iface.Self()},
					{tla.MakeTLAString("to"), ProxyID(iface)},
					{tla.MakeTLAString("body"), exprRead16},
					{tla.MakeTLAString("id"), exprRead17},
					{tla.MakeTLAString("typ"), REQ_MSG_TYP(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead18 tla.TLAValue
				exprRead18, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead4 tla.TLAValue
				indexRead4, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead5 tla.TLAValue
				indexRead5, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net5, []tla.TLAValue{tla.MakeTLATuple(indexRead4.ApplyFunction(tla.MakeTLAString("to")), indexRead5.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead18)
				if err != nil {
					return err
				}
				return iface.Goto("AClient.clientRcvResp")
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
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
			reqId0 := iface.RequireArchetypeResource("AClient.reqId")
			output, err := iface.RequireArchetypeResourceRef("AClient.output")
			if err != nil {
				return err
			}
			var exprRead19 tla.TLAValue
			exprRead19, err = iface.Read(net6, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(resp7, []tla.TLAValue{}, exprRead19)
			if err != nil {
				return err
			}
			var condition17 tla.TLAValue
			condition17, err = iface.Read(resp7, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition18 tla.TLAValue
			condition18, err = iface.Read(resp7, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition19 tla.TLAValue
			condition19, err = iface.Read(reqId0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition20 tla.TLAValue
			condition20, err = iface.Read(resp7, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition21 tla.TLAValue
			condition21, err = iface.Read(resp7, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition17.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition18.ApplyFunction(tla.MakeTLAString("id")), condition19).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition20.ApplyFunction(tla.MakeTLAString("from")), ProxyID(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition21.ApplyFunction(tla.MakeTLAString("typ")), RESP_MSG_TYP(iface)).AsBool()).AsBool() {
				return fmt.Errorf("%w: (((((resp).to) = (self)) /\\ (((resp).id) = (reqId))) /\\ (((resp).from) = (ProxyID))) /\\ (((resp).typ) = (RESP_MSG_TYP))", distsys.ErrAssertionFailed)
			}
			var exprRead20 tla.TLAValue
			exprRead20, err = iface.Read(reqId0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(reqId0, []tla.TLAValue{}, tla.TLA_PercentSymbol(tla.TLA_PlusSymbol(exprRead20, tla.MakeTLANumber(1)), MSG_ID_BOUND(iface)))
			if err != nil {
				return err
			}
			var exprRead21 tla.TLAValue
			exprRead21, err = iface.Read(resp7, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(output, []tla.TLAValue{}, exprRead21)
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

var AProxy = distsys.MPCalArchetype{
	Name:              "AProxy",
	Label:             "AProxy.proxyLoop",
	RequiredRefParams: []string{"AProxy.net", "AProxy.fd"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AProxy.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.proxyMsg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.idx", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AProxy.proxyResp", tla.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("AServer.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AServer.resp", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.net", "AClient.input", "AClient.output"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.reqId", tla.MakeTLANumber(0))
	},
}
