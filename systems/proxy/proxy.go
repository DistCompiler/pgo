package proxy

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func FAIL(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(100)
}
func NUM_NODES(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModulePlusSymbol(tla.ModulePlusSymbol(iface.GetConstant("NUM_SERVERS")(), iface.GetConstant("NUM_CLIENTS")()), tla.MakeNumber(1))
}
func ProxyID(iface distsys.ArchetypeInterface) tla.Value {
	return NUM_NODES(iface)
}
func REQ_MSG_TYP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func RESP_MSG_TYP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func PROXY_REQ_MSG_TYP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(3)
}
func PROXY_RESP_MSG_TYP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(4)
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.MakeNumber(1), NUM_NODES(iface))
}
func SERVER_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NUM_SERVERS")())
}
func CLIENT_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(iface.GetConstant("NUM_SERVERS")(), tla.MakeNumber(1)), tla.ModulePlusSymbol(iface.GetConstant("NUM_SERVERS")(), iface.GetConstant("NUM_CLIENTS")()))
}
func MSG_TYP_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet(REQ_MSG_TYP(iface), RESP_MSG_TYP(iface), PROXY_REQ_MSG_TYP(iface), PROXY_RESP_MSG_TYP(iface))
}
func MSG_ID_BOUND(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
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
			if tla.ModuleTRUE.AsBool() {
				var exprRead tla.Value
				exprRead, err = iface.Read(net, []tla.Value{tla.MakeTuple(ProxyID(iface), REQ_MSG_TYP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, nil, exprRead)
				if err != nil {
					return err
				}
				var condition tla.Value
				condition, err = iface.Read(msg, nil)
				if err != nil {
					return err
				}
				var condition0 tla.Value
				condition0, err = iface.Read(msg, nil)
				if err != nil {
					return err
				}
				if !tla.MakeBool(tla.ModuleEqualsSymbol(condition.ApplyFunction(tla.MakeString("to")), ProxyID(iface)).AsBool() && tla.ModuleEqualsSymbol(condition0.ApplyFunction(tla.MakeString("typ")), REQ_MSG_TYP(iface)).AsBool()).AsBool() {
					return fmt.Errorf("%w: (((msg).to) = (ProxyID)) /\\ (((msg).typ) = (REQ_MSG_TYP))", distsys.ErrAssertionFailed)
				}
				var exprRead0 tla.Value
				exprRead0, err = iface.Read(msg, nil)
				if err != nil {
					return err
				}
				var exprRead1 tla.Value
				exprRead1, err = iface.Read(msg, nil)
				if err != nil {
					return err
				}
				err = iface.Write(proxyResp, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("from"), ProxyID(iface)},
					{tla.MakeString("to"), exprRead0.ApplyFunction(tla.MakeString("from"))},
					{tla.MakeString("body"), FAIL(iface)},
					{tla.MakeString("id"), exprRead1.ApplyFunction(tla.MakeString("id"))},
					{tla.MakeString("typ"), PROXY_RESP_MSG_TYP(iface)},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(idx, nil, tla.MakeNumber(1))
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
			var condition1 tla.Value
			condition1, err = iface.Read(idx0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition1, iface.GetConstant("NUM_SERVERS")()).AsBool() {
				switch iface.NextFairnessCounter("AProxy.serversLoop.0", 2) {
				case 0:
					var exprRead2 tla.Value
					exprRead2, err = iface.Read(idx0, nil)
					if err != nil {
						return err
					}
					var exprRead3 tla.Value
					exprRead3, err = iface.Read(msg4, nil)
					if err != nil {
						return err
					}
					var exprRead4 tla.Value
					exprRead4, err = iface.Read(msg4, nil)
					if err != nil {
						return err
					}
					err = iface.Write(proxyMsg, nil, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("from"), ProxyID(iface)},
						{tla.MakeString("to"), exprRead2},
						{tla.MakeString("body"), exprRead3.ApplyFunction(tla.MakeString("body"))},
						{tla.MakeString("id"), exprRead4.ApplyFunction(tla.MakeString("id"))},
						{tla.MakeString("typ"), PROXY_REQ_MSG_TYP(iface)},
					}))
					if err != nil {
						return err
					}
					var exprRead5 tla.Value
					exprRead5, err = iface.Read(proxyMsg, nil)
					if err != nil {
						return err
					}
					var indexRead tla.Value
					indexRead, err = iface.Read(proxyMsg, nil)
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.Value{tla.MakeTuple(indexRead.ApplyFunction(tla.MakeString("to")), PROXY_REQ_MSG_TYP(iface))}, exprRead5)
					if err != nil {
						return err
					}
					return iface.Goto("AProxy.proxyRcvMsg")
				case 1:
					var condition2 tla.Value
					condition2, err = iface.Read(idx0, nil)
					if err != nil {
						return err
					}
					var condition3 tla.Value
					condition3, err = iface.Read(fd, []tla.Value{condition2})
					if err != nil {
						return err
					}
					if !condition3.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var exprRead6 tla.Value
					exprRead6, err = iface.Read(idx0, nil)
					if err != nil {
						return err
					}
					err = iface.Write(idx0, nil, tla.ModulePlusSymbol(exprRead6, tla.MakeNumber(1)))
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
				var tmpRead tla.Value
				tmpRead, err = iface.Read(net1, []tla.Value{tla.MakeTuple(ProxyID(iface), PROXY_RESP_MSG_TYP(iface))})
				if err != nil {
					return err
				}
				var tmp tla.Value = tmpRead
				_ = tmp
				var condition4 tla.Value
				condition4, err = iface.Read(idx5, nil)
				if err != nil {
					return err
				}
				var condition5 tla.Value
				condition5, err = iface.Read(msg6, nil)
				if err != nil {
					return err
				}
				if tla.MakeBool(tla.ModuleNotEqualsSymbol(tmp.ApplyFunction(tla.MakeString("from")), condition4).AsBool() || tla.ModuleNotEqualsSymbol(tmp.ApplyFunction(tla.MakeString("id")), condition5.ApplyFunction(tla.MakeString("id"))).AsBool()).AsBool() {
					return iface.Goto("AProxy.proxyRcvMsg")
				} else {
					err = iface.Write(proxyResp0, nil, tmp)
					if err != nil {
						return err
					}
					var condition6 tla.Value
					condition6, err = iface.Read(proxyResp0, nil)
					if err != nil {
						return err
					}
					var condition7 tla.Value
					condition7, err = iface.Read(proxyResp0, nil)
					if err != nil {
						return err
					}
					var condition8 tla.Value
					condition8, err = iface.Read(idx5, nil)
					if err != nil {
						return err
					}
					var condition9 tla.Value
					condition9, err = iface.Read(proxyResp0, nil)
					if err != nil {
						return err
					}
					var condition10 tla.Value
					condition10, err = iface.Read(msg6, nil)
					if err != nil {
						return err
					}
					var condition11 tla.Value
					condition11, err = iface.Read(proxyResp0, nil)
					if err != nil {
						return err
					}
					if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition6.ApplyFunction(tla.MakeString("to")), ProxyID(iface)).AsBool() && tla.ModuleEqualsSymbol(condition7.ApplyFunction(tla.MakeString("from")), condition8).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition9.ApplyFunction(tla.MakeString("id")), condition10.ApplyFunction(tla.MakeString("id"))).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition11.ApplyFunction(tla.MakeString("typ")), PROXY_RESP_MSG_TYP(iface)).AsBool()).AsBool() {
						return fmt.Errorf("%w: (((((proxyResp).to) = (ProxyID)) /\\ (((proxyResp).from) = (idx))) /\\ (((proxyResp).id) = ((msg).id))) /\\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP))", distsys.ErrAssertionFailed)
					}
					return iface.Goto("AProxy.sendMsgToClient")
				}
				// no statements
				// no statements
			case 1:
				var condition12 tla.Value
				condition12, err = iface.Read(idx5, nil)
				if err != nil {
					return err
				}
				var condition13 tla.Value
				condition13, err = iface.Read(fd0, []tla.Value{condition12})
				if err != nil {
					return err
				}
				if !condition13.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var exprRead7 tla.Value
				exprRead7, err = iface.Read(idx5, nil)
				if err != nil {
					return err
				}
				err = iface.Write(idx5, nil, tla.ModulePlusSymbol(exprRead7, tla.MakeNumber(1)))
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
			var exprRead8 tla.Value
			exprRead8, err = iface.Read(msg8, nil)
			if err != nil {
				return err
			}
			var exprRead9 tla.Value
			exprRead9, err = iface.Read(proxyResp5, nil)
			if err != nil {
				return err
			}
			var exprRead10 tla.Value
			exprRead10, err = iface.Read(msg8, nil)
			if err != nil {
				return err
			}
			err = iface.Write(resp, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), ProxyID(iface)},
				{tla.MakeString("to"), exprRead8.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), exprRead9.ApplyFunction(tla.MakeString("body"))},
				{tla.MakeString("id"), exprRead10.ApplyFunction(tla.MakeString("id"))},
				{tla.MakeString("typ"), RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead11 tla.Value
			exprRead11, err = iface.Read(resp, nil)
			if err != nil {
				return err
			}
			var indexRead0 tla.Value
			indexRead0, err = iface.Read(resp, nil)
			if err != nil {
				return err
			}
			var indexRead1 tla.Value
			indexRead1, err = iface.Read(resp, nil)
			if err != nil {
				return err
			}
			err = iface.Write(net2, []tla.Value{tla.MakeTuple(indexRead0.ApplyFunction(tla.MakeString("to")), indexRead1.ApplyFunction(tla.MakeString("typ")))}, exprRead11)
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
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AServer.serverLoop.0", 2) {
					case 0:
						// skip
						return iface.Goto("AServer.serverRcvMsg")
					case 1:
						err = iface.Write(netEnabled, []tla.Value{tla.MakeTuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))}, tla.ModuleFALSE)
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
			var exprRead12 tla.Value
			exprRead12, err = iface.Read(net3, []tla.Value{tla.MakeTuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(msg10, nil, exprRead12)
			if err != nil {
				return err
			}
			var condition14 tla.Value
			condition14, err = iface.Read(msg10, nil)
			if err != nil {
				return err
			}
			var condition15 tla.Value
			condition15, err = iface.Read(msg10, nil)
			if err != nil {
				return err
			}
			var condition16 tla.Value
			condition16, err = iface.Read(msg10, nil)
			if err != nil {
				return err
			}
			if !tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition14.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() && tla.ModuleEqualsSymbol(condition15.ApplyFunction(tla.MakeString("from")), ProxyID(iface)).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition16.ApplyFunction(tla.MakeString("typ")), PROXY_REQ_MSG_TYP(iface)).AsBool()).AsBool() {
				return fmt.Errorf("%w: ((((msg).to) = (self)) /\\ (((msg).from) = (ProxyID))) /\\ (((msg).typ) = (PROXY_REQ_MSG_TYP))", distsys.ErrAssertionFailed)
			}
			if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
				switch iface.NextFairnessCounter("AServer.serverRcvMsg.0", 2) {
				case 0:
					// skip
					return iface.Goto("AServer.serverSendMsg")
				case 1:
					err = iface.Write(netEnabled0, []tla.Value{tla.MakeTuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))}, tla.ModuleFALSE)
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
			var exprRead13 tla.Value
			exprRead13, err = iface.Read(msg14, nil)
			if err != nil {
				return err
			}
			var exprRead14 tla.Value
			exprRead14, err = iface.Read(msg14, nil)
			if err != nil {
				return err
			}
			err = iface.Write(resp3, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("to"), exprRead13.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), iface.Self()},
				{tla.MakeString("id"), exprRead14.ApplyFunction(tla.MakeString("id"))},
				{tla.MakeString("typ"), PROXY_RESP_MSG_TYP(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead15 tla.Value
			exprRead15, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			var indexRead2 tla.Value
			indexRead2, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			var indexRead3 tla.Value
			indexRead3, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			err = iface.Write(net4, []tla.Value{tla.MakeTuple(indexRead2.ApplyFunction(tla.MakeString("to")), indexRead3.ApplyFunction(tla.MakeString("typ")))}, exprRead15)
			if err != nil {
				return err
			}
			if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
				switch iface.NextFairnessCounter("AServer.serverSendMsg.0", 2) {
				case 0:
					// skip
					return iface.Goto("AServer.serverLoop")
				case 1:
					err = iface.Write(netEnabled1, []tla.Value{tla.MakeTuple(iface.Self(), PROXY_REQ_MSG_TYP(iface))}, tla.ModuleFALSE)
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
			err = iface.Write(fd1, []tla.Value{iface.Self()}, tla.ModuleTRUE)
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
				var exprRead16 tla.Value
				exprRead16, err = iface.Read(input, nil)
				if err != nil {
					return err
				}
				var exprRead17 tla.Value
				exprRead17, err = iface.Read(reqId, nil)
				if err != nil {
					return err
				}
				err = iface.Write(req, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("from"), iface.Self()},
					{tla.MakeString("to"), ProxyID(iface)},
					{tla.MakeString("body"), exprRead16},
					{tla.MakeString("id"), exprRead17},
					{tla.MakeString("typ"), REQ_MSG_TYP(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead18 tla.Value
				exprRead18, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				var indexRead4 tla.Value
				indexRead4, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				var indexRead5 tla.Value
				indexRead5, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				err = iface.Write(net5, []tla.Value{tla.MakeTuple(indexRead4.ApplyFunction(tla.MakeString("to")), indexRead5.ApplyFunction(tla.MakeString("typ")))}, exprRead18)
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
			var exprRead19 tla.Value
			exprRead19, err = iface.Read(net6, []tla.Value{tla.MakeTuple(iface.Self(), RESP_MSG_TYP(iface))})
			if err != nil {
				return err
			}
			err = iface.Write(resp7, nil, exprRead19)
			if err != nil {
				return err
			}
			var condition17 tla.Value
			condition17, err = iface.Read(resp7, nil)
			if err != nil {
				return err
			}
			var condition18 tla.Value
			condition18, err = iface.Read(resp7, nil)
			if err != nil {
				return err
			}
			var condition19 tla.Value
			condition19, err = iface.Read(reqId0, nil)
			if err != nil {
				return err
			}
			var condition20 tla.Value
			condition20, err = iface.Read(resp7, nil)
			if err != nil {
				return err
			}
			var condition21 tla.Value
			condition21, err = iface.Read(resp7, nil)
			if err != nil {
				return err
			}
			if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition17.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() && tla.ModuleEqualsSymbol(condition18.ApplyFunction(tla.MakeString("id")), condition19).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition20.ApplyFunction(tla.MakeString("from")), ProxyID(iface)).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition21.ApplyFunction(tla.MakeString("typ")), RESP_MSG_TYP(iface)).AsBool()).AsBool() {
				return fmt.Errorf("%w: (((((resp).to) = (self)) /\\ (((resp).id) = (reqId))) /\\ (((resp).from) = (ProxyID))) /\\ (((resp).typ) = (RESP_MSG_TYP))", distsys.ErrAssertionFailed)
			}
			var exprRead20 tla.Value
			exprRead20, err = iface.Read(reqId0, nil)
			if err != nil {
				return err
			}
			err = iface.Write(reqId0, nil, tla.ModulePercentSymbol(tla.ModulePlusSymbol(exprRead20, tla.MakeNumber(1)), MSG_ID_BOUND(iface)))
			if err != nil {
				return err
			}
			var exprRead21 tla.Value
			exprRead21, err = iface.Read(resp7, nil)
			if err != nil {
				return err
			}
			err = iface.Write(output, nil, exprRead21)
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
		iface.EnsureArchetypeResourceLocal("AProxy.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AProxy.proxyMsg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AProxy.idx", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AProxy.resp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AProxy.proxyResp", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("AServer.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AServer.resp", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.reqId", tla.MakeNumber(0))
	},
}
