package kv

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func Nil(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
}
func ProposeMessage(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("prm")
}
func AcceptMessage(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("acm")
}
func ClientPutRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("pq")
}
func ClientPutResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("pp")
}
func ClientGetRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("gq")
}
func ClientGetResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("gp")
}
func Put(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("p")
}
func Get(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("g")
}
func ServerPropSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(7), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(8), iface.GetConstant("NumServers")()))
}
func ServerAcctSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(8), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(9), iface.GetConstant("NumServers")()))
}
func ServerSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return ServerPropSet(iface)
}
func ClientSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(9), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(9), iface.GetConstant("NumServers")()), iface.GetConstant("NumClients")()))
}
func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_UnionSymbol(ServerSet(iface), ClientSet(iface))
}
func Key1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key1")
}
func Key2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key2")
}
func Value1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value1")
}
func KeySet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet()
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServerProp.serverPropLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net, err := iface.RequireArchetypeResourceRef("AServerProp.net")
			if err != nil {
				return err
			}
			srvId := iface.RequireArchetypeResource("AServerProp.srvId")
			propCh, err := iface.RequireArchetypeResourceRef("AServerProp.propCh")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var msgRead tla.TLAValue
				msgRead, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var msgRead0 tla.TLAValue
				msgRead0, err = iface.Read(net, []tla.TLAValue{msgRead})
				if err != nil {
					return err
				}
				var msg tla.TLAValue = msgRead0
				_ = msg
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint tla.TLAValue
					toPrint, err = iface.Read(srvId, []tla.TLAValue{})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ServerPropose"), toPrint, msg).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition tla.TLAValue
				condition, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(msg.ApplyFunction(tla.MakeTLAString("mdest")), condition).AsBool() {
					return fmt.Errorf("%w: ((msg).mdest) = (srvId)", distsys.ErrAssertionFailed)
				}
				var exprRead tla.TLAValue
				exprRead, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(propCh, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("mtype"), ProposeMessage(iface)},
					{tla.MakeTLAString("mcmd"), tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("mmsg"), msg},
						{tla.MakeTLAString("msrv"), exprRead},
					})},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AServerProp.serverPropLoop")
				// no statements
			} else {
				return iface.Goto("AServerProp.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerProp.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAcct.serverAccLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m := iface.RequireArchetypeResource("AServerAcct.m")
			acctCh, err := iface.RequireArchetypeResourceRef("AServerAcct.acctCh")
			if err != nil {
				return err
			}
			srvId3 := iface.RequireArchetypeResource("AServerAcct.srvId")
			sm := iface.RequireArchetypeResource("AServerAcct.sm")
			smDomain := iface.RequireArchetypeResource("AServerAcct.smDomain")
			net0, err := iface.RequireArchetypeResourceRef("AServerAcct.net")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(srvId3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(acctCh, []tla.TLAValue{exprRead0})
				if err != nil {
					return err
				}
				err = iface.Write(m, []tla.TLAValue{}, exprRead1)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint0 tla.TLAValue
					toPrint0, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint1 tla.TLAValue
					toPrint1, err = iface.Read(m, []tla.TLAValue{})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ServerAccept"), toPrint0, toPrint1).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition0 tla.TLAValue
				condition0, err = iface.Read(m, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition0.ApplyFunction(tla.MakeTLAString("mtype")), AcceptMessage(iface)).AsBool() {
					return fmt.Errorf("%w: ((m).mtype) = (AcceptMessage)", distsys.ErrAssertionFailed)
				}
				var cmdRead tla.TLAValue
				cmdRead, err = iface.Read(m, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var cmd tla.TLAValue = cmdRead.ApplyFunction(tla.MakeTLAString("mcmd"))
				_ = cmd
				var msg0 tla.TLAValue = cmd.ApplyFunction(tla.MakeTLAString("mmsg"))
				_ = msg0
				var srv tla.TLAValue = cmd.ApplyFunction(tla.MakeTLAString("msrv"))
				_ = srv
				if tla.TLA_EqualsSymbol(msg0.ApplyFunction(tla.MakeTLAString("mtype")), ClientPutRequest(iface)).AsBool() {
					var exprRead2 tla.TLAValue
					exprRead2, err = iface.Read(sm, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(sm, []tla.TLAValue{}, tla.TLA_DoubleAtSignSymbol(exprRead2, tla.TLA_ColonGreaterThanSymbol(msg0.ApplyFunction(tla.MakeTLAString("mkey")), msg0.ApplyFunction(tla.MakeTLAString("mvalue")))))
					if err != nil {
						return err
					}
					var exprRead3 tla.TLAValue
					exprRead3, err = iface.Read(smDomain, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(smDomain, []tla.TLAValue{}, tla.TLA_UnionSymbol(exprRead3, tla.MakeTLASet(msg0.ApplyFunction(tla.MakeTLAString("mkey")))))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var condition1 tla.TLAValue
				condition1, err = iface.Read(srvId3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(srv, condition1).AsBool() {
					var iRead tla.TLAValue
					iRead, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var i tla.TLAValue = iRead
					_ = i
					var j tla.TLAValue = msg0.ApplyFunction(tla.MakeTLAString("msource"))
					_ = j
					var respType tla.TLAValue = func() tla.TLAValue {
						if tla.TLA_EqualsSymbol(msg0.ApplyFunction(tla.MakeTLAString("mtype")), ClientPutRequest(iface)).AsBool() {
							return ClientPutResponse(iface)
						} else {
							return ClientGetResponse(iface)
						}
					}()
					_ = respType
					var respOkRead tla.TLAValue
					respOkRead, err = iface.Read(smDomain, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var respOk tla.TLAValue = tla.TLA_InSymbol(msg0.ApplyFunction(tla.MakeTLAString("mkey")), respOkRead)
					_ = respOk
					var valueRead tla.TLAValue
					valueRead, err = iface.Read(sm, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var value tla.TLAValue = func() tla.TLAValue {
						if respOk.AsBool() {
							return valueRead.ApplyFunction(msg0.ApplyFunction(tla.MakeTLAString("mkey")))
						} else {
							return Nil(iface)
						}
					}()
					_ = value
					err = iface.Write(net0, []tla.TLAValue{j}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("mtype"), respType},
						{tla.MakeTLAString("mresponse"), tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("idx"), msg0.ApplyFunction(tla.MakeTLAString("midx"))},
							{tla.MakeTLAString("key"), msg0.ApplyFunction(tla.MakeTLAString("mkey"))},
							{tla.MakeTLAString("value"), value},
							{tla.MakeTLAString("ok"), respOk},
						})},
						{tla.MakeTLAString("msource"), i},
						{tla.MakeTLAString("mdest"), j},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AServerAcct.serverAccLoop")
					// no statements
				} else {
					return iface.Goto("AServerAcct.serverAccLoop")
				}
				// no statements
				// no statements
			} else {
				return iface.Goto("AServerAcct.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAcct.Done",
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
			reqCh, err := iface.RequireArchetypeResourceRef("AClient.reqCh")
			if err != nil {
				return err
			}
			reqIdx := iface.RequireArchetypeResource("AClient.reqIdx")
			if tla.TLA_TRUE.AsBool() {
				var exprRead4 tla.TLAValue
				exprRead4, err = iface.Read(reqCh, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.TLAValue{}, exprRead4)
				if err != nil {
					return err
				}
				var exprRead5 tla.TLAValue
				exprRead5, err = iface.Read(reqIdx, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(reqIdx, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead5, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AClient.sndReq")
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			server := iface.RequireArchetypeResource("AClient.server")
			req0 := iface.RequireArchetypeResource("AClient.req")
			reqIdx1 := iface.RequireArchetypeResource("AClient.reqIdx")
			net1, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			var condition2 tla.TLAValue
			condition2, err = iface.Read(server, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition2, Nil(iface)).AsBool() {
				var sRead = ServerSet(iface)
				if sRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var s tla.TLAValue = sRead.SelectElement(iface.NextFairnessCounter("AClient.sndReq.1", uint(sRead.AsSet().Len())))
				_ = s
				err = iface.Write(server, []tla.TLAValue{}, s)
				if err != nil {
					return err
				}
				// no statements
				// no statements
			} else {
				// no statements
			}
			var valueRead0 tla.TLAValue
			valueRead0, err = iface.Read(req0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var valueRead1 tla.TLAValue
			valueRead1, err = iface.Read(req0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var value0 tla.TLAValue = func() tla.TLAValue {
				if tla.TLA_EqualsSymbol(valueRead0.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
					return valueRead1.ApplyFunction(tla.MakeTLAString("value"))
				} else {
					return Nil(iface)
				}
			}()
			_ = value0
			var mtypeRead tla.TLAValue
			mtypeRead, err = iface.Read(req0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var mtype tla.TLAValue = func() tla.TLAValue {
				if tla.TLA_EqualsSymbol(mtypeRead.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
					return ClientPutRequest(iface)
				} else {
					return ClientGetRequest(iface)
				}
			}()
			_ = mtype
			if iface.GetConstant("Debug")().AsBool() {
				var toPrint2 tla.TLAValue
				toPrint2, err = iface.Read(server, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var toPrint3 tla.TLAValue
				toPrint3, err = iface.Read(reqIdx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var toPrint4 tla.TLAValue
				toPrint4, err = iface.Read(req0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				tla.MakeTLATuple(tla.MakeTLAString("ClientSndReq"), iface.Self(), toPrint2, toPrint3, toPrint4).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
			case 0:
				var exprRead6 tla.TLAValue
				exprRead6, err = iface.Read(req0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead7 tla.TLAValue
				exprRead7, err = iface.Read(reqIdx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead8 tla.TLAValue
				exprRead8, err = iface.Read(server, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead tla.TLAValue
				indexRead, err = iface.Read(server, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net1, []tla.TLAValue{indexRead}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("mtype"), mtype},
					{tla.MakeTLAString("mkey"), exprRead6.ApplyFunction(tla.MakeTLAString("key"))},
					{tla.MakeTLAString("mvalue"), value0},
					{tla.MakeTLAString("midx"), exprRead7},
					{tla.MakeTLAString("msource"), iface.Self()},
					{tla.MakeTLAString("mdest"), exprRead8},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AClient.rcvResp")
			case 1:
				var condition3 tla.TLAValue
				condition3, err = iface.Read(server, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition4 tla.TLAValue
				condition4, err = iface.Read(fd, []tla.TLAValue{condition3})
				if err != nil {
					return err
				}
				if !condition4.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				return iface.Goto("AClient.rcvResp")
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.rcvResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp := iface.RequireArchetypeResource("AClient.resp")
			net2, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			server5 := iface.RequireArchetypeResource("AClient.server")
			reqIdx3 := iface.RequireArchetypeResource("AClient.reqIdx")
			req5 := iface.RequireArchetypeResource("AClient.req")
			respCh, err := iface.RequireArchetypeResourceRef("AClient.respCh")
			if err != nil {
				return err
			}
			fd0, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			netLen, err := iface.RequireArchetypeResourceRef("AClient.netLen")
			if err != nil {
				return err
			}
			timeout, err := iface.RequireArchetypeResourceRef("AClient.timeout")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AClient.rcvResp.0", 2) {
			case 0:
				var exprRead9 tla.TLAValue
				exprRead9, err = iface.Read(net2, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(resp, []tla.TLAValue{}, exprRead9)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint5 tla.TLAValue
					toPrint5, err = iface.Read(server5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint6 tla.TLAValue
					toPrint6, err = iface.Read(reqIdx3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint7 tla.TLAValue
					toPrint7, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ClientRcvResp"), iface.Self(), toPrint5, toPrint6, toPrint7).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition5 tla.TLAValue
				condition5, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition5.ApplyFunction(tla.MakeTLAString("mdest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).mdest) = (self)", distsys.ErrAssertionFailed)
				}
				var condition6 tla.TLAValue
				condition6, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition7 tla.TLAValue
				condition7, err = iface.Read(reqIdx3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition6.ApplyFunction(tla.MakeTLAString("mresponse")).ApplyFunction(tla.MakeTLAString("idx")), condition7).AsBool() {
					return iface.Goto("AClient.rcvResp")
				} else {
					var condition8 tla.TLAValue
					condition8, err = iface.Read(req5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition9 tla.TLAValue
					condition9, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition10 tla.TLAValue
					condition10, err = iface.Read(req5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition11 tla.TLAValue
					condition11, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition12 tla.TLAValue
					condition12, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition13 tla.TLAValue
					condition13, err = iface.Read(reqIdx3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition14 tla.TLAValue
					condition14, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition15 tla.TLAValue
					condition15, err = iface.Read(req5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(!tla.TLA_EqualsSymbol(condition8.ApplyFunction(tla.MakeTLAString("type")), Get(iface)).AsBool() || tla.TLA_EqualsSymbol(condition9.ApplyFunction(tla.MakeTLAString("mtype")), ClientGetResponse(iface)).AsBool()).AsBool() && tla.MakeTLABool(!tla.TLA_EqualsSymbol(condition10.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() || tla.TLA_EqualsSymbol(condition11.ApplyFunction(tla.MakeTLAString("mtype")), ClientPutResponse(iface)).AsBool()).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition12.ApplyFunction(tla.MakeTLAString("mresponse")).ApplyFunction(tla.MakeTLAString("idx")), condition13).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition14.ApplyFunction(tla.MakeTLAString("mresponse")).ApplyFunction(tla.MakeTLAString("key")), condition15.ApplyFunction(tla.MakeTLAString("key"))).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)))) /\\ ((((resp).mresponse).idx) = (reqIdx))) /\\ ((((resp).mresponse).key) = ((req).key))", distsys.ErrAssertionFailed)
					}
					var exprRead10 tla.TLAValue
					exprRead10, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(respCh, []tla.TLAValue{}, exprRead10)
					if err != nil {
						return err
					}
					if iface.GetConstant("Debug")().AsBool() {
						var toPrint8 tla.TLAValue
						toPrint8, err = iface.Read(server5, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var toPrint9 tla.TLAValue
						toPrint9, err = iface.Read(reqIdx3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var toPrint10 tla.TLAValue
						toPrint10, err = iface.Read(resp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						tla.MakeTLATuple(tla.MakeTLAString("ClientRcvChDone"), iface.Self(), toPrint8, toPrint9, toPrint10).PCalPrint()
						return iface.Goto("AClient.clientLoop")
					} else {
						return iface.Goto("AClient.clientLoop")
					}
					// no statements
				}
				// no statements
			case 1:
				var condition16 tla.TLAValue
				condition16, err = iface.Read(server5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition17 tla.TLAValue
				condition17, err = iface.Read(fd0, []tla.TLAValue{condition16})
				if err != nil {
					return err
				}
				var condition18 tla.TLAValue
				condition18, err = iface.Read(netLen, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				var condition19 tla.TLAValue
				condition19, err = iface.Read(timeout, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(tla.MakeTLABool(condition17.AsBool() && tla.TLA_EqualsSymbol(condition18, tla.MakeTLANumber(0)).AsBool()).AsBool() || condition19.AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint11 tla.TLAValue
					toPrint11, err = iface.Read(server5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint12 tla.TLAValue
					toPrint12, err = iface.Read(reqIdx3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ClientTimeout"), iface.Self(), toPrint11, toPrint12).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(server5, []tla.TLAValue{}, Nil(iface))
				if err != nil {
					return err
				}
				return iface.Goto("AClient.sndReq")
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AServerProp = distsys.MPCalArchetype{
	Name:              "AServerProp",
	Label:             "AServerProp.serverPropLoop",
	RequiredRefParams: []string{"AServerProp.net", "AServerProp.propCh"},
	RequiredValParams: []string{"AServerProp.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var AServerAcct = distsys.MPCalArchetype{
	Name:              "AServerAcct",
	Label:             "AServerAcct.serverAccLoop",
	RequiredRefParams: []string{"AServerAcct.net", "AServerAcct.acctCh"},
	RequiredValParams: []string{"AServerAcct.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerAcct.m", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AServerAcct.sm", tla.MakeTLAFunction([]tla.TLAValue{KeySet(iface)}, func(args []tla.TLAValue) tla.TLAValue {
			var k tla.TLAValue = args[0]
			_ = k
			return Nil(iface)
		}))
		iface.EnsureArchetypeResourceLocal("AServerAcct.smDomain", KeySet(iface))
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.net", "AClient.netLen", "AClient.fd", "AClient.reqCh", "AClient.respCh", "AClient.timeout"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.server", Nil(iface))
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.reqIdx", tla.MakeTLANumber(0))
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
	},
}
