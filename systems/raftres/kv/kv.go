package kv

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func Nil(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func ProposeMessage(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("prm")
}
func AcceptMessage(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("acm")
}
func ClientPutRequest(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("pq")
}
func ClientPutResponse(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("pp")
}
func ClientGetRequest(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("gq")
}
func ClientGetResponse(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("gp")
}
func Put(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("p")
}
func Get(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("g")
}
func ServerPropSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(7), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(8), iface.GetConstant("NumServers")()))
}
func ServerAcctSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(8), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(9), iface.GetConstant("NumServers")()))
}
func ServerSet(iface distsys.ArchetypeInterface) tla.Value {
	return ServerPropSet(iface)
}
func ClientSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(9), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(9), iface.GetConstant("NumServers")()), iface.GetConstant("NumClients")()))
}
func NodeSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleUnionSymbol(ServerSet(iface), ClientSet(iface))
}
func Key1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("key1")
}
func Key2(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("key2")
}
func Value1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("value1")
}
func KeySet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet()
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
			if tla.ModuleTRUE.AsBool() {
				var msgRead tla.Value
				msgRead, err = iface.Read(srvId, []tla.Value{})
				if err != nil {
					return err
				}
				var msgRead0 tla.Value
				msgRead0, err = iface.Read(net, []tla.Value{msgRead})
				if err != nil {
					return err
				}
				var msg tla.Value = msgRead0
				_ = msg
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint tla.Value
					toPrint, err = iface.Read(srvId, []tla.Value{})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ServerPropose"), toPrint, msg).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition tla.Value
				condition, err = iface.Read(srvId, []tla.Value{})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(msg.ApplyFunction(tla.MakeString("mdest")), condition).AsBool() {
					return fmt.Errorf("%w: ((msg).mdest) = (srvId)", distsys.ErrAssertionFailed)
				}
				var exprRead tla.Value
				exprRead, err = iface.Read(srvId, []tla.Value{})
				if err != nil {
					return err
				}
				err = iface.Write(propCh, []tla.Value{}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("mtype"), ProposeMessage(iface)},
					{tla.MakeString("mcmd"), tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("mmsg"), msg},
						{tla.MakeString("msrv"), exprRead},
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
			if tla.ModuleTRUE.AsBool() {
				var exprRead0 tla.Value
				exprRead0, err = iface.Read(srvId3, []tla.Value{})
				if err != nil {
					return err
				}
				var exprRead1 tla.Value
				exprRead1, err = iface.Read(acctCh, []tla.Value{exprRead0})
				if err != nil {
					return err
				}
				err = iface.Write(m, []tla.Value{}, exprRead1)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint0 tla.Value
					toPrint0, err = iface.Read(srvId3, []tla.Value{})
					if err != nil {
						return err
					}
					var toPrint1 tla.Value
					toPrint1, err = iface.Read(m, []tla.Value{})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ServerAccept"), toPrint0, toPrint1).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition0 tla.Value
				condition0, err = iface.Read(m, []tla.Value{})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition0.ApplyFunction(tla.MakeString("mtype")), AcceptMessage(iface)).AsBool() {
					return fmt.Errorf("%w: ((m).mtype) = (AcceptMessage)", distsys.ErrAssertionFailed)
				}
				var cmdRead tla.Value
				cmdRead, err = iface.Read(m, []tla.Value{})
				if err != nil {
					return err
				}
				var cmd tla.Value = cmdRead.ApplyFunction(tla.MakeString("mcmd"))
				_ = cmd
				var msg0 tla.Value = cmd.ApplyFunction(tla.MakeString("mmsg"))
				_ = msg0
				var srv tla.Value = cmd.ApplyFunction(tla.MakeString("msrv"))
				_ = srv
				if tla.ModuleEqualsSymbol(msg0.ApplyFunction(tla.MakeString("mtype")), ClientPutRequest(iface)).AsBool() {
					var exprRead2 tla.Value
					exprRead2, err = iface.Read(sm, []tla.Value{})
					if err != nil {
						return err
					}
					err = iface.Write(sm, []tla.Value{}, tla.ModuleDoubleAtSignSymbol(exprRead2, tla.ModuleColonGreaterThanSymbol(msg0.ApplyFunction(tla.MakeString("mkey")), msg0.ApplyFunction(tla.MakeString("mvalue")))))
					if err != nil {
						return err
					}
					var exprRead3 tla.Value
					exprRead3, err = iface.Read(smDomain, []tla.Value{})
					if err != nil {
						return err
					}
					err = iface.Write(smDomain, []tla.Value{}, tla.ModuleUnionSymbol(exprRead3, tla.MakeSet(msg0.ApplyFunction(tla.MakeString("mkey")))))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var condition1 tla.Value
				condition1, err = iface.Read(srvId3, []tla.Value{})
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(srv, condition1).AsBool() {
					var iRead tla.Value
					iRead, err = iface.Read(srvId3, []tla.Value{})
					if err != nil {
						return err
					}
					var i tla.Value = iRead
					_ = i
					var j tla.Value = msg0.ApplyFunction(tla.MakeString("msource"))
					_ = j
					var respType tla.Value = func() tla.Value {
						if tla.ModuleEqualsSymbol(msg0.ApplyFunction(tla.MakeString("mtype")), ClientPutRequest(iface)).AsBool() {
							return ClientPutResponse(iface)
						} else {
							return ClientGetResponse(iface)
						}
					}()
					_ = respType
					var respOkRead tla.Value
					respOkRead, err = iface.Read(smDomain, []tla.Value{})
					if err != nil {
						return err
					}
					var respOk tla.Value = tla.ModuleInSymbol(msg0.ApplyFunction(tla.MakeString("mkey")), respOkRead)
					_ = respOk
					var valueRead tla.Value
					valueRead, err = iface.Read(sm, []tla.Value{})
					if err != nil {
						return err
					}
					var value tla.Value = func() tla.Value {
						if respOk.AsBool() {
							return valueRead.ApplyFunction(msg0.ApplyFunction(tla.MakeString("mkey")))
						} else {
							return Nil(iface)
						}
					}()
					_ = value
					err = iface.Write(net0, []tla.Value{j}, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("mtype"), respType},
						{tla.MakeString("mresponse"), tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("idx"), msg0.ApplyFunction(tla.MakeString("midx"))},
							{tla.MakeString("key"), msg0.ApplyFunction(tla.MakeString("mkey"))},
							{tla.MakeString("value"), value},
							{tla.MakeString("ok"), respOk},
						})},
						{tla.MakeString("msource"), i},
						{tla.MakeString("mdest"), j},
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
			if tla.ModuleTRUE.AsBool() {
				var exprRead4 tla.Value
				exprRead4, err = iface.Read(reqCh, []tla.Value{})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.Value{}, exprRead4)
				if err != nil {
					return err
				}
				var exprRead5 tla.Value
				exprRead5, err = iface.Read(reqIdx, []tla.Value{})
				if err != nil {
					return err
				}
				err = iface.Write(reqIdx, []tla.Value{}, tla.ModulePlusSymbol(exprRead5, tla.MakeNumber(1)))
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
			var condition2 tla.Value
			condition2, err = iface.Read(server, []tla.Value{})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition2, Nil(iface)).AsBool() {
				var sRead = ServerSet(iface)
				if sRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var s tla.Value = sRead.SelectElement(iface.NextFairnessCounter("AClient.sndReq.1", uint(sRead.AsSet().Len())))
				_ = s
				err = iface.Write(server, []tla.Value{}, s)
				if err != nil {
					return err
				}
				// no statements
				// no statements
			} else {
				// no statements
			}
			var valueRead0 tla.Value
			valueRead0, err = iface.Read(req0, []tla.Value{})
			if err != nil {
				return err
			}
			var valueRead1 tla.Value
			valueRead1, err = iface.Read(req0, []tla.Value{})
			if err != nil {
				return err
			}
			var value0 tla.Value = func() tla.Value {
				if tla.ModuleEqualsSymbol(valueRead0.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
					return valueRead1.ApplyFunction(tla.MakeString("value"))
				} else {
					return Nil(iface)
				}
			}()
			_ = value0
			var mtypeRead tla.Value
			mtypeRead, err = iface.Read(req0, []tla.Value{})
			if err != nil {
				return err
			}
			var mtype tla.Value = func() tla.Value {
				if tla.ModuleEqualsSymbol(mtypeRead.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
					return ClientPutRequest(iface)
				} else {
					return ClientGetRequest(iface)
				}
			}()
			_ = mtype
			if iface.GetConstant("Debug")().AsBool() {
				var toPrint2 tla.Value
				toPrint2, err = iface.Read(server, []tla.Value{})
				if err != nil {
					return err
				}
				var toPrint3 tla.Value
				toPrint3, err = iface.Read(reqIdx1, []tla.Value{})
				if err != nil {
					return err
				}
				var toPrint4 tla.Value
				toPrint4, err = iface.Read(req0, []tla.Value{})
				if err != nil {
					return err
				}
				tla.MakeTuple(tla.MakeString("ClientSndReq"), iface.Self(), toPrint2, toPrint3, toPrint4).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
			case 0:
				var exprRead6 tla.Value
				exprRead6, err = iface.Read(req0, []tla.Value{})
				if err != nil {
					return err
				}
				var exprRead7 tla.Value
				exprRead7, err = iface.Read(reqIdx1, []tla.Value{})
				if err != nil {
					return err
				}
				var exprRead8 tla.Value
				exprRead8, err = iface.Read(server, []tla.Value{})
				if err != nil {
					return err
				}
				var indexRead tla.Value
				indexRead, err = iface.Read(server, []tla.Value{})
				if err != nil {
					return err
				}
				err = iface.Write(net1, []tla.Value{indexRead}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("mtype"), mtype},
					{tla.MakeString("mkey"), exprRead6.ApplyFunction(tla.MakeString("key"))},
					{tla.MakeString("mvalue"), value0},
					{tla.MakeString("midx"), exprRead7},
					{tla.MakeString("msource"), iface.Self()},
					{tla.MakeString("mdest"), exprRead8},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AClient.rcvResp")
			case 1:
				var condition3 tla.Value
				condition3, err = iface.Read(server, []tla.Value{})
				if err != nil {
					return err
				}
				var condition4 tla.Value
				condition4, err = iface.Read(fd, []tla.Value{condition3})
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
				var exprRead9 tla.Value
				exprRead9, err = iface.Read(net2, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(resp, []tla.Value{}, exprRead9)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint5 tla.Value
					toPrint5, err = iface.Read(server5, []tla.Value{})
					if err != nil {
						return err
					}
					var toPrint6 tla.Value
					toPrint6, err = iface.Read(reqIdx3, []tla.Value{})
					if err != nil {
						return err
					}
					var toPrint7 tla.Value
					toPrint7, err = iface.Read(resp, []tla.Value{})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ClientRcvResp"), iface.Self(), toPrint5, toPrint6, toPrint7).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition5 tla.Value
				condition5, err = iface.Read(resp, []tla.Value{})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition5.ApplyFunction(tla.MakeString("mdest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).mdest) = (self)", distsys.ErrAssertionFailed)
				}
				var condition6 tla.Value
				condition6, err = iface.Read(resp, []tla.Value{})
				if err != nil {
					return err
				}
				var condition7 tla.Value
				condition7, err = iface.Read(reqIdx3, []tla.Value{})
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition6.ApplyFunction(tla.MakeString("mresponse")).ApplyFunction(tla.MakeString("idx")), condition7).AsBool() {
					return iface.Goto("AClient.rcvResp")
				} else {
					var condition8 tla.Value
					condition8, err = iface.Read(req5, []tla.Value{})
					if err != nil {
						return err
					}
					var condition9 tla.Value
					condition9, err = iface.Read(resp, []tla.Value{})
					if err != nil {
						return err
					}
					var condition10 tla.Value
					condition10, err = iface.Read(req5, []tla.Value{})
					if err != nil {
						return err
					}
					var condition11 tla.Value
					condition11, err = iface.Read(resp, []tla.Value{})
					if err != nil {
						return err
					}
					var condition12 tla.Value
					condition12, err = iface.Read(resp, []tla.Value{})
					if err != nil {
						return err
					}
					var condition13 tla.Value
					condition13, err = iface.Read(reqIdx3, []tla.Value{})
					if err != nil {
						return err
					}
					var condition14 tla.Value
					condition14, err = iface.Read(resp, []tla.Value{})
					if err != nil {
						return err
					}
					var condition15 tla.Value
					condition15, err = iface.Read(req5, []tla.Value{})
					if err != nil {
						return err
					}
					if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(!tla.ModuleEqualsSymbol(condition8.ApplyFunction(tla.MakeString("type")), Get(iface)).AsBool() || tla.ModuleEqualsSymbol(condition9.ApplyFunction(tla.MakeString("mtype")), ClientGetResponse(iface)).AsBool()).AsBool() && tla.MakeBool(!tla.ModuleEqualsSymbol(condition10.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() || tla.ModuleEqualsSymbol(condition11.ApplyFunction(tla.MakeString("mtype")), ClientPutResponse(iface)).AsBool()).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition12.ApplyFunction(tla.MakeString("mresponse")).ApplyFunction(tla.MakeString("idx")), condition13).AsBool()).AsBool() && tla.ModuleEqualsSymbol(condition14.ApplyFunction(tla.MakeString("mresponse")).ApplyFunction(tla.MakeString("key")), condition15.ApplyFunction(tla.MakeString("key"))).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)))) /\\ ((((resp).mresponse).idx) = (reqIdx))) /\\ ((((resp).mresponse).key) = ((req).key))", distsys.ErrAssertionFailed)
					}
					var exprRead10 tla.Value
					exprRead10, err = iface.Read(resp, []tla.Value{})
					if err != nil {
						return err
					}
					err = iface.Write(respCh, []tla.Value{}, exprRead10)
					if err != nil {
						return err
					}
					if iface.GetConstant("Debug")().AsBool() {
						var toPrint8 tla.Value
						toPrint8, err = iface.Read(server5, []tla.Value{})
						if err != nil {
							return err
						}
						var toPrint9 tla.Value
						toPrint9, err = iface.Read(reqIdx3, []tla.Value{})
						if err != nil {
							return err
						}
						var toPrint10 tla.Value
						toPrint10, err = iface.Read(resp, []tla.Value{})
						if err != nil {
							return err
						}
						tla.MakeTuple(tla.MakeString("ClientRcvChDone"), iface.Self(), toPrint8, toPrint9, toPrint10).PCalPrint()
						return iface.Goto("AClient.clientLoop")
					} else {
						return iface.Goto("AClient.clientLoop")
					}
					// no statements
				}
				// no statements
			case 1:
				var condition16 tla.Value
				condition16, err = iface.Read(server5, []tla.Value{})
				if err != nil {
					return err
				}
				var condition17 tla.Value
				condition17, err = iface.Read(fd0, []tla.Value{condition16})
				if err != nil {
					return err
				}
				var condition18 tla.Value
				condition18, err = iface.Read(netLen, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				var condition19 tla.Value
				condition19, err = iface.Read(timeout, []tla.Value{})
				if err != nil {
					return err
				}
				if !tla.MakeBool(tla.MakeBool(condition17.AsBool() && tla.ModuleEqualsSymbol(condition18, tla.MakeNumber(0)).AsBool()).AsBool() || condition19.AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint11 tla.Value
					toPrint11, err = iface.Read(server5, []tla.Value{})
					if err != nil {
						return err
					}
					var toPrint12 tla.Value
					toPrint12, err = iface.Read(reqIdx3, []tla.Value{})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ClientTimeout"), iface.Self(), toPrint11, toPrint12).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(server5, []tla.Value{}, Nil(iface))
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
		iface.EnsureArchetypeResourceLocal("AServerAcct.m", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AServerAcct.sm", tla.MakeFunction([]tla.Value{KeySet(iface)}, func(args []tla.Value) tla.Value {
			var k tla.Value = args[0]
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
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.reqIdx", tla.MakeNumber(0))
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.Value{})
	},
}
