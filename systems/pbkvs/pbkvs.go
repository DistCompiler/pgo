package pbkvs

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func NUM_NODES(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
}
func CLIENT_SRC(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func PRIMARY_SRC(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func BACKUP_SRC(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(3)
}
func GET_REQ(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func GET_RESP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func PUT_REQ(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(3)
}
func PUT_RESP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(4)
}
func SYNC_REQ(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(5)
}
func SYNC_RESP(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(6)
}
func REQ_INDEX(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func RESP_INDEX(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func ACK_MSG_BODY(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeRecord([]tla.RecordField{
		{tla.MakeString("content"), tla.MakeString("ack-body")},
	})
}
func KEY1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("KEY1")
}
func VALUE1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("VALUE1")
}
func VALUE2(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("VALUE2")
}
func KEY_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet(KEY1(iface))
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_DotDotSymbol(tla.MakeNumber(1), NUM_NODES(iface))
}
func REPLICA_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_DotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NUM_REPLICAS")())
}
func CLIENT_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Symbol_DotDotSymbol(tla.Symbol_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeNumber(1)), tla.Symbol_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")()))
}
func MSG_INDEX_SET(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet(REQ_INDEX(iface), RESP_INDEX(iface))
}
func NULL(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			replicaSet := iface.RequireArchetypeResource("AReplica.replicaSet")
			idx := iface.RequireArchetypeResource("AReplica.idx")
			netEnabled, err := iface.RequireArchetypeResourceRef("AReplica.netEnabled")
			if err != nil {
				return err
			}
			if tla.Symbol_TRUE.AsBool() {
				err = iface.Write(replicaSet, nil, tla.Symbol_BackslashSymbol(REPLICA_SET(iface), tla.MakeSet(iface.Self())))
				if err != nil {
					return err
				}
				err = iface.Write(idx, nil, tla.MakeNumber(1))
				if err != nil {
					return err
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.replicaLoop.0", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.syncPrimary")
					case 1:
						err = iface.Write(netEnabled, []tla.Value{tla.MakeTuple(iface.Self(), REQ_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AReplica.syncPrimary")
				}
				// no statements
			} else {
				return iface.Goto("AReplica.failLabel")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.syncPrimary",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			primary, err := iface.RequireArchetypeResourceRef("AReplica.primary")
			if err != nil {
				return err
			}
			shouldSync := iface.RequireArchetypeResource("AReplica.shouldSync")
			var condition tla.Value
			condition, err = iface.Read(primary, nil)
			if err != nil {
				return err
			}
			var condition0 tla.Value
			condition0, err = iface.Read(shouldSync, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.Symbol_EqualsSymbol(condition, iface.Self()).AsBool() && condition0.AsBool()).AsBool() {
				err = iface.Write(shouldSync, nil, tla.Symbol_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.sndSyncReqLoop")
			} else {
				return iface.Goto("AReplica.rcvMsg")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndSyncReqLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx0 := iface.RequireArchetypeResource("AReplica.idx")
			repReq := iface.RequireArchetypeResource("AReplica.repReq")
			lastPutBody := iface.RequireArchetypeResource("AReplica.lastPutBody")
			net, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			netEnabled1, err := iface.RequireArchetypeResourceRef("AReplica.netEnabled")
			if err != nil {
				return err
			}
			var condition1 tla.Value
			condition1, err = iface.Read(idx0, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_LessThanOrEqualSymbol(condition1, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				var condition2 tla.Value
				condition2, err = iface.Read(idx0, nil)
				if err != nil {
					return err
				}
				if tla.Symbol_NotEqualsSymbol(condition2, iface.Self()).AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndSyncReqLoop.0", 2) {
					case 0:
						var exprRead0 tla.Value
						exprRead0, err = iface.Read(idx0, nil)
						if err != nil {
							return err
						}
						var exprRead1 tla.Value
						exprRead1, err = iface.Read(lastPutBody, nil)
						if err != nil {
							return err
						}
						err = iface.Write(repReq, nil, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("from"), iface.Self()},
							{tla.MakeString("to"), exprRead0},
							{tla.MakeString("body"), exprRead1},
							{tla.MakeString("srcTyp"), PRIMARY_SRC(iface)},
							{tla.MakeString("typ"), SYNC_REQ(iface)},
							{tla.MakeString("id"), tla.MakeNumber(3)},
						}))
						if err != nil {
							return err
						}
						var exprRead2 tla.Value
						exprRead2, err = iface.Read(repReq, nil)
						if err != nil {
							return err
						}
						var indexRead tla.Value
						indexRead, err = iface.Read(idx0, nil)
						if err != nil {
							return err
						}
						err = iface.Write(net, []tla.Value{tla.MakeTuple(indexRead, REQ_INDEX(iface))}, exprRead2)
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition3 tla.Value
						condition3, err = iface.Read(idx0, nil)
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
						// no statements
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead tla.Value
				exprRead, err = iface.Read(idx0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(idx0, nil, tla.Symbol_PlusSymbol(exprRead, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndSyncReqLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.sndSyncReqLoop")
					case 1:
						err = iface.Write(netEnabled1, []tla.Value{tla.MakeTuple(iface.Self(), REQ_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled1, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AReplica.sndSyncReqLoop")
				}
				// no statements
			} else {
				return iface.Goto("AReplica.rcvSyncRespLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvSyncRespLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			replicaSet0 := iface.RequireArchetypeResource("AReplica.replicaSet")
			repResp := iface.RequireArchetypeResource("AReplica.repResp")
			net0, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			fd0, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			lastPutBody0 := iface.RequireArchetypeResource("AReplica.lastPutBody")
			fs, err := iface.RequireArchetypeResourceRef("AReplica.fs")
			if err != nil {
				return err
			}
			idx7 := iface.RequireArchetypeResource("AReplica.idx")
			replica := iface.RequireArchetypeResource("AReplica.replica")
			netLen, err := iface.RequireArchetypeResourceRef("AReplica.netLen")
			if err != nil {
				return err
			}
			var condition5 tla.Value
			condition5, err = iface.Read(replicaSet0, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_GreaterThanSymbol(tla.Symbol_Cardinality(condition5), tla.MakeNumber(0)).AsBool() {
				switch iface.NextFairnessCounter("AReplica.rcvSyncRespLoop.0", 2) {
				case 0:
					var exprRead3 tla.Value
					exprRead3, err = iface.Read(net0, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					err = iface.Write(repResp, nil, exprRead3)
					if err != nil {
						return err
					}
					var condition6 tla.Value
					condition6, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition7 tla.Value
					condition7, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition8 tla.Value
					condition8, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition9 tla.Value
					condition9, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition10 tla.Value
					condition10, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition11 tla.Value
					condition11, err = iface.Read(replicaSet0, nil)
					if err != nil {
						return err
					}
					var condition12 tla.Value
					condition12, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition13 tla.Value
					condition13, err = iface.Read(fd0, []tla.Value{condition12.ApplyFunction(tla.MakeString("from"))})
					if err != nil {
						return err
					}
					if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.Symbol_EqualsSymbol(condition6.ApplyFunction(tla.MakeString("id")), tla.MakeNumber(3)).AsBool() && tla.Symbol_EqualsSymbol(condition7.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition8.ApplyFunction(tla.MakeString("srcTyp")), BACKUP_SRC(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition9.ApplyFunction(tla.MakeString("typ")), SYNC_RESP(iface)).AsBool()).AsBool() && tla.MakeBool(tla.Symbol_InSymbol(condition10.ApplyFunction(tla.MakeString("from")), condition11).AsBool() || condition13.AsBool()).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((((repResp).id) = (3)) /\\ (((repResp).to) = (self))) /\\ (((repResp).srcTyp) = (BACKUP_SRC))) /\\ (((repResp).typ) = (SYNC_RESP))) /\\ ((((repResp).from) \\in (replicaSet)) \\/ ((fd)[(repResp).from]))", distsys.ErrAssertionFailed)
					}
					var condition14 tla.Value
					condition14, err = iface.Read(repResp, nil)
					if err != nil {
						return err
					}
					var condition15 tla.Value
					condition15, err = iface.Read(lastPutBody0, nil)
					if err != nil {
						return err
					}
					if tla.Symbol_GreaterThanSymbol(condition14.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("versionNumber")), condition15.ApplyFunction(tla.MakeString("versionNumber"))).AsBool() {
						var exprRead4 tla.Value
						exprRead4, err = iface.Read(repResp, nil)
						if err != nil {
							return err
						}
						var indexRead0 tla.Value
						indexRead0, err = iface.Read(repResp, nil)
						if err != nil {
							return err
						}
						err = iface.Write(fs, []tla.Value{iface.Self(), indexRead0.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))}, exprRead4.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value")))
						if err != nil {
							return err
						}
						var exprRead5 tla.Value
						exprRead5, err = iface.Read(repResp, nil)
						if err != nil {
							return err
						}
						err = iface.Write(lastPutBody0, nil, exprRead5.ApplyFunction(tla.MakeString("body")))
						if err != nil {
							return err
						}
						err = iface.Write(replicaSet0, nil, tla.Symbol_BackslashSymbol(REPLICA_SET(iface), tla.MakeSet(iface.Self())))
						if err != nil {
							return err
						}
						err = iface.Write(idx7, nil, tla.MakeNumber(1))
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.sndSyncReqLoop")
					} else {
						var exprRead6 tla.Value
						exprRead6, err = iface.Read(replicaSet0, nil)
						if err != nil {
							return err
						}
						var exprRead7 tla.Value
						exprRead7, err = iface.Read(repResp, nil)
						if err != nil {
							return err
						}
						err = iface.Write(replicaSet0, nil, tla.Symbol_BackslashSymbol(exprRead6, tla.MakeSet(exprRead7.ApplyFunction(tla.MakeString("from")))))
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.rcvSyncRespLoop")
					}
					// no statements
				case 1:
					var exprRead8 tla.Value
					exprRead8, err = iface.Read(replicaSet0, nil)
					if err != nil {
						return err
					}
					err = iface.Write(replica, nil, tla.Choose(exprRead8, func(element tla.Value) bool {
						var r tla.Value = element
						_ = r
						return tla.Symbol_TRUE.AsBool()
					}))
					if err != nil {
						return err
					}
					var condition16 tla.Value
					condition16, err = iface.Read(replica, nil)
					if err != nil {
						return err
					}
					var condition17 tla.Value
					condition17, err = iface.Read(fd0, []tla.Value{condition16})
					if err != nil {
						return err
					}
					var condition18 tla.Value
					condition18, err = iface.Read(netLen, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					if !tla.MakeBool(condition17.AsBool() && tla.Symbol_EqualsSymbol(condition18, tla.MakeNumber(0)).AsBool()).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var exprRead9 tla.Value
					exprRead9, err = iface.Read(replicaSet0, nil)
					if err != nil {
						return err
					}
					var exprRead10 tla.Value
					exprRead10, err = iface.Read(replica, nil)
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet0, nil, tla.Symbol_BackslashSymbol(exprRead9, tla.MakeSet(exprRead10)))
					if err != nil {
						return err
					}
					return iface.Goto("AReplica.rcvSyncRespLoop")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AReplica.rcvMsg")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			primary0, err := iface.RequireArchetypeResourceRef("AReplica.primary")
			if err != nil {
				return err
			}
			shouldSync1 := iface.RequireArchetypeResource("AReplica.shouldSync")
			req := iface.RequireArchetypeResource("AReplica.req")
			net1, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			var condition19 tla.Value
			condition19, err = iface.Read(primary0, nil)
			if err != nil {
				return err
			}
			var condition20 tla.Value
			condition20, err = iface.Read(shouldSync1, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.Symbol_EqualsSymbol(condition19, iface.Self()).AsBool() && condition20.AsBool()).AsBool() {
				return iface.Goto("AReplica.syncPrimary")
			} else {
				var exprRead11 tla.Value
				exprRead11, err = iface.Read(net1, []tla.Value{tla.MakeTuple(iface.Self(), REQ_INDEX(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(req, nil, exprRead11)
				if err != nil {
					return err
				}
				if iface.GetConstant("DEBUG")().AsBool() {
					var toPrint tla.Value
					toPrint, err = iface.Read(req, nil)
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ServerRcvReq"), iface.Self(), toPrint).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition21 tla.Value
				condition21, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				if !tla.Symbol_EqualsSymbol(condition21.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((req).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition22 tla.Value
				condition22, err = iface.Read(primary0, nil)
				if err != nil {
					return err
				}
				var condition23 tla.Value
				condition23, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				if tla.MakeBool(tla.Symbol_EqualsSymbol(condition22, iface.Self()).AsBool() && tla.Symbol_EqualsSymbol(condition23.ApplyFunction(tla.MakeString("srcTyp")), CLIENT_SRC(iface)).AsBool()).AsBool() {
					return iface.Goto("AReplica.handlePrimary")
				} else {
					return iface.Goto("AReplica.handleBackup")
				}
				// no statements
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.handleBackup",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req3 := iface.RequireArchetypeResource("AReplica.req")
			respBody := iface.RequireArchetypeResource("AReplica.respBody")
			fs0, err := iface.RequireArchetypeResourceRef("AReplica.fs")
			if err != nil {
				return err
			}
			respTyp := iface.RequireArchetypeResource("AReplica.respTyp")
			lastPutBody2 := iface.RequireArchetypeResource("AReplica.lastPutBody")
			shouldSync2 := iface.RequireArchetypeResource("AReplica.shouldSync")
			resp := iface.RequireArchetypeResource("AReplica.resp")
			net2, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			fd2, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			if iface.GetConstant("DEBUG")().AsBool() {
				tla.MakeTuple(tla.MakeString("ServerHandleBackup"), iface.Self()).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			var condition24 tla.Value
			condition24, err = iface.Read(req3, nil)
			if err != nil {
				return err
			}
			if !tla.Symbol_EqualsSymbol(condition24.ApplyFunction(tla.MakeString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
				return fmt.Errorf("%w: ((req).srcTyp) = (PRIMARY_SRC)", distsys.ErrAssertionFailed)
			}
			var condition25 tla.Value
			condition25, err = iface.Read(req3, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_EqualsSymbol(condition25.ApplyFunction(tla.MakeString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead12 tla.Value
				exprRead12, err = iface.Read(req3, nil)
				if err != nil {
					return err
				}
				var exprRead13 tla.Value
				exprRead13, err = iface.Read(fs0, []tla.Value{iface.Self(), exprRead12.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("content"), exprRead13},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(respTyp, nil, GET_RESP(iface))
				if err != nil {
					return err
				}
				// no statements
			} else {
				var condition26 tla.Value
				condition26, err = iface.Read(req3, nil)
				if err != nil {
					return err
				}
				if tla.Symbol_EqualsSymbol(condition26.ApplyFunction(tla.MakeString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead14 tla.Value
					exprRead14, err = iface.Read(req3, nil)
					if err != nil {
						return err
					}
					var indexRead1 tla.Value
					indexRead1, err = iface.Read(req3, nil)
					if err != nil {
						return err
					}
					err = iface.Write(fs0, []tla.Value{iface.Self(), indexRead1.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))}, exprRead14.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value")))
					if err != nil {
						return err
					}
					var condition27 tla.Value
					condition27, err = iface.Read(req3, nil)
					if err != nil {
						return err
					}
					var condition28 tla.Value
					condition28, err = iface.Read(lastPutBody2, nil)
					if err != nil {
						return err
					}
					if !tla.Symbol_GreaterThanOrEqualSymbol(condition27.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("versionNumber")), condition28.ApplyFunction(tla.MakeString("versionNumber"))).AsBool() {
						return fmt.Errorf("%w: (((req).body).versionNumber) >= ((lastPutBody).versionNumber)", distsys.ErrAssertionFailed)
					}
					var exprRead15 tla.Value
					exprRead15, err = iface.Read(req3, nil)
					if err != nil {
						return err
					}
					err = iface.Write(lastPutBody2, nil, exprRead15.ApplyFunction(tla.MakeString("body")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody, nil, ACK_MSG_BODY(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp, nil, PUT_RESP(iface))
					if err != nil {
						return err
					}
					err = iface.Write(shouldSync2, nil, tla.Symbol_TRUE)
					if err != nil {
						return err
					}
					// no statements
				} else {
					var condition29 tla.Value
					condition29, err = iface.Read(req3, nil)
					if err != nil {
						return err
					}
					if tla.Symbol_EqualsSymbol(condition29.ApplyFunction(tla.MakeString("typ")), SYNC_REQ(iface)).AsBool() {
						var condition30 tla.Value
						condition30, err = iface.Read(req3, nil)
						if err != nil {
							return err
						}
						var condition31 tla.Value
						condition31, err = iface.Read(lastPutBody2, nil)
						if err != nil {
							return err
						}
						if tla.Symbol_GreaterThanSymbol(condition30.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("versionNumber")), condition31.ApplyFunction(tla.MakeString("versionNumber"))).AsBool() {
							var exprRead16 tla.Value
							exprRead16, err = iface.Read(req3, nil)
							if err != nil {
								return err
							}
							var indexRead2 tla.Value
							indexRead2, err = iface.Read(req3, nil)
							if err != nil {
								return err
							}
							err = iface.Write(fs0, []tla.Value{iface.Self(), indexRead2.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))}, exprRead16.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value")))
							if err != nil {
								return err
							}
							var exprRead17 tla.Value
							exprRead17, err = iface.Read(req3, nil)
							if err != nil {
								return err
							}
							err = iface.Write(lastPutBody2, nil, exprRead17.ApplyFunction(tla.MakeString("body")))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var exprRead18 tla.Value
						exprRead18, err = iface.Read(lastPutBody2, nil)
						if err != nil {
							return err
						}
						err = iface.Write(respBody, nil, exprRead18)
						if err != nil {
							return err
						}
						err = iface.Write(respTyp, nil, SYNC_RESP(iface))
						if err != nil {
							return err
						}
						err = iface.Write(shouldSync2, nil, tla.Symbol_TRUE)
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				}
				// no statements
			}
			var exprRead19 tla.Value
			exprRead19, err = iface.Read(req3, nil)
			if err != nil {
				return err
			}
			var exprRead20 tla.Value
			exprRead20, err = iface.Read(respBody, nil)
			if err != nil {
				return err
			}
			var exprRead21 tla.Value
			exprRead21, err = iface.Read(respTyp, nil)
			if err != nil {
				return err
			}
			var exprRead22 tla.Value
			exprRead22, err = iface.Read(req3, nil)
			if err != nil {
				return err
			}
			err = iface.Write(resp, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("to"), exprRead19.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), exprRead20},
				{tla.MakeString("srcTyp"), BACKUP_SRC(iface)},
				{tla.MakeString("typ"), exprRead21},
				{tla.MakeString("id"), exprRead22.ApplyFunction(tla.MakeString("id"))},
			}))
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AReplica.handleBackup.0", 2) {
			case 0:
				var exprRead23 tla.Value
				exprRead23, err = iface.Read(resp, nil)
				if err != nil {
					return err
				}
				var indexRead3 tla.Value
				indexRead3, err = iface.Read(resp, nil)
				if err != nil {
					return err
				}
				err = iface.Write(net2, []tla.Value{tla.MakeTuple(indexRead3.ApplyFunction(tla.MakeString("to")), RESP_INDEX(iface))}, exprRead23)
				if err != nil {
					return err
				}
				// no statements
			case 1:
				var condition32 tla.Value
				condition32, err = iface.Read(resp, nil)
				if err != nil {
					return err
				}
				var condition33 tla.Value
				condition33, err = iface.Read(fd2, []tla.Value{condition32.ApplyFunction(tla.MakeString("to"))})
				if err != nil {
					return err
				}
				if !condition33.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				// no statements
			default:
				panic("current branch of either matches no code paths!")
			}
			return iface.Goto("AReplica.replicaLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.handlePrimary",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req18 := iface.RequireArchetypeResource("AReplica.req")
			respBody3 := iface.RequireArchetypeResource("AReplica.respBody")
			fs3, err := iface.RequireArchetypeResourceRef("AReplica.fs")
			if err != nil {
				return err
			}
			respTyp3 := iface.RequireArchetypeResource("AReplica.respTyp")
			lastPutBody7 := iface.RequireArchetypeResource("AReplica.lastPutBody")
			replicaSet8 := iface.RequireArchetypeResource("AReplica.replicaSet")
			idx8 := iface.RequireArchetypeResource("AReplica.idx")
			if iface.GetConstant("DEBUG")().AsBool() {
				tla.MakeTuple(tla.MakeString("ServerHandlePrimary"), iface.Self()).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			var condition34 tla.Value
			condition34, err = iface.Read(req18, nil)
			if err != nil {
				return err
			}
			if !tla.Symbol_EqualsSymbol(condition34.ApplyFunction(tla.MakeString("srcTyp")), CLIENT_SRC(iface)).AsBool() {
				return fmt.Errorf("%w: ((req).srcTyp) = (CLIENT_SRC)", distsys.ErrAssertionFailed)
			}
			var condition35 tla.Value
			condition35, err = iface.Read(req18, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_EqualsSymbol(condition35.ApplyFunction(tla.MakeString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead24 tla.Value
				exprRead24, err = iface.Read(req18, nil)
				if err != nil {
					return err
				}
				var exprRead25 tla.Value
				exprRead25, err = iface.Read(fs3, []tla.Value{iface.Self(), exprRead24.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody3, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("content"), exprRead25},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(respTyp3, nil, GET_RESP(iface))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.sndResp")
			} else {
				var condition36 tla.Value
				condition36, err = iface.Read(req18, nil)
				if err != nil {
					return err
				}
				if tla.Symbol_EqualsSymbol(condition36.ApplyFunction(tla.MakeString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead26 tla.Value
					exprRead26, err = iface.Read(req18, nil)
					if err != nil {
						return err
					}
					var indexRead4 tla.Value
					indexRead4, err = iface.Read(req18, nil)
					if err != nil {
						return err
					}
					err = iface.Write(fs3, []tla.Value{iface.Self(), indexRead4.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))}, exprRead26.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value")))
					if err != nil {
						return err
					}
					var exprRead27 tla.Value
					exprRead27, err = iface.Read(lastPutBody7, nil)
					if err != nil {
						return err
					}
					var exprRead28 tla.Value
					exprRead28, err = iface.Read(req18, nil)
					if err != nil {
						return err
					}
					var exprRead29 tla.Value
					exprRead29, err = iface.Read(req18, nil)
					if err != nil {
						return err
					}
					err = iface.Write(lastPutBody7, nil, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("versionNumber"), tla.Symbol_PlusSymbol(exprRead27.ApplyFunction(tla.MakeString("versionNumber")), tla.MakeNumber(1))},
						{tla.MakeString("key"), exprRead28.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key"))},
						{tla.MakeString("value"), exprRead29.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value"))},
					}))
					if err != nil {
						return err
					}
					err = iface.Write(respBody3, nil, ACK_MSG_BODY(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp3, nil, PUT_RESP(iface))
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet8, nil, tla.Symbol_BackslashSymbol(REPLICA_SET(iface), tla.MakeSet(iface.Self())))
					if err != nil {
						return err
					}
					err = iface.Write(idx8, nil, tla.MakeNumber(1))
					if err != nil {
						return err
					}
					return iface.Goto("AReplica.sndReplicaReqLoop")
				} else {
					return iface.Goto("AReplica.sndReplicaReqLoop")
				}
				// no statements
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndReplicaReqLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx9 := iface.RequireArchetypeResource("AReplica.idx")
			repReq1 := iface.RequireArchetypeResource("AReplica.repReq")
			lastPutBody9 := iface.RequireArchetypeResource("AReplica.lastPutBody")
			req26 := iface.RequireArchetypeResource("AReplica.req")
			net3, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			fd3, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			netEnabled3, err := iface.RequireArchetypeResourceRef("AReplica.netEnabled")
			if err != nil {
				return err
			}
			var condition37 tla.Value
			condition37, err = iface.Read(idx9, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_LessThanOrEqualSymbol(condition37, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				var condition38 tla.Value
				condition38, err = iface.Read(idx9, nil)
				if err != nil {
					return err
				}
				if tla.Symbol_NotEqualsSymbol(condition38, iface.Self()).AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndReplicaReqLoop.0", 2) {
					case 0:
						var exprRead31 tla.Value
						exprRead31, err = iface.Read(idx9, nil)
						if err != nil {
							return err
						}
						var exprRead32 tla.Value
						exprRead32, err = iface.Read(lastPutBody9, nil)
						if err != nil {
							return err
						}
						var exprRead33 tla.Value
						exprRead33, err = iface.Read(req26, nil)
						if err != nil {
							return err
						}
						err = iface.Write(repReq1, nil, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("from"), iface.Self()},
							{tla.MakeString("to"), exprRead31},
							{tla.MakeString("body"), exprRead32},
							{tla.MakeString("srcTyp"), PRIMARY_SRC(iface)},
							{tla.MakeString("typ"), PUT_REQ(iface)},
							{tla.MakeString("id"), exprRead33.ApplyFunction(tla.MakeString("id"))},
						}))
						if err != nil {
							return err
						}
						var exprRead34 tla.Value
						exprRead34, err = iface.Read(repReq1, nil)
						if err != nil {
							return err
						}
						var indexRead5 tla.Value
						indexRead5, err = iface.Read(idx9, nil)
						if err != nil {
							return err
						}
						err = iface.Write(net3, []tla.Value{tla.MakeTuple(indexRead5, REQ_INDEX(iface))}, exprRead34)
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition39 tla.Value
						condition39, err = iface.Read(idx9, nil)
						if err != nil {
							return err
						}
						var condition40 tla.Value
						condition40, err = iface.Read(fd3, []tla.Value{condition39})
						if err != nil {
							return err
						}
						if !condition40.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead30 tla.Value
				exprRead30, err = iface.Read(idx9, nil)
				if err != nil {
					return err
				}
				err = iface.Write(idx9, nil, tla.Symbol_PlusSymbol(exprRead30, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndReplicaReqLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.sndReplicaReqLoop")
					case 1:
						err = iface.Write(netEnabled3, []tla.Value{tla.MakeTuple(iface.Self(), REQ_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled3, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AReplica.sndReplicaReqLoop")
				}
				// no statements
			} else {
				return iface.Goto("AReplica.rcvReplicaRespLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvReplicaRespLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			replicaSet9 := iface.RequireArchetypeResource("AReplica.replicaSet")
			repResp11 := iface.RequireArchetypeResource("AReplica.repResp")
			net4, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			fd4, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			req27 := iface.RequireArchetypeResource("AReplica.req")
			replica2 := iface.RequireArchetypeResource("AReplica.replica")
			netLen0, err := iface.RequireArchetypeResourceRef("AReplica.netLen")
			if err != nil {
				return err
			}
			netEnabled5, err := iface.RequireArchetypeResourceRef("AReplica.netEnabled")
			if err != nil {
				return err
			}
			var condition41 tla.Value
			condition41, err = iface.Read(replicaSet9, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_GreaterThanSymbol(tla.Symbol_Cardinality(condition41), tla.MakeNumber(0)).AsBool() {
				switch iface.NextFairnessCounter("AReplica.rcvReplicaRespLoop.0", 2) {
				case 0:
					var exprRead35 tla.Value
					exprRead35, err = iface.Read(net4, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					err = iface.Write(repResp11, nil, exprRead35)
					if err != nil {
						return err
					}
					var condition42 tla.Value
					condition42, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition43 tla.Value
					condition43, err = iface.Read(replicaSet9, nil)
					if err != nil {
						return err
					}
					var condition44 tla.Value
					condition44, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition45 tla.Value
					condition45, err = iface.Read(fd4, []tla.Value{condition44.ApplyFunction(tla.MakeString("from"))})
					if err != nil {
						return err
					}
					var condition46 tla.Value
					condition46, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition47 tla.Value
					condition47, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition48 tla.Value
					condition48, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition49 tla.Value
					condition49, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition50 tla.Value
					condition50, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					var condition51 tla.Value
					condition51, err = iface.Read(req27, nil)
					if err != nil {
						return err
					}
					if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.Symbol_InSymbol(condition42.ApplyFunction(tla.MakeString("from")), condition43).AsBool() || condition45.AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition46.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition47.ApplyFunction(tla.MakeString("body")), ACK_MSG_BODY(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition48.ApplyFunction(tla.MakeString("srcTyp")), BACKUP_SRC(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition49.ApplyFunction(tla.MakeString("typ")), PUT_RESP(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition50.ApplyFunction(tla.MakeString("id")), condition51.ApplyFunction(tla.MakeString("id"))).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((((((repResp).from) \\in (replicaSet)) \\/ ((fd)[(repResp).from])) /\\ (((repResp).to) = (self))) /\\ (((repResp).body) = (ACK_MSG_BODY))) /\\ (((repResp).srcTyp) = (BACKUP_SRC))) /\\ (((repResp).typ) = (PUT_RESP))) /\\ (((repResp).id) = ((req).id))", distsys.ErrAssertionFailed)
					}
					var exprRead36 tla.Value
					exprRead36, err = iface.Read(replicaSet9, nil)
					if err != nil {
						return err
					}
					var exprRead37 tla.Value
					exprRead37, err = iface.Read(repResp11, nil)
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet9, nil, tla.Symbol_BackslashSymbol(exprRead36, tla.MakeSet(exprRead37.ApplyFunction(tla.MakeString("from")))))
					if err != nil {
						return err
					}
					// no statements
				case 1:
					var exprRead38 tla.Value
					exprRead38, err = iface.Read(replicaSet9, nil)
					if err != nil {
						return err
					}
					err = iface.Write(replica2, nil, tla.Choose(exprRead38, func(element0 tla.Value) bool {
						var r0 tla.Value = element0
						_ = r0
						return tla.Symbol_TRUE.AsBool()
					}))
					if err != nil {
						return err
					}
					var condition52 tla.Value
					condition52, err = iface.Read(replica2, nil)
					if err != nil {
						return err
					}
					var condition53 tla.Value
					condition53, err = iface.Read(fd4, []tla.Value{condition52})
					if err != nil {
						return err
					}
					var condition54 tla.Value
					condition54, err = iface.Read(netLen0, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					if !tla.MakeBool(condition53.AsBool() && tla.Symbol_EqualsSymbol(condition54, tla.MakeNumber(0)).AsBool()).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var exprRead39 tla.Value
					exprRead39, err = iface.Read(replicaSet9, nil)
					if err != nil {
						return err
					}
					var exprRead40 tla.Value
					exprRead40, err = iface.Read(replica2, nil)
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet9, nil, tla.Symbol_BackslashSymbol(exprRead39, tla.MakeSet(exprRead40)))
					if err != nil {
						return err
					}
					// no statements
				default:
					panic("current branch of either matches no code paths!")
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.rcvReplicaRespLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.rcvReplicaRespLoop")
					case 1:
						err = iface.Write(netEnabled5, []tla.Value{tla.MakeTuple(iface.Self(), REQ_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled5, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))}, tla.Symbol_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AReplica.rcvReplicaRespLoop")
				}
				// no statements
			} else {
				return iface.Goto("AReplica.sndResp")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp3 := iface.RequireArchetypeResource("AReplica.resp")
			req28 := iface.RequireArchetypeResource("AReplica.req")
			respBody5 := iface.RequireArchetypeResource("AReplica.respBody")
			respTyp5 := iface.RequireArchetypeResource("AReplica.respTyp")
			net5, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			var exprRead41 tla.Value
			exprRead41, err = iface.Read(req28, nil)
			if err != nil {
				return err
			}
			var exprRead42 tla.Value
			exprRead42, err = iface.Read(respBody5, nil)
			if err != nil {
				return err
			}
			var exprRead43 tla.Value
			exprRead43, err = iface.Read(respTyp5, nil)
			if err != nil {
				return err
			}
			var exprRead44 tla.Value
			exprRead44, err = iface.Read(req28, nil)
			if err != nil {
				return err
			}
			err = iface.Write(resp3, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("to"), exprRead41.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), exprRead42},
				{tla.MakeString("srcTyp"), PRIMARY_SRC(iface)},
				{tla.MakeString("typ"), exprRead43},
				{tla.MakeString("id"), exprRead44.ApplyFunction(tla.MakeString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead45 tla.Value
			exprRead45, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			var indexRead6 tla.Value
			indexRead6, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			err = iface.Write(net5, []tla.Value{tla.MakeTuple(indexRead6.ApplyFunction(tla.MakeString("to")), RESP_INDEX(iface))}, exprRead45)
			if err != nil {
				return err
			}
			if iface.GetConstant("DEBUG")().AsBool() {
				var toPrint0 tla.Value
				toPrint0, err = iface.Read(req28, nil)
				if err != nil {
					return err
				}
				tla.MakeTuple(tla.MakeString("ServerSendResp"), iface.Self(), toPrint0.ApplyFunction(tla.MakeString("from"))).PCalPrint()
				return iface.Goto("AReplica.replicaLoop")
			} else {
				return iface.Goto("AReplica.replicaLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.failLabel",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd6, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			primary2, err := iface.RequireArchetypeResourceRef("AReplica.primary")
			if err != nil {
				return err
			}
			err = iface.Write(fd6, []tla.Value{iface.Self()}, tla.Symbol_TRUE)
			if err != nil {
				return err
			}
			err = iface.Write(primary2, nil, iface.Self())
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AClient.msg")
			input, err := iface.RequireArchetypeResourceRef("AClient.input")
			if err != nil {
				return err
			}
			idx16 := iface.RequireArchetypeResource("AClient.idx")
			if tla.Symbol_TRUE.AsBool() {
				if iface.GetConstant("DEBUG")().AsBool() {
					tla.MakeTuple(tla.MakeString("ClientLoop"), iface.Self()).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var exprRead46 tla.Value
				exprRead46, err = iface.Read(input, nil)
				if err != nil {
					return err
				}
				err = iface.Write(msg, nil, exprRead46)
				if err != nil {
					return err
				}
				var exprRead47 tla.Value
				exprRead47, err = iface.Read(idx16, nil)
				if err != nil {
					return err
				}
				err = iface.Write(idx16, nil, tla.Symbol_PlusSymbol(exprRead47, tla.MakeNumber(1)))
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
			replica5 := iface.RequireArchetypeResource("AClient.replica")
			primary3, err := iface.RequireArchetypeResourceRef("AClient.primary")
			if err != nil {
				return err
			}
			req31 := iface.RequireArchetypeResource("AClient.req")
			msg0 := iface.RequireArchetypeResource("AClient.msg")
			idx18 := iface.RequireArchetypeResource("AClient.idx")
			net6, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			fd7, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			var exprRead48 tla.Value
			exprRead48, err = iface.Read(primary3, nil)
			if err != nil {
				return err
			}
			err = iface.Write(replica5, nil, exprRead48)
			if err != nil {
				return err
			}
			var condition55 tla.Value
			condition55, err = iface.Read(replica5, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_NotEqualsSymbol(condition55, NULL(iface)).AsBool() {
				switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
				case 0:
					var exprRead49 tla.Value
					exprRead49, err = iface.Read(replica5, nil)
					if err != nil {
						return err
					}
					var exprRead50 tla.Value
					exprRead50, err = iface.Read(msg0, nil)
					if err != nil {
						return err
					}
					var exprRead51 tla.Value
					exprRead51, err = iface.Read(msg0, nil)
					if err != nil {
						return err
					}
					var exprRead52 tla.Value
					exprRead52, err = iface.Read(idx18, nil)
					if err != nil {
						return err
					}
					err = iface.Write(req31, nil, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("from"), iface.Self()},
						{tla.MakeString("to"), exprRead49},
						{tla.MakeString("body"), exprRead50.ApplyFunction(tla.MakeString("body"))},
						{tla.MakeString("srcTyp"), CLIENT_SRC(iface)},
						{tla.MakeString("typ"), exprRead51.ApplyFunction(tla.MakeString("typ"))},
						{tla.MakeString("id"), exprRead52},
					}))
					if err != nil {
						return err
					}
					var exprRead53 tla.Value
					exprRead53, err = iface.Read(req31, nil)
					if err != nil {
						return err
					}
					var indexRead7 tla.Value
					indexRead7, err = iface.Read(req31, nil)
					if err != nil {
						return err
					}
					err = iface.Write(net6, []tla.Value{tla.MakeTuple(indexRead7.ApplyFunction(tla.MakeString("to")), REQ_INDEX(iface))}, exprRead53)
					if err != nil {
						return err
					}
					if iface.GetConstant("DEBUG")().AsBool() {
						var toPrint1 tla.Value
						toPrint1, err = iface.Read(replica5, nil)
						if err != nil {
							return err
						}
						tla.MakeTuple(tla.MakeString("ClientSendReq"), iface.Self(), toPrint1).PCalPrint()
						return iface.Goto("AClient.rcvResp")
					} else {
						return iface.Goto("AClient.rcvResp")
					}
					// no statements
				case 1:
					var condition56 tla.Value
					condition56, err = iface.Read(replica5, nil)
					if err != nil {
						return err
					}
					var condition57 tla.Value
					condition57, err = iface.Read(fd7, []tla.Value{condition56})
					if err != nil {
						return err
					}
					if !condition57.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("AClient.sndReq")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.rcvResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp6 := iface.RequireArchetypeResource("AClient.resp")
			net7, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			replica10 := iface.RequireArchetypeResource("AClient.replica")
			idx19 := iface.RequireArchetypeResource("AClient.idx")
			msg2 := iface.RequireArchetypeResource("AClient.msg")
			output, err := iface.RequireArchetypeResourceRef("AClient.output")
			if err != nil {
				return err
			}
			fd8, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			netLen1, err := iface.RequireArchetypeResourceRef("AClient.netLen")
			if err != nil {
				return err
			}
			if iface.GetConstant("DEBUG")().AsBool() {
				tla.MakeTuple(tla.MakeString("ClientRcvRespEither"), iface.Self()).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			switch iface.NextFairnessCounter("AClient.rcvResp.0", 2) {
			case 0:
				var exprRead54 tla.Value
				exprRead54, err = iface.Read(net7, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp6, nil, exprRead54)
				if err != nil {
					return err
				}
				if iface.GetConstant("DEBUG")().AsBool() {
					var toPrint2 tla.Value
					toPrint2, err = iface.Read(replica10, nil)
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ClientRcvResp"), iface.Self(), toPrint2).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition58 tla.Value
				condition58, err = iface.Read(resp6, nil)
				if err != nil {
					return err
				}
				var condition59 tla.Value
				condition59, err = iface.Read(idx19, nil)
				if err != nil {
					return err
				}
				if tla.Symbol_NotEqualsSymbol(condition58.ApplyFunction(tla.MakeString("id")), condition59).AsBool() {
					return iface.Goto("AClient.rcvResp")
				} else {
					var condition60 tla.Value
					condition60, err = iface.Read(msg2, nil)
					if err != nil {
						return err
					}
					if tla.Symbol_EqualsSymbol(condition60.ApplyFunction(tla.MakeString("typ")), PUT_REQ(iface)).AsBool() {
						var condition61 tla.Value
						condition61, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						var condition62 tla.Value
						condition62, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						var condition63 tla.Value
						condition63, err = iface.Read(replica10, nil)
						if err != nil {
							return err
						}
						var condition64 tla.Value
						condition64, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						var condition65 tla.Value
						condition65, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						var condition66 tla.Value
						condition66, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						var condition67 tla.Value
						condition67, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						var condition68 tla.Value
						condition68, err = iface.Read(idx19, nil)
						if err != nil {
							return err
						}
						if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.Symbol_EqualsSymbol(condition61.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() && tla.Symbol_EqualsSymbol(condition62.ApplyFunction(tla.MakeString("from")), condition63).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition64.ApplyFunction(tla.MakeString("body")), ACK_MSG_BODY(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition65.ApplyFunction(tla.MakeString("srcTyp")), PRIMARY_SRC(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition66.ApplyFunction(tla.MakeString("typ")), PUT_RESP(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition67.ApplyFunction(tla.MakeString("id")), condition68).AsBool()).AsBool() {
							return fmt.Errorf("%w: (((((((resp).to) = (self)) /\\ (((resp).from) = (replica))) /\\ (((resp).body) = (ACK_MSG_BODY))) /\\ (((resp).srcTyp) = (PRIMARY_SRC))) /\\ (((resp).typ) = (PUT_RESP))) /\\ (((resp).id) = (idx))", distsys.ErrAssertionFailed)
						}
						var exprRead55 tla.Value
						exprRead55, err = iface.Read(resp6, nil)
						if err != nil {
							return err
						}
						err = iface.Write(output, nil, exprRead55.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("content")))
						if err != nil {
							return err
						}
						return iface.Goto("AClient.clientLoop")
					} else {
						var condition69 tla.Value
						condition69, err = iface.Read(msg2, nil)
						if err != nil {
							return err
						}
						if tla.Symbol_EqualsSymbol(condition69.ApplyFunction(tla.MakeString("typ")), GET_REQ(iface)).AsBool() {
							var condition70 tla.Value
							condition70, err = iface.Read(resp6, nil)
							if err != nil {
								return err
							}
							var condition71 tla.Value
							condition71, err = iface.Read(resp6, nil)
							if err != nil {
								return err
							}
							var condition72 tla.Value
							condition72, err = iface.Read(replica10, nil)
							if err != nil {
								return err
							}
							var condition73 tla.Value
							condition73, err = iface.Read(resp6, nil)
							if err != nil {
								return err
							}
							var condition74 tla.Value
							condition74, err = iface.Read(resp6, nil)
							if err != nil {
								return err
							}
							var condition75 tla.Value
							condition75, err = iface.Read(resp6, nil)
							if err != nil {
								return err
							}
							var condition76 tla.Value
							condition76, err = iface.Read(idx19, nil)
							if err != nil {
								return err
							}
							if !tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.MakeBool(tla.Symbol_EqualsSymbol(condition70.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() && tla.Symbol_EqualsSymbol(condition71.ApplyFunction(tla.MakeString("from")), condition72).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition73.ApplyFunction(tla.MakeString("srcTyp")), PRIMARY_SRC(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition74.ApplyFunction(tla.MakeString("typ")), GET_RESP(iface)).AsBool()).AsBool() && tla.Symbol_EqualsSymbol(condition75.ApplyFunction(tla.MakeString("id")), condition76).AsBool()).AsBool() {
								return fmt.Errorf("%w: ((((((resp).to) = (self)) /\\ (((resp).from) = (replica))) /\\ (((resp).srcTyp) = (PRIMARY_SRC))) /\\ (((resp).typ) = (GET_RESP))) /\\ (((resp).id) = (idx))", distsys.ErrAssertionFailed)
							}
							var exprRead56 tla.Value
							exprRead56, err = iface.Read(resp6, nil)
							if err != nil {
								return err
							}
							err = iface.Write(output, nil, exprRead56.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("content")))
							if err != nil {
								return err
							}
							return iface.Goto("AClient.clientLoop")
						} else {
							if !tla.Symbol_FALSE.AsBool() {
								return fmt.Errorf("%w: FALSE", distsys.ErrAssertionFailed)
							}
							return iface.Goto("AClient.clientLoop")
						}
						// no statements
					}
					// no statements
				}
				// no statements
			case 1:
				var condition77 tla.Value
				condition77, err = iface.Read(replica10, nil)
				if err != nil {
					return err
				}
				var condition78 tla.Value
				condition78, err = iface.Read(fd8, []tla.Value{condition77})
				if err != nil {
					return err
				}
				var condition79 tla.Value
				condition79, err = iface.Read(netLen1, []tla.Value{tla.MakeTuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				if !tla.MakeBool(condition78.AsBool() && tla.Symbol_EqualsSymbol(condition79, tla.MakeNumber(0)).AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				if iface.GetConstant("DEBUG")().AsBool() {
					var toPrint3 tla.Value
					toPrint3, err = iface.Read(replica10, nil)
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ClientDetectedFail"), iface.Self(), toPrint3).PCalPrint()
					// no statements
				} else {
					// no statements
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

var AReplica = distsys.MPCalArchetype{
	Name:              "AReplica",
	Label:             "AReplica.replicaLoop",
	RequiredRefParams: []string{"AReplica.net", "AReplica.fs", "AReplica.fd", "AReplica.netEnabled", "AReplica.primary", "AReplica.netLen"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AReplica.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.respBody", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.respTyp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.idx", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.repReq", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.repResp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.resp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.replicaSet", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.shouldSync", tla.Symbol_FALSE)
		iface.EnsureArchetypeResourceLocal("AReplica.lastPutBody", tla.MakeRecord([]tla.RecordField{
			{tla.MakeString("versionNumber"), tla.MakeNumber(0)},
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.replica", tla.Value{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.net", "AClient.fd", "AClient.primary", "AClient.netLen", "AClient.input", "AClient.output"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.replica", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.idx", tla.MakeNumber(0))
	},
}
