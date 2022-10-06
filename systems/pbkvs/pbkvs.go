package pbkvs

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func NUM_NODES(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_PUT_CLIENTS")()), iface.GetConstant("NUM_GET_CLIENTS")())
}
func CLIENT_SRC(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func PRIMARY_SRC(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func BACKUP_SRC(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func GET_REQ(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func GET_RESP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func PUT_REQ(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func PUT_RESP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(4)
}
func SYNC_REQ(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(5)
}
func SYNC_RESP(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(6)
}
func REQ_INDEX(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func RESP_INDEX(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func ACK_MSG_BODY(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLARecord([]tla.TLARecordField{
		{tla.MakeTLAString("content"), tla.MakeTLAString("ack-body")},
	})
}
func KEY1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("KEY1")
}
func VALUE1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("VALUE1")
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), NUM_NODES(iface))
}
func REPLICA_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NUM_REPLICAS")())
}
func PUT_CLIENT_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_PUT_CLIENTS")()))
}
func GET_CLIENT_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_PUT_CLIENTS")()), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_PUT_CLIENTS")()), iface.GetConstant("NUM_GET_CLIENTS")()))
}
func MSG_INDEX_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(REQ_INDEX(iface), RESP_INDEX(iface))
}
func KEY_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(KEY1(iface))
}
func VALUE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(VALUE1(iface))
}
func NULL(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
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
			if tla.TLA_TRUE.AsBool() {
				err = iface.Write(replicaSet, []tla.TLAValue{}, tla.TLA_BackslashSymbol(REPLICA_SET(iface), tla.MakeTLASet(iface.Self())))
				if err != nil {
					return err
				}
				err = iface.Write(idx, []tla.TLAValue{}, tla.MakeTLANumber(1))
				if err != nil {
					return err
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.replicaLoop.0", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.syncPrimary")
					case 1:
						err = iface.Write(netEnabled, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), REQ_INDEX(iface))}, tla.TLA_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))}, tla.TLA_FALSE)
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
			var condition tla.TLAValue
			condition, err = iface.Read(primary, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition0 tla.TLAValue
			condition0, err = iface.Read(shouldSync, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition, iface.Self()).AsBool() && condition0.AsBool()).AsBool() {
				err = iface.Write(shouldSync, []tla.TLAValue{}, tla.TLA_FALSE)
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
			var condition1 tla.TLAValue
			condition1, err = iface.Read(idx0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition1, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				var condition2 tla.TLAValue
				condition2, err = iface.Read(idx0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition2, iface.Self()).AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndSyncReqLoop.0", 2) {
					case 0:
						var exprRead0 tla.TLAValue
						exprRead0, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead1 tla.TLAValue
						exprRead1, err = iface.Read(lastPutBody, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(repReq, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("from"), iface.Self()},
							{tla.MakeTLAString("to"), exprRead0},
							{tla.MakeTLAString("body"), exprRead1},
							{tla.MakeTLAString("srcTyp"), PRIMARY_SRC(iface)},
							{tla.MakeTLAString("typ"), SYNC_REQ(iface)},
							{tla.MakeTLAString("id"), tla.MakeTLANumber(3)},
						}))
						if err != nil {
							return err
						}
						var exprRead2 tla.TLAValue
						exprRead2, err = iface.Read(repReq, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead tla.TLAValue
						indexRead, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net, []tla.TLAValue{tla.MakeTLATuple(indexRead, REQ_INDEX(iface))}, exprRead2)
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition3 tla.TLAValue
						condition3, err = iface.Read(idx0, []tla.TLAValue{})
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
						// no statements
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead tla.TLAValue
				exprRead, err = iface.Read(idx0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndSyncReqLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.sndSyncReqLoop")
					case 1:
						err = iface.Write(netEnabled1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), REQ_INDEX(iface))}, tla.TLA_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))}, tla.TLA_FALSE)
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
			var condition5 tla.TLAValue
			condition5, err = iface.Read(replicaSet0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_GreaterThanSymbol(tla.TLA_Cardinality(condition5), tla.MakeTLANumber(0)).AsBool() {
				switch iface.NextFairnessCounter("AReplica.rcvSyncRespLoop.0", 2) {
				case 0:
					var exprRead3 tla.TLAValue
					exprRead3, err = iface.Read(net0, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					err = iface.Write(repResp, []tla.TLAValue{}, exprRead3)
					if err != nil {
						return err
					}
					var condition6 tla.TLAValue
					condition6, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition7 tla.TLAValue
					condition7, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition8 tla.TLAValue
					condition8, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition9 tla.TLAValue
					condition9, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition10 tla.TLAValue
					condition10, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition11 tla.TLAValue
					condition11, err = iface.Read(replicaSet0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition12 tla.TLAValue
					condition12, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition13 tla.TLAValue
					condition13, err = iface.Read(fd0, []tla.TLAValue{condition12.ApplyFunction(tla.MakeTLAString("from"))})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition6.ApplyFunction(tla.MakeTLAString("id")), tla.MakeTLANumber(3)).AsBool() && tla.TLA_EqualsSymbol(condition7.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition8.ApplyFunction(tla.MakeTLAString("srcTyp")), BACKUP_SRC(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition9.ApplyFunction(tla.MakeTLAString("typ")), SYNC_RESP(iface)).AsBool()).AsBool() && tla.MakeTLABool(tla.TLA_InSymbol(condition10.ApplyFunction(tla.MakeTLAString("from")), condition11).AsBool() || condition13.AsBool()).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((((repResp).id) = (3)) /\\ (((repResp).to) = (self))) /\\ (((repResp).srcTyp) = (BACKUP_SRC))) /\\ (((repResp).typ) = (SYNC_RESP))) /\\ ((((repResp).from) \\in (replicaSet)) \\/ ((fd)[(repResp).from]))", distsys.ErrAssertionFailed)
					}
					var condition14 tla.TLAValue
					condition14, err = iface.Read(repResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition15 tla.TLAValue
					condition15, err = iface.Read(lastPutBody0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_GreaterThanSymbol(condition14.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("versionNumber")), condition15.ApplyFunction(tla.MakeTLAString("versionNumber"))).AsBool() {
						var exprRead4 tla.TLAValue
						exprRead4, err = iface.Read(repResp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead0 tla.TLAValue
						indexRead0, err = iface.Read(repResp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(fs, []tla.TLAValue{iface.Self(), indexRead0.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))}, exprRead4.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value")))
						if err != nil {
							return err
						}
						var exprRead5 tla.TLAValue
						exprRead5, err = iface.Read(repResp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(lastPutBody0, []tla.TLAValue{}, exprRead5.ApplyFunction(tla.MakeTLAString("body")))
						if err != nil {
							return err
						}
						err = iface.Write(replicaSet0, []tla.TLAValue{}, tla.TLA_BackslashSymbol(REPLICA_SET(iface), tla.MakeTLASet(iface.Self())))
						if err != nil {
							return err
						}
						err = iface.Write(idx7, []tla.TLAValue{}, tla.MakeTLANumber(1))
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.sndSyncReqLoop")
					} else {
						var exprRead6 tla.TLAValue
						exprRead6, err = iface.Read(replicaSet0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead7 tla.TLAValue
						exprRead7, err = iface.Read(repResp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(replicaSet0, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead6, tla.MakeTLASet(exprRead7.ApplyFunction(tla.MakeTLAString("from")))))
						if err != nil {
							return err
						}
						return iface.Goto("AReplica.rcvSyncRespLoop")
					}
					// no statements
				case 1:
					var exprRead8 tla.TLAValue
					exprRead8, err = iface.Read(replicaSet0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(replica, []tla.TLAValue{}, tla.TLAChoose(exprRead8, func(element tla.TLAValue) bool {
						var r tla.TLAValue = element
						_ = r
						return tla.TLA_TRUE.AsBool()
					}))
					if err != nil {
						return err
					}
					var condition16 tla.TLAValue
					condition16, err = iface.Read(replica, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition17 tla.TLAValue
					condition17, err = iface.Read(fd0, []tla.TLAValue{condition16})
					if err != nil {
						return err
					}
					var condition18 tla.TLAValue
					condition18, err = iface.Read(netLen, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(condition17.AsBool() && tla.TLA_EqualsSymbol(condition18, tla.MakeTLANumber(0)).AsBool()).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var exprRead9 tla.TLAValue
					exprRead9, err = iface.Read(replicaSet0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead10 tla.TLAValue
					exprRead10, err = iface.Read(replica, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet0, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead9, tla.MakeTLASet(exprRead10)))
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
			var condition19 tla.TLAValue
			condition19, err = iface.Read(primary0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition20 tla.TLAValue
			condition20, err = iface.Read(shouldSync1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition19, iface.Self()).AsBool() && condition20.AsBool()).AsBool() {
				return iface.Goto("AReplica.syncPrimary")
			} else {
				var exprRead11 tla.TLAValue
				exprRead11, err = iface.Read(net1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), REQ_INDEX(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.TLAValue{}, exprRead11)
				if err != nil {
					return err
				}
				var condition21 tla.TLAValue
				condition21, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition21.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((req).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition22 tla.TLAValue
				condition22, err = iface.Read(primary0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition23 tla.TLAValue
				condition23, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition22, iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition23.ApplyFunction(tla.MakeTLAString("srcTyp")), CLIENT_SRC(iface)).AsBool()).AsBool() {
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
			req2 := iface.RequireArchetypeResource("AReplica.req")
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
			var condition24 tla.TLAValue
			condition24, err = iface.Read(req2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition24.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
				return fmt.Errorf("%w: ((req).srcTyp) = (PRIMARY_SRC)", distsys.ErrAssertionFailed)
			}
			var condition25 tla.TLAValue
			condition25, err = iface.Read(req2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition25.ApplyFunction(tla.MakeTLAString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead12 tla.TLAValue
				exprRead12, err = iface.Read(req2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead13 tla.TLAValue
				exprRead13, err = iface.Read(fs0, []tla.TLAValue{iface.Self(), exprRead12.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("content"), exprRead13},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(respTyp, []tla.TLAValue{}, GET_RESP(iface))
				if err != nil {
					return err
				}
				// no statements
			} else {
				var condition26 tla.TLAValue
				condition26, err = iface.Read(req2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition26.ApplyFunction(tla.MakeTLAString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead14 tla.TLAValue
					exprRead14, err = iface.Read(req2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead1 tla.TLAValue
					indexRead1, err = iface.Read(req2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(fs0, []tla.TLAValue{iface.Self(), indexRead1.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))}, exprRead14.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value")))
					if err != nil {
						return err
					}
					var condition27 tla.TLAValue
					condition27, err = iface.Read(req2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition28 tla.TLAValue
					condition28, err = iface.Read(lastPutBody2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_GreaterThanSymbol(condition27.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("versionNumber")), condition28.ApplyFunction(tla.MakeTLAString("versionNumber"))).AsBool() {
						return fmt.Errorf("%w: (((req).body).versionNumber) > ((lastPutBody).versionNumber)", distsys.ErrAssertionFailed)
					}
					var exprRead15 tla.TLAValue
					exprRead15, err = iface.Read(req2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(lastPutBody2, []tla.TLAValue{}, exprRead15.ApplyFunction(tla.MakeTLAString("body")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody, []tla.TLAValue{}, ACK_MSG_BODY(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp, []tla.TLAValue{}, PUT_RESP(iface))
					if err != nil {
						return err
					}
					err = iface.Write(shouldSync2, []tla.TLAValue{}, tla.TLA_TRUE)
					if err != nil {
						return err
					}
					// no statements
				} else {
					var condition29 tla.TLAValue
					condition29, err = iface.Read(req2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_EqualsSymbol(condition29.ApplyFunction(tla.MakeTLAString("typ")), SYNC_REQ(iface)).AsBool() {
						var condition30 tla.TLAValue
						condition30, err = iface.Read(req2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition31 tla.TLAValue
						condition31, err = iface.Read(lastPutBody2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_GreaterThanSymbol(condition30.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("versionNumber")), condition31.ApplyFunction(tla.MakeTLAString("versionNumber"))).AsBool() {
							var exprRead16 tla.TLAValue
							exprRead16, err = iface.Read(req2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var indexRead2 tla.TLAValue
							indexRead2, err = iface.Read(req2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(fs0, []tla.TLAValue{iface.Self(), indexRead2.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))}, exprRead16.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value")))
							if err != nil {
								return err
							}
							var exprRead17 tla.TLAValue
							exprRead17, err = iface.Read(req2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(lastPutBody2, []tla.TLAValue{}, exprRead17.ApplyFunction(tla.MakeTLAString("body")))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var exprRead18 tla.TLAValue
						exprRead18, err = iface.Read(lastPutBody2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(respBody, []tla.TLAValue{}, exprRead18)
						if err != nil {
							return err
						}
						err = iface.Write(respTyp, []tla.TLAValue{}, SYNC_RESP(iface))
						if err != nil {
							return err
						}
						err = iface.Write(shouldSync2, []tla.TLAValue{}, tla.TLA_TRUE)
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
			var exprRead19 tla.TLAValue
			exprRead19, err = iface.Read(req2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead20 tla.TLAValue
			exprRead20, err = iface.Read(respBody, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead21 tla.TLAValue
			exprRead21, err = iface.Read(respTyp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead22 tla.TLAValue
			exprRead22, err = iface.Read(req2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("to"), exprRead19.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), exprRead20},
				{tla.MakeTLAString("srcTyp"), BACKUP_SRC(iface)},
				{tla.MakeTLAString("typ"), exprRead21},
				{tla.MakeTLAString("id"), exprRead22.ApplyFunction(tla.MakeTLAString("id"))},
			}))
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AReplica.handleBackup.0", 2) {
			case 0:
				var exprRead23 tla.TLAValue
				exprRead23, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead3 tla.TLAValue
				indexRead3, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net2, []tla.TLAValue{tla.MakeTLATuple(indexRead3.ApplyFunction(tla.MakeTLAString("to")), RESP_INDEX(iface))}, exprRead23)
				if err != nil {
					return err
				}
				// no statements
			case 1:
				var condition32 tla.TLAValue
				condition32, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition33 tla.TLAValue
				condition33, err = iface.Read(fd2, []tla.TLAValue{condition32.ApplyFunction(tla.MakeTLAString("to"))})
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
			req17 := iface.RequireArchetypeResource("AReplica.req")
			respBody3 := iface.RequireArchetypeResource("AReplica.respBody")
			fs3, err := iface.RequireArchetypeResourceRef("AReplica.fs")
			if err != nil {
				return err
			}
			respTyp3 := iface.RequireArchetypeResource("AReplica.respTyp")
			lastPutBody7 := iface.RequireArchetypeResource("AReplica.lastPutBody")
			replicaSet8 := iface.RequireArchetypeResource("AReplica.replicaSet")
			idx8 := iface.RequireArchetypeResource("AReplica.idx")
			var condition34 tla.TLAValue
			condition34, err = iface.Read(req17, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition34.ApplyFunction(tla.MakeTLAString("srcTyp")), CLIENT_SRC(iface)).AsBool() {
				return fmt.Errorf("%w: ((req).srcTyp) = (CLIENT_SRC)", distsys.ErrAssertionFailed)
			}
			var condition35 tla.TLAValue
			condition35, err = iface.Read(req17, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition35.ApplyFunction(tla.MakeTLAString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead24 tla.TLAValue
				exprRead24, err = iface.Read(req17, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead25 tla.TLAValue
				exprRead25, err = iface.Read(fs3, []tla.TLAValue{iface.Self(), exprRead24.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody3, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("content"), exprRead25},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(respTyp3, []tla.TLAValue{}, GET_RESP(iface))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.sndResp")
			} else {
				var condition36 tla.TLAValue
				condition36, err = iface.Read(req17, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition36.ApplyFunction(tla.MakeTLAString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead26 tla.TLAValue
					exprRead26, err = iface.Read(req17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead4 tla.TLAValue
					indexRead4, err = iface.Read(req17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(fs3, []tla.TLAValue{iface.Self(), indexRead4.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))}, exprRead26.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value")))
					if err != nil {
						return err
					}
					var exprRead27 tla.TLAValue
					exprRead27, err = iface.Read(lastPutBody7, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead28 tla.TLAValue
					exprRead28, err = iface.Read(req17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead29 tla.TLAValue
					exprRead29, err = iface.Read(req17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(lastPutBody7, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("versionNumber"), tla.TLA_PlusSymbol(exprRead27.ApplyFunction(tla.MakeTLAString("versionNumber")), tla.MakeTLANumber(1))},
						{tla.MakeTLAString("key"), exprRead28.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key"))},
						{tla.MakeTLAString("value"), exprRead29.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value"))},
					}))
					if err != nil {
						return err
					}
					err = iface.Write(respBody3, []tla.TLAValue{}, ACK_MSG_BODY(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp3, []tla.TLAValue{}, PUT_RESP(iface))
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet8, []tla.TLAValue{}, tla.TLA_BackslashSymbol(REPLICA_SET(iface), tla.MakeTLASet(iface.Self())))
					if err != nil {
						return err
					}
					err = iface.Write(idx8, []tla.TLAValue{}, tla.MakeTLANumber(1))
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
			req25 := iface.RequireArchetypeResource("AReplica.req")
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
			var condition37 tla.TLAValue
			condition37, err = iface.Read(idx9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition37, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				var condition38 tla.TLAValue
				condition38, err = iface.Read(idx9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition38, iface.Self()).AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndReplicaReqLoop.0", 2) {
					case 0:
						var exprRead31 tla.TLAValue
						exprRead31, err = iface.Read(idx9, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead32 tla.TLAValue
						exprRead32, err = iface.Read(lastPutBody9, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead33 tla.TLAValue
						exprRead33, err = iface.Read(req25, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(repReq1, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("from"), iface.Self()},
							{tla.MakeTLAString("to"), exprRead31},
							{tla.MakeTLAString("body"), exprRead32},
							{tla.MakeTLAString("srcTyp"), PRIMARY_SRC(iface)},
							{tla.MakeTLAString("typ"), PUT_REQ(iface)},
							{tla.MakeTLAString("id"), exprRead33.ApplyFunction(tla.MakeTLAString("id"))},
						}))
						if err != nil {
							return err
						}
						var exprRead34 tla.TLAValue
						exprRead34, err = iface.Read(repReq1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead5 tla.TLAValue
						indexRead5, err = iface.Read(idx9, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net3, []tla.TLAValue{tla.MakeTLATuple(indexRead5, REQ_INDEX(iface))}, exprRead34)
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition39 tla.TLAValue
						condition39, err = iface.Read(idx9, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition40 tla.TLAValue
						condition40, err = iface.Read(fd3, []tla.TLAValue{condition39})
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
				var exprRead30 tla.TLAValue
				exprRead30, err = iface.Read(idx9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx9, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead30, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				if iface.GetConstant("EXPLORE_FAIL")().AsBool() {
					switch iface.NextFairnessCounter("AReplica.sndReplicaReqLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AReplica.sndReplicaReqLoop")
					case 1:
						err = iface.Write(netEnabled3, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), REQ_INDEX(iface))}, tla.TLA_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled3, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))}, tla.TLA_FALSE)
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
			req26 := iface.RequireArchetypeResource("AReplica.req")
			replica2 := iface.RequireArchetypeResource("AReplica.replica")
			netLen0, err := iface.RequireArchetypeResourceRef("AReplica.netLen")
			if err != nil {
				return err
			}
			netEnabled5, err := iface.RequireArchetypeResourceRef("AReplica.netEnabled")
			if err != nil {
				return err
			}
			var condition41 tla.TLAValue
			condition41, err = iface.Read(replicaSet9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_GreaterThanSymbol(tla.TLA_Cardinality(condition41), tla.MakeTLANumber(0)).AsBool() {
				switch iface.NextFairnessCounter("AReplica.rcvReplicaRespLoop.0", 2) {
				case 0:
					var exprRead35 tla.TLAValue
					exprRead35, err = iface.Read(net4, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					err = iface.Write(repResp11, []tla.TLAValue{}, exprRead35)
					if err != nil {
						return err
					}
					var condition42 tla.TLAValue
					condition42, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition43 tla.TLAValue
					condition43, err = iface.Read(replicaSet9, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition44 tla.TLAValue
					condition44, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition45 tla.TLAValue
					condition45, err = iface.Read(fd4, []tla.TLAValue{condition44.ApplyFunction(tla.MakeTLAString("from"))})
					if err != nil {
						return err
					}
					var condition46 tla.TLAValue
					condition46, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition47 tla.TLAValue
					condition47, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition48 tla.TLAValue
					condition48, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition49 tla.TLAValue
					condition49, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition50 tla.TLAValue
					condition50, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition51 tla.TLAValue
					condition51, err = iface.Read(req26, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_InSymbol(condition42.ApplyFunction(tla.MakeTLAString("from")), condition43).AsBool() || condition45.AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition46.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition47.ApplyFunction(tla.MakeTLAString("body")), ACK_MSG_BODY(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition48.ApplyFunction(tla.MakeTLAString("srcTyp")), BACKUP_SRC(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition49.ApplyFunction(tla.MakeTLAString("typ")), PUT_RESP(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition50.ApplyFunction(tla.MakeTLAString("id")), condition51.ApplyFunction(tla.MakeTLAString("id"))).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((((((repResp).from) \\in (replicaSet)) \\/ ((fd)[(repResp).from])) /\\ (((repResp).to) = (self))) /\\ (((repResp).body) = (ACK_MSG_BODY))) /\\ (((repResp).srcTyp) = (BACKUP_SRC))) /\\ (((repResp).typ) = (PUT_RESP))) /\\ (((repResp).id) = ((req).id))", distsys.ErrAssertionFailed)
					}
					var exprRead36 tla.TLAValue
					exprRead36, err = iface.Read(replicaSet9, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead37 tla.TLAValue
					exprRead37, err = iface.Read(repResp11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet9, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead36, tla.MakeTLASet(exprRead37.ApplyFunction(tla.MakeTLAString("from")))))
					if err != nil {
						return err
					}
					// no statements
				case 1:
					var exprRead38 tla.TLAValue
					exprRead38, err = iface.Read(replicaSet9, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(replica2, []tla.TLAValue{}, tla.TLAChoose(exprRead38, func(element0 tla.TLAValue) bool {
						var r0 tla.TLAValue = element0
						_ = r0
						return tla.TLA_TRUE.AsBool()
					}))
					if err != nil {
						return err
					}
					var condition52 tla.TLAValue
					condition52, err = iface.Read(replica2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition53 tla.TLAValue
					condition53, err = iface.Read(fd4, []tla.TLAValue{condition52})
					if err != nil {
						return err
					}
					var condition54 tla.TLAValue
					condition54, err = iface.Read(netLen0, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(condition53.AsBool() && tla.TLA_EqualsSymbol(condition54, tla.MakeTLANumber(0)).AsBool()).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var exprRead39 tla.TLAValue
					exprRead39, err = iface.Read(replicaSet9, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead40 tla.TLAValue
					exprRead40, err = iface.Read(replica2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(replicaSet9, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead39, tla.MakeTLASet(exprRead40)))
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
						err = iface.Write(netEnabled5, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), REQ_INDEX(iface))}, tla.TLA_FALSE)
						if err != nil {
							return err
						}
						err = iface.Write(netEnabled5, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))}, tla.TLA_FALSE)
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
			req27 := iface.RequireArchetypeResource("AReplica.req")
			respBody5 := iface.RequireArchetypeResource("AReplica.respBody")
			respTyp5 := iface.RequireArchetypeResource("AReplica.respTyp")
			net5, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			var exprRead41 tla.TLAValue
			exprRead41, err = iface.Read(req27, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead42 tla.TLAValue
			exprRead42, err = iface.Read(respBody5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead43 tla.TLAValue
			exprRead43, err = iface.Read(respTyp5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead44 tla.TLAValue
			exprRead44, err = iface.Read(req27, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp3, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("to"), exprRead41.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), exprRead42},
				{tla.MakeTLAString("srcTyp"), PRIMARY_SRC(iface)},
				{tla.MakeTLAString("typ"), exprRead43},
				{tla.MakeTLAString("id"), exprRead44.ApplyFunction(tla.MakeTLAString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead45 tla.TLAValue
			exprRead45, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead6 tla.TLAValue
			indexRead6, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net5, []tla.TLAValue{tla.MakeTLATuple(indexRead6.ApplyFunction(tla.MakeTLAString("to")), RESP_INDEX(iface))}, exprRead45)
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.replicaLoop")
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
			err = iface.Write(fd6, []tla.TLAValue{iface.Self()}, tla.TLA_TRUE)
			if err != nil {
				return err
			}
			err = iface.Write(primary2, []tla.TLAValue{}, iface.Self())
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
		Name: "APutClient.putClientLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			body := iface.RequireArchetypeResource("APutClient.body")
			input, err := iface.RequireArchetypeResourceRef("APutClient.input")
			if err != nil {
				return err
			}
			if iface.GetConstant("PUT_CLIENT_RUN")().AsBool() {
				var exprRead46 tla.TLAValue
				exprRead46, err = iface.Read(input, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(body, []tla.TLAValue{}, exprRead46)
				if err != nil {
					return err
				}
				return iface.Goto("APutClient.sndPutReq")
			} else {
				return iface.Goto("APutClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "APutClient.sndPutReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			replica5 := iface.RequireArchetypeResource("APutClient.replica")
			primary3, err := iface.RequireArchetypeResourceRef("APutClient.primary")
			if err != nil {
				return err
			}
			req29 := iface.RequireArchetypeResource("APutClient.req")
			body0 := iface.RequireArchetypeResource("APutClient.body")
			net6, err := iface.RequireArchetypeResourceRef("APutClient.net")
			if err != nil {
				return err
			}
			fd7, err := iface.RequireArchetypeResourceRef("APutClient.fd")
			if err != nil {
				return err
			}
			var exprRead47 tla.TLAValue
			exprRead47, err = iface.Read(primary3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(replica5, []tla.TLAValue{}, exprRead47)
			if err != nil {
				return err
			}
			var condition55 tla.TLAValue
			condition55, err = iface.Read(replica5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_NotEqualsSymbol(condition55, NULL(iface)).AsBool() {
				switch iface.NextFairnessCounter("APutClient.sndPutReq.0", 2) {
				case 0:
					var exprRead48 tla.TLAValue
					exprRead48, err = iface.Read(replica5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead49 tla.TLAValue
					exprRead49, err = iface.Read(body0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(req29, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("from"), iface.Self()},
						{tla.MakeTLAString("to"), exprRead48},
						{tla.MakeTLAString("body"), exprRead49},
						{tla.MakeTLAString("srcTyp"), CLIENT_SRC(iface)},
						{tla.MakeTLAString("typ"), PUT_REQ(iface)},
						{tla.MakeTLAString("id"), tla.MakeTLANumber(1)},
					}))
					if err != nil {
						return err
					}
					var exprRead50 tla.TLAValue
					exprRead50, err = iface.Read(req29, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead7 tla.TLAValue
					indexRead7, err = iface.Read(req29, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net6, []tla.TLAValue{tla.MakeTLATuple(indexRead7.ApplyFunction(tla.MakeTLAString("to")), REQ_INDEX(iface))}, exprRead50)
					if err != nil {
						return err
					}
					return iface.Goto("APutClient.rcvPutResp")
				case 1:
					var condition56 tla.TLAValue
					condition56, err = iface.Read(replica5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition57 tla.TLAValue
					condition57, err = iface.Read(fd7, []tla.TLAValue{condition56})
					if err != nil {
						return err
					}
					if !condition57.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("APutClient.sndPutReq")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("APutClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "APutClient.rcvPutResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp6 := iface.RequireArchetypeResource("APutClient.resp")
			net7, err := iface.RequireArchetypeResourceRef("APutClient.net")
			if err != nil {
				return err
			}
			replica9 := iface.RequireArchetypeResource("APutClient.replica")
			output, err := iface.RequireArchetypeResourceRef("APutClient.output")
			if err != nil {
				return err
			}
			fd8, err := iface.RequireArchetypeResourceRef("APutClient.fd")
			if err != nil {
				return err
			}
			netLen1, err := iface.RequireArchetypeResourceRef("APutClient.netLen")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("APutClient.rcvPutResp.0", 2) {
			case 0:
				var exprRead51 tla.TLAValue
				exprRead51, err = iface.Read(net7, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp6, []tla.TLAValue{}, exprRead51)
				if err != nil {
					return err
				}
				var condition58 tla.TLAValue
				condition58, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition59 tla.TLAValue
				condition59, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition60 tla.TLAValue
				condition60, err = iface.Read(replica9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition61 tla.TLAValue
				condition61, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition62 tla.TLAValue
				condition62, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition63 tla.TLAValue
				condition63, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition64 tla.TLAValue
				condition64, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition58.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition59.ApplyFunction(tla.MakeTLAString("from")), condition60).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition61.ApplyFunction(tla.MakeTLAString("body")), ACK_MSG_BODY(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition62.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition63.ApplyFunction(tla.MakeTLAString("typ")), PUT_RESP(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition64.ApplyFunction(tla.MakeTLAString("id")), tla.MakeTLANumber(1)).AsBool()).AsBool() {
					return fmt.Errorf("%w: (((((((resp).to) = (self)) /\\ (((resp).from) = (replica))) /\\ (((resp).body) = (ACK_MSG_BODY))) /\\ (((resp).srcTyp) = (PRIMARY_SRC))) /\\ (((resp).typ) = (PUT_RESP))) /\\ (((resp).id) = (1))", distsys.ErrAssertionFailed)
				}
				var exprRead52 tla.TLAValue
				exprRead52, err = iface.Read(resp6, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(output, []tla.TLAValue{}, exprRead52)
				if err != nil {
					return err
				}
				return iface.Goto("APutClient.putClientLoop")
			case 1:
				var condition65 tla.TLAValue
				condition65, err = iface.Read(replica9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition66 tla.TLAValue
				condition66, err = iface.Read(fd8, []tla.TLAValue{condition65})
				if err != nil {
					return err
				}
				var condition67 tla.TLAValue
				condition67, err = iface.Read(netLen1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(condition66.AsBool() && tla.TLA_EqualsSymbol(condition67, tla.MakeTLANumber(0)).AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				return iface.Goto("APutClient.sndPutReq")
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "APutClient.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AGetClient.getClientLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			body1 := iface.RequireArchetypeResource("AGetClient.body")
			input0, err := iface.RequireArchetypeResourceRef("AGetClient.input")
			if err != nil {
				return err
			}
			if iface.GetConstant("GET_CLIENT_RUN")().AsBool() {
				var exprRead53 tla.TLAValue
				exprRead53, err = iface.Read(input0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(body1, []tla.TLAValue{}, exprRead53)
				if err != nil {
					return err
				}
				return iface.Goto("AGetClient.sndGetReq")
			} else {
				return iface.Goto("AGetClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AGetClient.sndGetReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			replica11 := iface.RequireArchetypeResource("AGetClient.replica")
			primary4, err := iface.RequireArchetypeResourceRef("AGetClient.primary")
			if err != nil {
				return err
			}
			req32 := iface.RequireArchetypeResource("AGetClient.req")
			body2 := iface.RequireArchetypeResource("AGetClient.body")
			net8, err := iface.RequireArchetypeResourceRef("AGetClient.net")
			if err != nil {
				return err
			}
			fd9, err := iface.RequireArchetypeResourceRef("AGetClient.fd")
			if err != nil {
				return err
			}
			var exprRead54 tla.TLAValue
			exprRead54, err = iface.Read(primary4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(replica11, []tla.TLAValue{}, exprRead54)
			if err != nil {
				return err
			}
			var condition68 tla.TLAValue
			condition68, err = iface.Read(replica11, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_NotEqualsSymbol(condition68, NULL(iface)).AsBool() {
				switch iface.NextFairnessCounter("AGetClient.sndGetReq.0", 2) {
				case 0:
					var exprRead55 tla.TLAValue
					exprRead55, err = iface.Read(replica11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead56 tla.TLAValue
					exprRead56, err = iface.Read(body2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(req32, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("from"), iface.Self()},
						{tla.MakeTLAString("to"), exprRead55},
						{tla.MakeTLAString("body"), exprRead56},
						{tla.MakeTLAString("srcTyp"), CLIENT_SRC(iface)},
						{tla.MakeTLAString("typ"), GET_REQ(iface)},
						{tla.MakeTLAString("id"), tla.MakeTLANumber(2)},
					}))
					if err != nil {
						return err
					}
					var exprRead57 tla.TLAValue
					exprRead57, err = iface.Read(req32, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead8 tla.TLAValue
					indexRead8, err = iface.Read(req32, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net8, []tla.TLAValue{tla.MakeTLATuple(indexRead8.ApplyFunction(tla.MakeTLAString("to")), REQ_INDEX(iface))}, exprRead57)
					if err != nil {
						return err
					}
					return iface.Goto("AGetClient.rcvGetResp")
				case 1:
					var condition69 tla.TLAValue
					condition69, err = iface.Read(replica11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition70 tla.TLAValue
					condition70, err = iface.Read(fd9, []tla.TLAValue{condition69})
					if err != nil {
						return err
					}
					if !condition70.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("AGetClient.sndGetReq")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AGetClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AGetClient.rcvGetResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp14 := iface.RequireArchetypeResource("AGetClient.resp")
			net9, err := iface.RequireArchetypeResourceRef("AGetClient.net")
			if err != nil {
				return err
			}
			replica15 := iface.RequireArchetypeResource("AGetClient.replica")
			output0, err := iface.RequireArchetypeResourceRef("AGetClient.output")
			if err != nil {
				return err
			}
			fd10, err := iface.RequireArchetypeResourceRef("AGetClient.fd")
			if err != nil {
				return err
			}
			netLen2, err := iface.RequireArchetypeResourceRef("AGetClient.netLen")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AGetClient.rcvGetResp.0", 2) {
			case 0:
				var exprRead58 tla.TLAValue
				exprRead58, err = iface.Read(net9, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp14, []tla.TLAValue{}, exprRead58)
				if err != nil {
					return err
				}
				var condition71 tla.TLAValue
				condition71, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition72 tla.TLAValue
				condition72, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition73 tla.TLAValue
				condition73, err = iface.Read(replica15, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition74 tla.TLAValue
				condition74, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition75 tla.TLAValue
				condition75, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition76 tla.TLAValue
				condition76, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition71.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition72.ApplyFunction(tla.MakeTLAString("from")), condition73).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition74.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition75.ApplyFunction(tla.MakeTLAString("typ")), GET_RESP(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition76.ApplyFunction(tla.MakeTLAString("id")), tla.MakeTLANumber(2)).AsBool()).AsBool() {
					return fmt.Errorf("%w: ((((((resp).to) = (self)) /\\ (((resp).from) = (replica))) /\\ (((resp).srcTyp) = (PRIMARY_SRC))) /\\ (((resp).typ) = (GET_RESP))) /\\ (((resp).id) = (2))", distsys.ErrAssertionFailed)
				}
				var exprRead59 tla.TLAValue
				exprRead59, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(output0, []tla.TLAValue{}, exprRead59)
				if err != nil {
					return err
				}
				return iface.Goto("AGetClient.getClientLoop")
			case 1:
				var condition77 tla.TLAValue
				condition77, err = iface.Read(replica15, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition78 tla.TLAValue
				condition78, err = iface.Read(fd10, []tla.TLAValue{condition77})
				if err != nil {
					return err
				}
				var condition79 tla.TLAValue
				condition79, err = iface.Read(netLen2, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(condition78.AsBool() && tla.TLA_EqualsSymbol(condition79, tla.MakeTLANumber(0)).AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				return iface.Goto("AGetClient.sndGetReq")
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AGetClient.Done",
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
			input1, err := iface.RequireArchetypeResourceRef("AClient.input")
			if err != nil {
				return err
			}
			idx16 := iface.RequireArchetypeResource("AClient.idx")
			resp21 := iface.RequireArchetypeResource("AClient.resp")
			net10, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				switch iface.NextFairnessCounter("AClient.clientLoop.0", 2) {
				case 0:
					var exprRead60 tla.TLAValue
					exprRead60, err = iface.Read(input1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(msg, []tla.TLAValue{}, exprRead60)
					if err != nil {
						return err
					}
					var exprRead61 tla.TLAValue
					exprRead61, err = iface.Read(idx16, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(idx16, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead61, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					return iface.Goto("AClient.sndReq")
				case 1:
					var exprRead62 tla.TLAValue
					exprRead62, err = iface.Read(net10, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
					if err != nil {
						return err
					}
					err = iface.Write(resp21, []tla.TLAValue{}, exprRead62)
					if err != nil {
						return err
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
		Name: "AClient.sndReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			replica17 := iface.RequireArchetypeResource("AClient.replica")
			primary5, err := iface.RequireArchetypeResourceRef("AClient.primary")
			if err != nil {
				return err
			}
			req35 := iface.RequireArchetypeResource("AClient.req")
			msg0 := iface.RequireArchetypeResource("AClient.msg")
			idx18 := iface.RequireArchetypeResource("AClient.idx")
			net11, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			fd11, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			var exprRead63 tla.TLAValue
			exprRead63, err = iface.Read(primary5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(replica17, []tla.TLAValue{}, exprRead63)
			if err != nil {
				return err
			}
			var condition80 tla.TLAValue
			condition80, err = iface.Read(replica17, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_NotEqualsSymbol(condition80, NULL(iface)).AsBool() {
				switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
				case 0:
					var exprRead64 tla.TLAValue
					exprRead64, err = iface.Read(replica17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead65 tla.TLAValue
					exprRead65, err = iface.Read(msg0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead66 tla.TLAValue
					exprRead66, err = iface.Read(msg0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead67 tla.TLAValue
					exprRead67, err = iface.Read(idx18, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(req35, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("from"), iface.Self()},
						{tla.MakeTLAString("to"), exprRead64},
						{tla.MakeTLAString("body"), exprRead65.ApplyFunction(tla.MakeTLAString("body"))},
						{tla.MakeTLAString("srcTyp"), CLIENT_SRC(iface)},
						{tla.MakeTLAString("typ"), exprRead66.ApplyFunction(tla.MakeTLAString("typ"))},
						{tla.MakeTLAString("id"), exprRead67},
					}))
					if err != nil {
						return err
					}
					var exprRead68 tla.TLAValue
					exprRead68, err = iface.Read(req35, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead9 tla.TLAValue
					indexRead9, err = iface.Read(req35, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net11, []tla.TLAValue{tla.MakeTLATuple(indexRead9.ApplyFunction(tla.MakeTLAString("to")), REQ_INDEX(iface))}, exprRead68)
					if err != nil {
						return err
					}
					return iface.Goto("AClient.rcvResp")
				case 1:
					var condition81 tla.TLAValue
					condition81, err = iface.Read(replica17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition82 tla.TLAValue
					condition82, err = iface.Read(fd11, []tla.TLAValue{condition81})
					if err != nil {
						return err
					}
					if !condition82.AsBool() {
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
			resp22 := iface.RequireArchetypeResource("AClient.resp")
			net12, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			idx19 := iface.RequireArchetypeResource("AClient.idx")
			msg2 := iface.RequireArchetypeResource("AClient.msg")
			replica21 := iface.RequireArchetypeResource("AClient.replica")
			output1, err := iface.RequireArchetypeResourceRef("AClient.output")
			if err != nil {
				return err
			}
			fd12, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			netLen3, err := iface.RequireArchetypeResourceRef("AClient.netLen")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AClient.rcvResp.0", 2) {
			case 0:
				var exprRead69 tla.TLAValue
				exprRead69, err = iface.Read(net12, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp22, []tla.TLAValue{}, exprRead69)
				if err != nil {
					return err
				}
				var condition83 tla.TLAValue
				condition83, err = iface.Read(resp22, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition84 tla.TLAValue
				condition84, err = iface.Read(idx19, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition83.ApplyFunction(tla.MakeTLAString("id")), condition84).AsBool() {
					return iface.Goto("AClient.rcvResp")
				} else {
					var condition85 tla.TLAValue
					condition85, err = iface.Read(msg2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_EqualsSymbol(condition85.ApplyFunction(tla.MakeTLAString("typ")), PUT_REQ(iface)).AsBool() {
						var condition86 tla.TLAValue
						condition86, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition87 tla.TLAValue
						condition87, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition88 tla.TLAValue
						condition88, err = iface.Read(replica21, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition89 tla.TLAValue
						condition89, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition90 tla.TLAValue
						condition90, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition91 tla.TLAValue
						condition91, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition92 tla.TLAValue
						condition92, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition93 tla.TLAValue
						condition93, err = iface.Read(idx19, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition86.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition87.ApplyFunction(tla.MakeTLAString("from")), condition88).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition89.ApplyFunction(tla.MakeTLAString("body")), ACK_MSG_BODY(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition90.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition91.ApplyFunction(tla.MakeTLAString("typ")), PUT_RESP(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition92.ApplyFunction(tla.MakeTLAString("id")), condition93).AsBool()).AsBool() {
							return fmt.Errorf("%w: (((((((resp).to) = (self)) /\\ (((resp).from) = (replica))) /\\ (((resp).body) = (ACK_MSG_BODY))) /\\ (((resp).srcTyp) = (PRIMARY_SRC))) /\\ (((resp).typ) = (PUT_RESP))) /\\ (((resp).id) = (idx))", distsys.ErrAssertionFailed)
						}
						var exprRead70 tla.TLAValue
						exprRead70, err = iface.Read(resp22, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(output1, []tla.TLAValue{}, exprRead70.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("content")))
						if err != nil {
							return err
						}
						return iface.Goto("AClient.clientLoop")
					} else {
						var condition94 tla.TLAValue
						condition94, err = iface.Read(msg2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_EqualsSymbol(condition94.ApplyFunction(tla.MakeTLAString("typ")), GET_REQ(iface)).AsBool() {
							var condition95 tla.TLAValue
							condition95, err = iface.Read(resp22, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition96 tla.TLAValue
							condition96, err = iface.Read(resp22, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition97 tla.TLAValue
							condition97, err = iface.Read(replica21, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition98 tla.TLAValue
							condition98, err = iface.Read(resp22, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition99 tla.TLAValue
							condition99, err = iface.Read(resp22, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition100 tla.TLAValue
							condition100, err = iface.Read(resp22, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition101 tla.TLAValue
							condition101, err = iface.Read(idx19, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if !tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition95.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() && tla.TLA_EqualsSymbol(condition96.ApplyFunction(tla.MakeTLAString("from")), condition97).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition98.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition99.ApplyFunction(tla.MakeTLAString("typ")), GET_RESP(iface)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition100.ApplyFunction(tla.MakeTLAString("id")), condition101).AsBool()).AsBool() {
								return fmt.Errorf("%w: ((((((resp).to) = (self)) /\\ (((resp).from) = (replica))) /\\ (((resp).srcTyp) = (PRIMARY_SRC))) /\\ (((resp).typ) = (GET_RESP))) /\\ (((resp).id) = (idx))", distsys.ErrAssertionFailed)
							}
							var exprRead71 tla.TLAValue
							exprRead71, err = iface.Read(resp22, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(output1, []tla.TLAValue{}, exprRead71.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("content")))
							if err != nil {
								return err
							}
							return iface.Goto("AClient.clientLoop")
						} else {
							if !tla.TLA_FALSE.AsBool() {
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
				var condition102 tla.TLAValue
				condition102, err = iface.Read(replica21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition103 tla.TLAValue
				condition103, err = iface.Read(fd12, []tla.TLAValue{condition102})
				if err != nil {
					return err
				}
				var condition104 tla.TLAValue
				condition104, err = iface.Read(netLen3, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), RESP_INDEX(iface))})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(condition103.AsBool() && tla.TLA_EqualsSymbol(condition104, tla.MakeTLANumber(0)).AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
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
		iface.EnsureArchetypeResourceLocal("AReplica.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.respBody", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.respTyp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.idx", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.repReq", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.repResp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.replicaSet", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.shouldSync", tla.TLA_FALSE)
		iface.EnsureArchetypeResourceLocal("AReplica.lastPutBody", tla.MakeTLARecord([]tla.TLARecordField{
			{tla.MakeTLAString("versionNumber"), tla.MakeTLANumber(0)},
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.replica", tla.TLAValue{})
	},
}

var APutClient = distsys.MPCalArchetype{
	Name:              "APutClient",
	Label:             "APutClient.putClientLoop",
	RequiredRefParams: []string{"APutClient.net", "APutClient.fd", "APutClient.primary", "APutClient.netLen", "APutClient.input", "APutClient.output"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("APutClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("APutClient.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("APutClient.body", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("APutClient.replica", tla.TLAValue{})
	},
}

var AGetClient = distsys.MPCalArchetype{
	Name:              "AGetClient",
	Label:             "AGetClient.getClientLoop",
	RequiredRefParams: []string{"AGetClient.net", "AGetClient.fd", "AGetClient.primary", "AGetClient.netLen", "AGetClient.input", "AGetClient.output"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AGetClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AGetClient.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AGetClient.body", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AGetClient.replica", tla.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.replica", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.idx", tla.MakeTLANumber(0))
	},
}
