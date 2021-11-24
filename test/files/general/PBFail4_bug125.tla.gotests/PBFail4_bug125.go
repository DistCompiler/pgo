package pbfail

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func NUM_NODES(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
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
func ACK_MSG(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("ack-body")
}
func KEY1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("KEY1")
}
func VALUE1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("VALUE1")
}
func TEMP_VAL(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("TEMP")
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
				return iface.Goto("AReplica.rcvMsg")
			} else {
				return iface.Goto("AReplica.failLabel")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AReplica.msg")
			net, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AReplica.rcvMsg.0", 2) {
			case 0:
				var exprRead tla.TLAValue
				exprRead, err = iface.Read(net, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), GET_REQ(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, []tla.TLAValue{}, exprRead)
				if err != nil {
					return err
				}
				// no statements
			case 1:
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(net, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PUT_REQ(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, []tla.TLAValue{}, exprRead0)
				if err != nil {
					return err
				}
				// no statements
			default:
				panic("current branch of either matches no code paths!")
			}
			var condition tla.TLAValue
			condition, err = iface.Read(msg, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() {
				return fmt.Errorf("%w: ((msg).to) = (self)", distsys.ErrAssertionFailed)
			}
			var condition0 tla.TLAValue
			condition0, err = iface.Read(msg, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition0.ApplyFunction(tla.MakeTLAString("srcTyp")), CLIENT_SRC(iface)).AsBool() {
				return iface.Goto("AReplica.handlePrimary")
			} else {
				var condition1 tla.TLAValue
				condition1, err = iface.Read(msg, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition1.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
					return iface.Goto("AReplica.handleBackup")
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
			msg4 := iface.RequireArchetypeResource("AReplica.msg")
			respBody := iface.RequireArchetypeResource("AReplica.respBody")
			fs, err := iface.RequireArchetypeResourceRef("AReplica.fs")
			if err != nil {
				return err
			}
			respTyp := iface.RequireArchetypeResource("AReplica.respTyp")
			resp := iface.RequireArchetypeResource("AReplica.resp")
			net1, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			var condition2 tla.TLAValue
			condition2, err = iface.Read(msg4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition2.ApplyFunction(tla.MakeTLAString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(msg4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead2 tla.TLAValue
				exprRead2, err = iface.Read(fs, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), exprRead1.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key")))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody, []tla.TLAValue{}, exprRead2)
				if err != nil {
					return err
				}
				err = iface.Write(respTyp, []tla.TLAValue{}, GET_RESP(iface))
				if err != nil {
					return err
				}
				// no statements
			} else {
				var condition3 tla.TLAValue
				condition3, err = iface.Read(msg4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition3.ApplyFunction(tla.MakeTLAString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead3 tla.TLAValue
					exprRead3, err = iface.Read(msg4, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead tla.TLAValue
					indexRead, err = iface.Read(msg4, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(fs, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), indexRead.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key")))}, exprRead3.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody, []tla.TLAValue{}, ACK_MSG(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp, []tla.TLAValue{}, PUT_RESP(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				// no statements
			}
			var exprRead4 tla.TLAValue
			exprRead4, err = iface.Read(msg4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead5 tla.TLAValue
			exprRead5, err = iface.Read(respBody, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead6 tla.TLAValue
			exprRead6, err = iface.Read(respTyp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead7 tla.TLAValue
			exprRead7, err = iface.Read(msg4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("to"), exprRead4.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), exprRead5},
				{tla.MakeTLAString("srcTyp"), BACKUP_SRC(iface)},
				{tla.MakeTLAString("typ"), exprRead6},
				{tla.MakeTLAString("id"), exprRead7.ApplyFunction(tla.MakeTLAString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead8 tla.TLAValue
			exprRead8, err = iface.Read(resp, []tla.TLAValue{})
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
			err = iface.Write(net1, []tla.TLAValue{tla.MakeTLATuple(indexRead0.ApplyFunction(tla.MakeTLAString("to")), indexRead1.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead8)
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.replicaLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.handlePrimary",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg11 := iface.RequireArchetypeResource("AReplica.msg")
			respBody2 := iface.RequireArchetypeResource("AReplica.respBody")
			fs1, err := iface.RequireArchetypeResourceRef("AReplica.fs")
			if err != nil {
				return err
			}
			respTyp2 := iface.RequireArchetypeResource("AReplica.respTyp")
			var condition4 tla.TLAValue
			condition4, err = iface.Read(msg11, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition4.ApplyFunction(tla.MakeTLAString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead9 tla.TLAValue
				exprRead9, err = iface.Read(msg11, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead10 tla.TLAValue
				exprRead10, err = iface.Read(fs1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), exprRead9.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key")))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody2, []tla.TLAValue{}, exprRead10)
				if err != nil {
					return err
				}
				err = iface.Write(respTyp2, []tla.TLAValue{}, GET_RESP(iface))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.sndResp")
			} else {
				var condition5 tla.TLAValue
				condition5, err = iface.Read(msg11, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition5.ApplyFunction(tla.MakeTLAString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead11 tla.TLAValue
					exprRead11, err = iface.Read(msg11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead2 tla.TLAValue
					indexRead2, err = iface.Read(msg11, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(fs1, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), indexRead2.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("key")))}, exprRead11.ApplyFunction(tla.MakeTLAString("body")).ApplyFunction(tla.MakeTLAString("value")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody2, []tla.TLAValue{}, ACK_MSG(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp2, []tla.TLAValue{}, PUT_RESP(iface))
					if err != nil {
						return err
					}
					return iface.Goto("AReplica.sndReplicaMsg")
				} else {
					return iface.Goto("AReplica.sndReplicaMsg")
				}
				// no statements
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndReplicaMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx := iface.RequireArchetypeResource("AReplica.idx")
			err = iface.Write(idx, []tla.TLAValue{}, tla.MakeTLANumber(1))
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.sndMsgLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndMsgLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx0 := iface.RequireArchetypeResource("AReplica.idx")
			var condition6 tla.TLAValue
			condition6, err = iface.Read(idx0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition6, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				return iface.Goto("AReplica.sndMsg")
			} else {
				return iface.Goto("AReplica.rcvReplicaMsg")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			idx1 := iface.RequireArchetypeResource("AReplica.idx")
			repMsg := iface.RequireArchetypeResource("AReplica.repMsg")
			msg16 := iface.RequireArchetypeResource("AReplica.msg")
			net2, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			var condition7 tla.TLAValue
			condition7, err = iface.Read(idx1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition8 tla.TLAValue
			condition8, err = iface.Read(fd, []tla.TLAValue{condition7})
			if err != nil {
				return err
			}
			var condition9 tla.TLAValue
			condition9, err = iface.Read(idx1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition8, tla.TLA_TRUE).AsBool() && tla.TLA_NotEqualsSymbol(condition9, iface.Self()).AsBool()).AsBool() {
				var exprRead12 tla.TLAValue
				exprRead12, err = iface.Read(idx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead13 tla.TLAValue
				exprRead13, err = iface.Read(msg16, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead14 tla.TLAValue
				exprRead14, err = iface.Read(msg16, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(repMsg, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("from"), iface.Self()},
					{tla.MakeTLAString("to"), exprRead12},
					{tla.MakeTLAString("body"), exprRead13.ApplyFunction(tla.MakeTLAString("body"))},
					{tla.MakeTLAString("srcTyp"), PRIMARY_SRC(iface)},
					{tla.MakeTLAString("typ"), PUT_REQ(iface)},
					{tla.MakeTLAString("id"), exprRead14.ApplyFunction(tla.MakeTLAString("id"))},
				}))
				if err != nil {
					return err
				}
				var exprRead15 tla.TLAValue
				exprRead15, err = iface.Read(repMsg, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead3 tla.TLAValue
				indexRead3, err = iface.Read(idx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net2, []tla.TLAValue{tla.MakeTLATuple(indexRead3, PUT_REQ(iface))}, exprRead15)
				if err != nil {
					return err
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead16 tla.TLAValue
			exprRead16, err = iface.Read(idx1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(idx1, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead16, tla.MakeTLANumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.sndMsgLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvReplicaMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx7 := iface.RequireArchetypeResource("AReplica.idx")
			err = iface.Write(idx7, []tla.TLAValue{}, tla.MakeTLANumber(1))
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.rcvMsgLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvMsgLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx8 := iface.RequireArchetypeResource("AReplica.idx")
			var condition10 tla.TLAValue
			condition10, err = iface.Read(idx8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition10, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				return iface.Goto("AReplica.rcvMsgFromReplica")
			} else {
				return iface.Goto("AReplica.sndResp")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.rcvMsgFromReplica",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd0, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			idx9 := iface.RequireArchetypeResource("AReplica.idx")
			rep := iface.RequireArchetypeResource("AReplica.rep")
			net3, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			msg18 := iface.RequireArchetypeResource("AReplica.msg")
			var condition11 tla.TLAValue
			condition11, err = iface.Read(idx9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition12 tla.TLAValue
			condition12, err = iface.Read(fd0, []tla.TLAValue{condition11})
			if err != nil {
				return err
			}
			var condition13 tla.TLAValue
			condition13, err = iface.Read(idx9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition12, tla.TLA_TRUE).AsBool() && tla.TLA_NotEqualsSymbol(condition13, iface.Self()).AsBool()).AsBool() {
				var exprRead17 tla.TLAValue
				exprRead17, err = iface.Read(net3, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PUT_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(rep, []tla.TLAValue{}, exprRead17)
				if err != nil {
					return err
				}
				var condition14 tla.TLAValue
				condition14, err = iface.Read(rep, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition15 tla.TLAValue
				condition15, err = iface.Read(idx9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition14.ApplyFunction(tla.MakeTLAString("from")), condition15).AsBool() {
					return fmt.Errorf("%w: ((rep).from) = (idx)", distsys.ErrAssertionFailed)
				}
				var condition16 tla.TLAValue
				condition16, err = iface.Read(rep, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition16.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((rep).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition17 tla.TLAValue
				condition17, err = iface.Read(rep, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition17.ApplyFunction(tla.MakeTLAString("body")), ACK_MSG(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
				}
				var condition18 tla.TLAValue
				condition18, err = iface.Read(rep, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition18.ApplyFunction(tla.MakeTLAString("srcTyp")), BACKUP_SRC(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).srcTyp) = (BACKUP_SRC)", distsys.ErrAssertionFailed)
				}
				var condition19 tla.TLAValue
				condition19, err = iface.Read(rep, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition19.ApplyFunction(tla.MakeTLAString("typ")), PUT_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
				}
				var condition20 tla.TLAValue
				condition20, err = iface.Read(rep, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition21 tla.TLAValue
				condition21, err = iface.Read(msg18, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition20.ApplyFunction(tla.MakeTLAString("id")), condition21.ApplyFunction(tla.MakeTLAString("id"))).AsBool() {
					return fmt.Errorf("%w: ((rep).id) = ((msg).id)", distsys.ErrAssertionFailed)
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead18 tla.TLAValue
			exprRead18, err = iface.Read(idx9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(idx9, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead18, tla.MakeTLANumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.rcvMsgLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.sndResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp3 := iface.RequireArchetypeResource("AReplica.resp")
			msg19 := iface.RequireArchetypeResource("AReplica.msg")
			respBody4 := iface.RequireArchetypeResource("AReplica.respBody")
			respTyp4 := iface.RequireArchetypeResource("AReplica.respTyp")
			net4, err := iface.RequireArchetypeResourceRef("AReplica.net")
			if err != nil {
				return err
			}
			var exprRead19 tla.TLAValue
			exprRead19, err = iface.Read(msg19, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead20 tla.TLAValue
			exprRead20, err = iface.Read(respBody4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead21 tla.TLAValue
			exprRead21, err = iface.Read(respTyp4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead22 tla.TLAValue
			exprRead22, err = iface.Read(msg19, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp3, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("to"), exprRead19.ApplyFunction(tla.MakeTLAString("from"))},
				{tla.MakeTLAString("body"), exprRead20},
				{tla.MakeTLAString("srcTyp"), PRIMARY_SRC(iface)},
				{tla.MakeTLAString("typ"), exprRead21},
				{tla.MakeTLAString("id"), exprRead22.ApplyFunction(tla.MakeTLAString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead23 tla.TLAValue
			exprRead23, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead4 tla.TLAValue
			indexRead4, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead5 tla.TLAValue
			indexRead5, err = iface.Read(resp3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net4, []tla.TLAValue{tla.MakeTLATuple(indexRead4.ApplyFunction(tla.MakeTLAString("to")), indexRead5.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead23)
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
			fd1, err := iface.RequireArchetypeResourceRef("AReplica.fd")
			if err != nil {
				return err
			}
			err = iface.Write(fd1, []tla.TLAValue{iface.Self()}, tla.TLA_FALSE)
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
		Name: "AClient.sndPutReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx14 := iface.RequireArchetypeResource("AClient.idx")
			err = iface.Write(idx14, []tla.TLAValue{}, tla.MakeTLANumber(1))
			if err != nil {
				return err
			}
			return iface.Goto("AClient.sndPutReqLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndPutReqLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx15 := iface.RequireArchetypeResource("AClient.idx")
			var condition22 tla.TLAValue
			condition22, err = iface.Read(idx15, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition22, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				return iface.Goto("AClient.sndPutMsg")
			} else {
				return iface.Goto("AClient.rcvPutResp")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndPutMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd2, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			idx16 := iface.RequireArchetypeResource("AClient.idx")
			body := iface.RequireArchetypeResource("AClient.body")
			req := iface.RequireArchetypeResource("AClient.req")
			net5, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var condition23 tla.TLAValue
			condition23, err = iface.Read(idx16, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition24 tla.TLAValue
			condition24, err = iface.Read(fd2, []tla.TLAValue{condition23})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition24, tla.TLA_TRUE).AsBool() {
				err = iface.Write(body, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("key"), KEY1(iface)},
					{tla.MakeTLAString("value"), VALUE1(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead24 tla.TLAValue
				exprRead24, err = iface.Read(idx16, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead25 tla.TLAValue
				exprRead25, err = iface.Read(body, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("from"), iface.Self()},
					{tla.MakeTLAString("to"), exprRead24},
					{tla.MakeTLAString("body"), exprRead25},
					{tla.MakeTLAString("srcTyp"), CLIENT_SRC(iface)},
					{tla.MakeTLAString("typ"), PUT_REQ(iface)},
					{tla.MakeTLAString("id"), tla.MakeTLANumber(1)},
				}))
				if err != nil {
					return err
				}
				var exprRead26 tla.TLAValue
				exprRead26, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead6 tla.TLAValue
				indexRead6, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead7 tla.TLAValue
				indexRead7, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net5, []tla.TLAValue{tla.MakeTLATuple(indexRead6.ApplyFunction(tla.MakeTLAString("to")), indexRead7.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead26)
				if err != nil {
					return err
				}
				return iface.Goto("AClient.rcvPutResp")
			} else {
				return iface.Goto("AClient.sndPutReqLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.rcvPutResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd3, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			idx18 := iface.RequireArchetypeResource("AClient.idx")
			resp7 := iface.RequireArchetypeResource("AClient.resp")
			net6, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var condition25 tla.TLAValue
			condition25, err = iface.Read(idx18, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition26 tla.TLAValue
			condition26, err = iface.Read(fd3, []tla.TLAValue{condition25})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition26, tla.TLA_TRUE).AsBool() {
				var exprRead27 tla.TLAValue
				exprRead27, err = iface.Read(net6, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), PUT_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp7, []tla.TLAValue{}, exprRead27)
				if err != nil {
					return err
				}
				var condition27 tla.TLAValue
				condition27, err = iface.Read(resp7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition27.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition28 tla.TLAValue
				condition28, err = iface.Read(resp7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition28.ApplyFunction(tla.MakeTLAString("body")), ACK_MSG(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
				}
				var condition29 tla.TLAValue
				condition29, err = iface.Read(resp7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition29.ApplyFunction(tla.MakeTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).srcTyp) = (PRIMARY_SRC)", distsys.ErrAssertionFailed)
				}
				var condition30 tla.TLAValue
				condition30, err = iface.Read(resp7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition30.ApplyFunction(tla.MakeTLAString("typ")), PUT_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
				}
				var condition31 tla.TLAValue
				condition31, err = iface.Read(resp7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition31.ApplyFunction(tla.MakeTLAString("id")), tla.MakeTLANumber(1)).AsBool() {
					return fmt.Errorf("%w: ((resp).id) = (1)", distsys.ErrAssertionFailed)
				}
				var toPrint tla.TLAValue
				toPrint, err = iface.Read(resp7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				tla.MakeTLATuple(tla.MakeTLAString("PUT RESP: "), toPrint).PCalPrint()
				return iface.Goto("AClient.sndGetReq")
			} else {
				return iface.Goto("AClient.sndPutReq")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndGetReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx19 := iface.RequireArchetypeResource("AClient.idx")
			err = iface.Write(idx19, []tla.TLAValue{}, tla.MakeTLANumber(1))
			if err != nil {
				return err
			}
			return iface.Goto("AClient.sndGetReqLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndGetReqLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx20 := iface.RequireArchetypeResource("AClient.idx")
			var condition32 tla.TLAValue
			condition32, err = iface.Read(idx20, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition32, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
				return iface.Goto("AClient.sndGetMsg")
			} else {
				return iface.Goto("AClient.rcvGetResp")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndGetMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd4, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			idx21 := iface.RequireArchetypeResource("AClient.idx")
			body1 := iface.RequireArchetypeResource("AClient.body")
			req3 := iface.RequireArchetypeResource("AClient.req")
			net7, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var condition33 tla.TLAValue
			condition33, err = iface.Read(idx21, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition34 tla.TLAValue
			condition34, err = iface.Read(fd4, []tla.TLAValue{condition33})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition34, tla.TLA_TRUE).AsBool() {
				err = iface.Write(body1, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("key"), KEY1(iface)},
					{tla.MakeTLAString("value"), TEMP_VAL(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead28 tla.TLAValue
				exprRead28, err = iface.Read(idx21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead29 tla.TLAValue
				exprRead29, err = iface.Read(body1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req3, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("from"), iface.Self()},
					{tla.MakeTLAString("to"), exprRead28},
					{tla.MakeTLAString("body"), exprRead29},
					{tla.MakeTLAString("srcTyp"), CLIENT_SRC(iface)},
					{tla.MakeTLAString("typ"), GET_REQ(iface)},
					{tla.MakeTLAString("id"), tla.MakeTLANumber(2)},
				}))
				if err != nil {
					return err
				}
				var exprRead30 tla.TLAValue
				exprRead30, err = iface.Read(req3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead8 tla.TLAValue
				indexRead8, err = iface.Read(req3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead9 tla.TLAValue
				indexRead9, err = iface.Read(req3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net7, []tla.TLAValue{tla.MakeTLATuple(indexRead8.ApplyFunction(tla.MakeTLAString("to")), indexRead9.ApplyFunction(tla.MakeTLAString("typ")))}, exprRead30)
				if err != nil {
					return err
				}
				return iface.Goto("AClient.rcvGetResp")
			} else {
				return iface.Goto("AClient.sndGetReqLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.rcvGetResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd5, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			idx23 := iface.RequireArchetypeResource("AClient.idx")
			resp14 := iface.RequireArchetypeResource("AClient.resp")
			net8, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var condition35 tla.TLAValue
			condition35, err = iface.Read(idx23, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition36 tla.TLAValue
			condition36, err = iface.Read(fd5, []tla.TLAValue{condition35})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition36, tla.TLA_TRUE).AsBool() {
				var exprRead31 tla.TLAValue
				exprRead31, err = iface.Read(net8, []tla.TLAValue{tla.MakeTLATuple(iface.Self(), GET_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp14, []tla.TLAValue{}, exprRead31)
				if err != nil {
					return err
				}
				var condition37 tla.TLAValue
				condition37, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition37.ApplyFunction(tla.MakeTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition38 tla.TLAValue
				condition38, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition38.ApplyFunction(tla.MakeTLAString("body")), VALUE1(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).body) = (VALUE1)", distsys.ErrAssertionFailed)
				}
				var condition39 tla.TLAValue
				condition39, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition39.ApplyFunction(tla.MakeTLAString("typ")), GET_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).typ) = (GET_RESP)", distsys.ErrAssertionFailed)
				}
				var condition40 tla.TLAValue
				condition40, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition40.ApplyFunction(tla.MakeTLAString("id")), tla.MakeTLANumber(2)).AsBool() {
					return fmt.Errorf("%w: ((resp).id) = (2)", distsys.ErrAssertionFailed)
				}
				var toPrint0 tla.TLAValue
				toPrint0, err = iface.Read(resp14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				tla.MakeTLATuple(tla.MakeTLAString("GET RESP: "), toPrint0).PCalPrint()
				return iface.Goto("AClient.Done")
			} else {
				return iface.Goto("AClient.sndGetReq")
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
	RequiredRefParams: []string{"AReplica.net", "AReplica.fs", "AReplica.fd"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AReplica.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.respBody", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.respTyp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.idx", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.repMsg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.rep", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.resp", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.sndPutReq",
	RequiredRefParams: []string{"AClient.net", "AClient.fd"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.idx", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.body", tla.TLAValue{})
	},
}
