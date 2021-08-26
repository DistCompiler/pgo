package pbfail

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

func NUM_NODES(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
}
func CLIENT_SRC(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}
func PRIMARY_SRC(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}
func BACKUP_SRC(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}
func GET_REQ(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}
func GET_RESP(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}
func PUT_REQ(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}
func PUT_RESP(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(4)
}
func ACK_MSG(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLAString("ack-body")
}
func KEY1(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLAString("KEY1")
}
func VALUE1(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLAString("VALUE1")
}
func TEMP_VAL(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLAString("TEMP")
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if distsys.TLA_TRUE.AsBool() {
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
			switch iface.Fairness("AReplica.rcvMsg.0", 2) {
			case 0:
				var exprRead distsys.TLAValue
				exprRead, err = iface.Read(net, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), GET_REQ(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, []distsys.TLAValue{}, exprRead)
				if err != nil {
					return err
				}
				// no statements
			case 1:
				var exprRead0 distsys.TLAValue
				exprRead0, err = iface.Read(net, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), PUT_REQ(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, []distsys.TLAValue{}, exprRead0)
				if err != nil {
					return err
				}
				// no statements
			default:
				panic("current branch of either matches no code paths!")
			}
			var condition distsys.TLAValue
			condition, err = iface.Read(msg, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if !distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("to")), iface.Self()).AsBool() {
				return fmt.Errorf("%w: ((msg).to) = (self)", distsys.ErrAssertionFailed)
			}
			var condition0 distsys.TLAValue
			condition0, err = iface.Read(msg, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition0.ApplyFunction(distsys.NewTLAString("srcTyp")), CLIENT_SRC(iface)).AsBool() {
				return iface.Goto("AReplica.handlePrimary")
			} else {
				var condition1 distsys.TLAValue
				condition1, err = iface.Read(msg, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if distsys.TLA_EqualsSymbol(condition1.ApplyFunction(distsys.NewTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
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
			var condition2 distsys.TLAValue
			condition2, err = iface.Read(msg4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition2.ApplyFunction(distsys.NewTLAString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead1 distsys.TLAValue
				exprRead1, err = iface.Read(msg4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead2 distsys.TLAValue
				exprRead2, err = iface.Read(fs, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), exprRead1.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody, []distsys.TLAValue{}, exprRead2)
				if err != nil {
					return err
				}
				err = iface.Write(respTyp, []distsys.TLAValue{}, GET_RESP(iface))
				if err != nil {
					return err
				}
				// no statements
			} else {
				var condition3 distsys.TLAValue
				condition3, err = iface.Read(msg4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if distsys.TLA_EqualsSymbol(condition3.ApplyFunction(distsys.NewTLAString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead3 distsys.TLAValue
					exprRead3, err = iface.Read(msg4, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead distsys.TLAValue
					indexRead, err = iface.Read(msg4, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(fs, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), indexRead.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))}, exprRead3.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("value")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody, []distsys.TLAValue{}, ACK_MSG(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp, []distsys.TLAValue{}, PUT_RESP(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				// no statements
			}
			var exprRead4 distsys.TLAValue
			exprRead4, err = iface.Read(msg4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead5 distsys.TLAValue
			exprRead5, err = iface.Read(respBody, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead6 distsys.TLAValue
			exprRead6, err = iface.Read(respTyp, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead7 distsys.TLAValue
			exprRead7, err = iface.Read(msg4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), iface.Self()},
				{distsys.NewTLAString("to"), exprRead4.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead5},
				{distsys.NewTLAString("srcTyp"), BACKUP_SRC(iface)},
				{distsys.NewTLAString("typ"), exprRead6},
				{distsys.NewTLAString("id"), exprRead7.ApplyFunction(distsys.NewTLAString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead8 distsys.TLAValue
			exprRead8, err = iface.Read(resp, []distsys.TLAValue{})
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
			err = iface.Write(net1, []distsys.TLAValue{distsys.NewTLATuple(indexRead0.ApplyFunction(distsys.NewTLAString("to")), indexRead1.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead8)
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
			var condition4 distsys.TLAValue
			condition4, err = iface.Read(msg11, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition4.ApplyFunction(distsys.NewTLAString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead9 distsys.TLAValue
				exprRead9, err = iface.Read(msg11, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead10 distsys.TLAValue
				exprRead10, err = iface.Read(fs1, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), exprRead9.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody2, []distsys.TLAValue{}, exprRead10)
				if err != nil {
					return err
				}
				err = iface.Write(respTyp2, []distsys.TLAValue{}, GET_RESP(iface))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.sndResp")
			} else {
				var condition5 distsys.TLAValue
				condition5, err = iface.Read(msg11, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if distsys.TLA_EqualsSymbol(condition5.ApplyFunction(distsys.NewTLAString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead11 distsys.TLAValue
					exprRead11, err = iface.Read(msg11, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead2 distsys.TLAValue
					indexRead2, err = iface.Read(msg11, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(fs1, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), indexRead2.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))}, exprRead11.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("value")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody2, []distsys.TLAValue{}, ACK_MSG(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp2, []distsys.TLAValue{}, PUT_RESP(iface))
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
			err = iface.Write(idx, []distsys.TLAValue{}, distsys.NewTLANumber(1))
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
			var condition6 distsys.TLAValue
			condition6, err = iface.Read(idx0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition6, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition7 distsys.TLAValue
			condition7, err = iface.Read(idx1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition8 distsys.TLAValue
			condition8, err = iface.Read(fd, []distsys.TLAValue{condition7})
			if err != nil {
				return err
			}
			var condition9 distsys.TLAValue
			condition9, err = iface.Read(idx1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition8, distsys.TLA_TRUE), distsys.TLA_NotEqualsSymbol(condition9, iface.Self())).AsBool() {
				var exprRead12 distsys.TLAValue
				exprRead12, err = iface.Read(idx1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead13 distsys.TLAValue
				exprRead13, err = iface.Read(msg16, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead14 distsys.TLAValue
				exprRead14, err = iface.Read(msg16, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(repMsg, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), iface.Self()},
					{distsys.NewTLAString("to"), exprRead12},
					{distsys.NewTLAString("body"), exprRead13.ApplyFunction(distsys.NewTLAString("body"))},
					{distsys.NewTLAString("srcTyp"), PRIMARY_SRC(iface)},
					{distsys.NewTLAString("typ"), PUT_REQ(iface)},
					{distsys.NewTLAString("id"), exprRead14.ApplyFunction(distsys.NewTLAString("id"))},
				}))
				if err != nil {
					return err
				}
				var exprRead15 distsys.TLAValue
				exprRead15, err = iface.Read(repMsg, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead3 distsys.TLAValue
				indexRead3, err = iface.Read(idx1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net2, []distsys.TLAValue{distsys.NewTLATuple(indexRead3, PUT_REQ(iface))}, exprRead15)
				if err != nil {
					return err
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead16 distsys.TLAValue
			exprRead16, err = iface.Read(idx1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(idx1, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead16, distsys.NewTLANumber(1)))
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
			err = iface.Write(idx7, []distsys.TLAValue{}, distsys.NewTLANumber(1))
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
			var condition10 distsys.TLAValue
			condition10, err = iface.Read(idx8, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition10, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition11 distsys.TLAValue
			condition11, err = iface.Read(idx9, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition12 distsys.TLAValue
			condition12, err = iface.Read(fd0, []distsys.TLAValue{condition11})
			if err != nil {
				return err
			}
			var condition13 distsys.TLAValue
			condition13, err = iface.Read(idx9, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition12, distsys.TLA_TRUE), distsys.TLA_NotEqualsSymbol(condition13, iface.Self())).AsBool() {
				var exprRead17 distsys.TLAValue
				exprRead17, err = iface.Read(net3, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), PUT_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(rep, []distsys.TLAValue{}, exprRead17)
				if err != nil {
					return err
				}
				var condition14 distsys.TLAValue
				condition14, err = iface.Read(rep, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition15 distsys.TLAValue
				condition15, err = iface.Read(idx9, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition14.ApplyFunction(distsys.NewTLAString("from")), condition15).AsBool() {
					return fmt.Errorf("%w: ((rep).from) = (idx)", distsys.ErrAssertionFailed)
				}
				var condition16 distsys.TLAValue
				condition16, err = iface.Read(rep, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition16.ApplyFunction(distsys.NewTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((rep).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition17 distsys.TLAValue
				condition17, err = iface.Read(rep, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition17.ApplyFunction(distsys.NewTLAString("body")), ACK_MSG(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
				}
				var condition18 distsys.TLAValue
				condition18, err = iface.Read(rep, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition18.ApplyFunction(distsys.NewTLAString("srcTyp")), BACKUP_SRC(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).srcTyp) = (BACKUP_SRC)", distsys.ErrAssertionFailed)
				}
				var condition19 distsys.TLAValue
				condition19, err = iface.Read(rep, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition19.ApplyFunction(distsys.NewTLAString("typ")), PUT_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
				}
				var condition20 distsys.TLAValue
				condition20, err = iface.Read(rep, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition21 distsys.TLAValue
				condition21, err = iface.Read(msg18, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition20.ApplyFunction(distsys.NewTLAString("id")), condition21.ApplyFunction(distsys.NewTLAString("id"))).AsBool() {
					return fmt.Errorf("%w: ((rep).id) = ((msg).id)", distsys.ErrAssertionFailed)
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead18 distsys.TLAValue
			exprRead18, err = iface.Read(idx9, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(idx9, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead18, distsys.NewTLANumber(1)))
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
			var exprRead19 distsys.TLAValue
			exprRead19, err = iface.Read(msg19, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead20 distsys.TLAValue
			exprRead20, err = iface.Read(respBody4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead21 distsys.TLAValue
			exprRead21, err = iface.Read(respTyp4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var exprRead22 distsys.TLAValue
			exprRead22, err = iface.Read(msg19, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(resp3, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), iface.Self()},
				{distsys.NewTLAString("to"), exprRead19.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead20},
				{distsys.NewTLAString("srcTyp"), PRIMARY_SRC(iface)},
				{distsys.NewTLAString("typ"), exprRead21},
				{distsys.NewTLAString("id"), exprRead22.ApplyFunction(distsys.NewTLAString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead23 distsys.TLAValue
			exprRead23, err = iface.Read(resp3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead4 distsys.TLAValue
			indexRead4, err = iface.Read(resp3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead5 distsys.TLAValue
			indexRead5, err = iface.Read(resp3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net4, []distsys.TLAValue{distsys.NewTLATuple(indexRead4.ApplyFunction(distsys.NewTLAString("to")), indexRead5.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead23)
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
			err = iface.Write(fd1, []distsys.TLAValue{iface.Self()}, distsys.TLA_FALSE)
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
			err = iface.Write(idx14, []distsys.TLAValue{}, distsys.NewTLANumber(1))
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
			var condition22 distsys.TLAValue
			condition22, err = iface.Read(idx15, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition22, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition23 distsys.TLAValue
			condition23, err = iface.Read(idx16, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition24 distsys.TLAValue
			condition24, err = iface.Read(fd2, []distsys.TLAValue{condition23})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition24, distsys.TLA_TRUE).AsBool() {
				err = iface.Write(body, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("key"), KEY1(iface)},
					{distsys.NewTLAString("value"), VALUE1(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead24 distsys.TLAValue
				exprRead24, err = iface.Read(idx16, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead25 distsys.TLAValue
				exprRead25, err = iface.Read(body, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), iface.Self()},
					{distsys.NewTLAString("to"), exprRead24},
					{distsys.NewTLAString("body"), exprRead25},
					{distsys.NewTLAString("srcTyp"), CLIENT_SRC(iface)},
					{distsys.NewTLAString("typ"), PUT_REQ(iface)},
					{distsys.NewTLAString("id"), distsys.NewTLANumber(1)},
				}))
				if err != nil {
					return err
				}
				var exprRead26 distsys.TLAValue
				exprRead26, err = iface.Read(req, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead6 distsys.TLAValue
				indexRead6, err = iface.Read(req, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead7 distsys.TLAValue
				indexRead7, err = iface.Read(req, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net5, []distsys.TLAValue{distsys.NewTLATuple(indexRead6.ApplyFunction(distsys.NewTLAString("to")), indexRead7.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead26)
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
			var condition25 distsys.TLAValue
			condition25, err = iface.Read(idx18, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition26 distsys.TLAValue
			condition26, err = iface.Read(fd3, []distsys.TLAValue{condition25})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition26, distsys.TLA_TRUE).AsBool() {
				var exprRead27 distsys.TLAValue
				exprRead27, err = iface.Read(net6, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), PUT_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp7, []distsys.TLAValue{}, exprRead27)
				if err != nil {
					return err
				}
				var condition27 distsys.TLAValue
				condition27, err = iface.Read(resp7, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition27.ApplyFunction(distsys.NewTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition28 distsys.TLAValue
				condition28, err = iface.Read(resp7, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition28.ApplyFunction(distsys.NewTLAString("body")), ACK_MSG(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
				}
				var condition29 distsys.TLAValue
				condition29, err = iface.Read(resp7, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition29.ApplyFunction(distsys.NewTLAString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).srcTyp) = (PRIMARY_SRC)", distsys.ErrAssertionFailed)
				}
				var condition30 distsys.TLAValue
				condition30, err = iface.Read(resp7, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition30.ApplyFunction(distsys.NewTLAString("typ")), PUT_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
				}
				var condition31 distsys.TLAValue
				condition31, err = iface.Read(resp7, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition31.ApplyFunction(distsys.NewTLAString("id")), distsys.NewTLANumber(1)).AsBool() {
					return fmt.Errorf("%w: ((resp).id) = (1)", distsys.ErrAssertionFailed)
				}
				var toPrint distsys.TLAValue
				toPrint, err = iface.Read(resp7, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				distsys.NewTLATuple(distsys.NewTLAString("PUT RESP: "), toPrint).PCalPrint()
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
			err = iface.Write(idx19, []distsys.TLAValue{}, distsys.NewTLANumber(1))
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
			var condition32 distsys.TLAValue
			condition32, err = iface.Read(idx20, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition32, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition33 distsys.TLAValue
			condition33, err = iface.Read(idx21, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition34 distsys.TLAValue
			condition34, err = iface.Read(fd4, []distsys.TLAValue{condition33})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition34, distsys.TLA_TRUE).AsBool() {
				err = iface.Write(body1, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("key"), KEY1(iface)},
					{distsys.NewTLAString("value"), TEMP_VAL(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead28 distsys.TLAValue
				exprRead28, err = iface.Read(idx21, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead29 distsys.TLAValue
				exprRead29, err = iface.Read(body1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req3, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), iface.Self()},
					{distsys.NewTLAString("to"), exprRead28},
					{distsys.NewTLAString("body"), exprRead29},
					{distsys.NewTLAString("srcTyp"), CLIENT_SRC(iface)},
					{distsys.NewTLAString("typ"), GET_REQ(iface)},
					{distsys.NewTLAString("id"), distsys.NewTLANumber(2)},
				}))
				if err != nil {
					return err
				}
				var exprRead30 distsys.TLAValue
				exprRead30, err = iface.Read(req3, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead8 distsys.TLAValue
				indexRead8, err = iface.Read(req3, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead9 distsys.TLAValue
				indexRead9, err = iface.Read(req3, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net7, []distsys.TLAValue{distsys.NewTLATuple(indexRead8.ApplyFunction(distsys.NewTLAString("to")), indexRead9.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead30)
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
			var condition35 distsys.TLAValue
			condition35, err = iface.Read(idx23, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition36 distsys.TLAValue
			condition36, err = iface.Read(fd5, []distsys.TLAValue{condition35})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition36, distsys.TLA_TRUE).AsBool() {
				var exprRead31 distsys.TLAValue
				exprRead31, err = iface.Read(net8, []distsys.TLAValue{distsys.NewTLATuple(iface.Self(), GET_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp14, []distsys.TLAValue{}, exprRead31)
				if err != nil {
					return err
				}
				var condition37 distsys.TLAValue
				condition37, err = iface.Read(resp14, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition37.ApplyFunction(distsys.NewTLAString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition38 distsys.TLAValue
				condition38, err = iface.Read(resp14, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition38.ApplyFunction(distsys.NewTLAString("body")), VALUE1(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).body) = (VALUE1)", distsys.ErrAssertionFailed)
				}
				var condition39 distsys.TLAValue
				condition39, err = iface.Read(resp14, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition39.ApplyFunction(distsys.NewTLAString("typ")), GET_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).typ) = (GET_RESP)", distsys.ErrAssertionFailed)
				}
				var condition40 distsys.TLAValue
				condition40, err = iface.Read(resp14, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition40.ApplyFunction(distsys.NewTLAString("id")), distsys.NewTLANumber(2)).AsBool() {
					return fmt.Errorf("%w: ((resp).id) = (2)", distsys.ErrAssertionFailed)
				}
				var toPrint0 distsys.TLAValue
				toPrint0, err = iface.Read(resp14, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				distsys.NewTLATuple(distsys.NewTLAString("GET RESP: "), toPrint0).PCalPrint()
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
		iface.EnsureArchetypeResourceLocal("AReplica.msg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.respBody", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.respTyp", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.idx", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.repMsg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.rep", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.resp", distsys.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("AClient.req", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.idx", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.body", distsys.TLAValue{})
	},
}
