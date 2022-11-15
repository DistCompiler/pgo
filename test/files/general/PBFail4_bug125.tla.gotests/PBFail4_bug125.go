package pbfail

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func NUM_NODES(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
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
func ACK_MSG(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("ack-body")
}
func KEY1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("KEY1")
}
func VALUE1(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("VALUE1")
}
func TEMP_VAL(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("TEMP")
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.ModuleTRUE.AsBool() {
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
				var exprRead tla.Value
				exprRead, err = iface.Read(net, []tla.Value{tla.MakeTuple(iface.Self(), GET_REQ(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, nil, exprRead)
				if err != nil {
					return err
				}
				// no statements
			case 1:
				var exprRead0 tla.Value
				exprRead0, err = iface.Read(net, []tla.Value{tla.MakeTuple(iface.Self(), PUT_REQ(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(msg, nil, exprRead0)
				if err != nil {
					return err
				}
				// no statements
			default:
				panic("current branch of either matches no code paths!")
			}
			var condition tla.Value
			condition, err = iface.Read(msg, nil)
			if err != nil {
				return err
			}
			if !tla.ModuleEqualsSymbol(condition.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() {
				return fmt.Errorf("%w: ((msg).to) = (self)", distsys.ErrAssertionFailed)
			}
			var condition0 tla.Value
			condition0, err = iface.Read(msg, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition0.ApplyFunction(tla.MakeString("srcTyp")), CLIENT_SRC(iface)).AsBool() {
				return iface.Goto("AReplica.handlePrimary")
			} else {
				var condition1 tla.Value
				condition1, err = iface.Read(msg, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition1.ApplyFunction(tla.MakeString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
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
			var condition2 tla.Value
			condition2, err = iface.Read(msg4, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition2.ApplyFunction(tla.MakeString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead1 tla.Value
				exprRead1, err = iface.Read(msg4, nil)
				if err != nil {
					return err
				}
				var exprRead2 tla.Value
				exprRead2, err = iface.Read(fs, []tla.Value{tla.MakeTuple(iface.Self(), exprRead1.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key")))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody, nil, exprRead2)
				if err != nil {
					return err
				}
				err = iface.Write(respTyp, nil, GET_RESP(iface))
				if err != nil {
					return err
				}
				// no statements
			} else {
				var condition3 tla.Value
				condition3, err = iface.Read(msg4, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition3.ApplyFunction(tla.MakeString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead3 tla.Value
					exprRead3, err = iface.Read(msg4, nil)
					if err != nil {
						return err
					}
					var indexRead tla.Value
					indexRead, err = iface.Read(msg4, nil)
					if err != nil {
						return err
					}
					err = iface.Write(fs, []tla.Value{tla.MakeTuple(iface.Self(), indexRead.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key")))}, exprRead3.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody, nil, ACK_MSG(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp, nil, PUT_RESP(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				// no statements
			}
			var exprRead4 tla.Value
			exprRead4, err = iface.Read(msg4, nil)
			if err != nil {
				return err
			}
			var exprRead5 tla.Value
			exprRead5, err = iface.Read(respBody, nil)
			if err != nil {
				return err
			}
			var exprRead6 tla.Value
			exprRead6, err = iface.Read(respTyp, nil)
			if err != nil {
				return err
			}
			var exprRead7 tla.Value
			exprRead7, err = iface.Read(msg4, nil)
			if err != nil {
				return err
			}
			err = iface.Write(resp, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("to"), exprRead4.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), exprRead5},
				{tla.MakeString("srcTyp"), BACKUP_SRC(iface)},
				{tla.MakeString("typ"), exprRead6},
				{tla.MakeString("id"), exprRead7.ApplyFunction(tla.MakeString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead8 tla.Value
			exprRead8, err = iface.Read(resp, nil)
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
			err = iface.Write(net1, []tla.Value{tla.MakeTuple(indexRead0.ApplyFunction(tla.MakeString("to")), indexRead1.ApplyFunction(tla.MakeString("typ")))}, exprRead8)
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
			var condition4 tla.Value
			condition4, err = iface.Read(msg11, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition4.ApplyFunction(tla.MakeString("typ")), GET_REQ(iface)).AsBool() {
				var exprRead9 tla.Value
				exprRead9, err = iface.Read(msg11, nil)
				if err != nil {
					return err
				}
				var exprRead10 tla.Value
				exprRead10, err = iface.Read(fs1, []tla.Value{tla.MakeTuple(iface.Self(), exprRead9.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key")))})
				if err != nil {
					return err
				}
				err = iface.Write(respBody2, nil, exprRead10)
				if err != nil {
					return err
				}
				err = iface.Write(respTyp2, nil, GET_RESP(iface))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.sndResp")
			} else {
				var condition5 tla.Value
				condition5, err = iface.Read(msg11, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition5.ApplyFunction(tla.MakeString("typ")), PUT_REQ(iface)).AsBool() {
					var exprRead11 tla.Value
					exprRead11, err = iface.Read(msg11, nil)
					if err != nil {
						return err
					}
					var indexRead2 tla.Value
					indexRead2, err = iface.Read(msg11, nil)
					if err != nil {
						return err
					}
					err = iface.Write(fs1, []tla.Value{tla.MakeTuple(iface.Self(), indexRead2.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("key")))}, exprRead11.ApplyFunction(tla.MakeString("body")).ApplyFunction(tla.MakeString("value")))
					if err != nil {
						return err
					}
					err = iface.Write(respBody2, nil, ACK_MSG(iface))
					if err != nil {
						return err
					}
					err = iface.Write(respTyp2, nil, PUT_RESP(iface))
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
			err = iface.Write(idx, nil, tla.MakeNumber(1))
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
			var condition6 tla.Value
			condition6, err = iface.Read(idx0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition6, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition7 tla.Value
			condition7, err = iface.Read(idx1, nil)
			if err != nil {
				return err
			}
			var condition8 tla.Value
			condition8, err = iface.Read(fd, []tla.Value{condition7})
			if err != nil {
				return err
			}
			var condition9 tla.Value
			condition9, err = iface.Read(idx1, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleEqualsSymbol(condition8, tla.ModuleTRUE).AsBool() && tla.ModuleNotEqualsSymbol(condition9, iface.Self()).AsBool()).AsBool() {
				var exprRead12 tla.Value
				exprRead12, err = iface.Read(idx1, nil)
				if err != nil {
					return err
				}
				var exprRead13 tla.Value
				exprRead13, err = iface.Read(msg16, nil)
				if err != nil {
					return err
				}
				var exprRead14 tla.Value
				exprRead14, err = iface.Read(msg16, nil)
				if err != nil {
					return err
				}
				err = iface.Write(repMsg, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("from"), iface.Self()},
					{tla.MakeString("to"), exprRead12},
					{tla.MakeString("body"), exprRead13.ApplyFunction(tla.MakeString("body"))},
					{tla.MakeString("srcTyp"), PRIMARY_SRC(iface)},
					{tla.MakeString("typ"), PUT_REQ(iface)},
					{tla.MakeString("id"), exprRead14.ApplyFunction(tla.MakeString("id"))},
				}))
				if err != nil {
					return err
				}
				var exprRead15 tla.Value
				exprRead15, err = iface.Read(repMsg, nil)
				if err != nil {
					return err
				}
				var indexRead3 tla.Value
				indexRead3, err = iface.Read(idx1, nil)
				if err != nil {
					return err
				}
				err = iface.Write(net2, []tla.Value{tla.MakeTuple(indexRead3, PUT_REQ(iface))}, exprRead15)
				if err != nil {
					return err
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead16 tla.Value
			exprRead16, err = iface.Read(idx1, nil)
			if err != nil {
				return err
			}
			err = iface.Write(idx1, nil, tla.ModulePlusSymbol(exprRead16, tla.MakeNumber(1)))
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
			err = iface.Write(idx7, nil, tla.MakeNumber(1))
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
			var condition10 tla.Value
			condition10, err = iface.Read(idx8, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition10, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition11 tla.Value
			condition11, err = iface.Read(idx9, nil)
			if err != nil {
				return err
			}
			var condition12 tla.Value
			condition12, err = iface.Read(fd0, []tla.Value{condition11})
			if err != nil {
				return err
			}
			var condition13 tla.Value
			condition13, err = iface.Read(idx9, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleEqualsSymbol(condition12, tla.ModuleTRUE).AsBool() && tla.ModuleNotEqualsSymbol(condition13, iface.Self()).AsBool()).AsBool() {
				var exprRead17 tla.Value
				exprRead17, err = iface.Read(net3, []tla.Value{tla.MakeTuple(iface.Self(), PUT_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(rep, nil, exprRead17)
				if err != nil {
					return err
				}
				var condition14 tla.Value
				condition14, err = iface.Read(rep, nil)
				if err != nil {
					return err
				}
				var condition15 tla.Value
				condition15, err = iface.Read(idx9, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition14.ApplyFunction(tla.MakeString("from")), condition15).AsBool() {
					return fmt.Errorf("%w: ((rep).from) = (idx)", distsys.ErrAssertionFailed)
				}
				var condition16 tla.Value
				condition16, err = iface.Read(rep, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition16.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((rep).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition17 tla.Value
				condition17, err = iface.Read(rep, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition17.ApplyFunction(tla.MakeString("body")), ACK_MSG(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
				}
				var condition18 tla.Value
				condition18, err = iface.Read(rep, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition18.ApplyFunction(tla.MakeString("srcTyp")), BACKUP_SRC(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).srcTyp) = (BACKUP_SRC)", distsys.ErrAssertionFailed)
				}
				var condition19 tla.Value
				condition19, err = iface.Read(rep, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition19.ApplyFunction(tla.MakeString("typ")), PUT_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((rep).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
				}
				var condition20 tla.Value
				condition20, err = iface.Read(rep, nil)
				if err != nil {
					return err
				}
				var condition21 tla.Value
				condition21, err = iface.Read(msg18, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition20.ApplyFunction(tla.MakeString("id")), condition21.ApplyFunction(tla.MakeString("id"))).AsBool() {
					return fmt.Errorf("%w: ((rep).id) = ((msg).id)", distsys.ErrAssertionFailed)
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead18 tla.Value
			exprRead18, err = iface.Read(idx9, nil)
			if err != nil {
				return err
			}
			err = iface.Write(idx9, nil, tla.ModulePlusSymbol(exprRead18, tla.MakeNumber(1)))
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
			var exprRead19 tla.Value
			exprRead19, err = iface.Read(msg19, nil)
			if err != nil {
				return err
			}
			var exprRead20 tla.Value
			exprRead20, err = iface.Read(respBody4, nil)
			if err != nil {
				return err
			}
			var exprRead21 tla.Value
			exprRead21, err = iface.Read(respTyp4, nil)
			if err != nil {
				return err
			}
			var exprRead22 tla.Value
			exprRead22, err = iface.Read(msg19, nil)
			if err != nil {
				return err
			}
			err = iface.Write(resp3, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("to"), exprRead19.ApplyFunction(tla.MakeString("from"))},
				{tla.MakeString("body"), exprRead20},
				{tla.MakeString("srcTyp"), PRIMARY_SRC(iface)},
				{tla.MakeString("typ"), exprRead21},
				{tla.MakeString("id"), exprRead22.ApplyFunction(tla.MakeString("id"))},
			}))
			if err != nil {
				return err
			}
			var exprRead23 tla.Value
			exprRead23, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			var indexRead4 tla.Value
			indexRead4, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			var indexRead5 tla.Value
			indexRead5, err = iface.Read(resp3, nil)
			if err != nil {
				return err
			}
			err = iface.Write(net4, []tla.Value{tla.MakeTuple(indexRead4.ApplyFunction(tla.MakeString("to")), indexRead5.ApplyFunction(tla.MakeString("typ")))}, exprRead23)
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
			err = iface.Write(fd1, []tla.Value{iface.Self()}, tla.ModuleFALSE)
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
			err = iface.Write(idx14, nil, tla.MakeNumber(1))
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
			var condition22 tla.Value
			condition22, err = iface.Read(idx15, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition22, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition23 tla.Value
			condition23, err = iface.Read(idx16, nil)
			if err != nil {
				return err
			}
			var condition24 tla.Value
			condition24, err = iface.Read(fd2, []tla.Value{condition23})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition24, tla.ModuleTRUE).AsBool() {
				err = iface.Write(body, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("key"), KEY1(iface)},
					{tla.MakeString("value"), VALUE1(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead24 tla.Value
				exprRead24, err = iface.Read(idx16, nil)
				if err != nil {
					return err
				}
				var exprRead25 tla.Value
				exprRead25, err = iface.Read(body, nil)
				if err != nil {
					return err
				}
				err = iface.Write(req, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("from"), iface.Self()},
					{tla.MakeString("to"), exprRead24},
					{tla.MakeString("body"), exprRead25},
					{tla.MakeString("srcTyp"), CLIENT_SRC(iface)},
					{tla.MakeString("typ"), PUT_REQ(iface)},
					{tla.MakeString("id"), tla.MakeNumber(1)},
				}))
				if err != nil {
					return err
				}
				var exprRead26 tla.Value
				exprRead26, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				var indexRead6 tla.Value
				indexRead6, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				var indexRead7 tla.Value
				indexRead7, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				err = iface.Write(net5, []tla.Value{tla.MakeTuple(indexRead6.ApplyFunction(tla.MakeString("to")), indexRead7.ApplyFunction(tla.MakeString("typ")))}, exprRead26)
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
			var condition25 tla.Value
			condition25, err = iface.Read(idx18, nil)
			if err != nil {
				return err
			}
			var condition26 tla.Value
			condition26, err = iface.Read(fd3, []tla.Value{condition25})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition26, tla.ModuleTRUE).AsBool() {
				var exprRead27 tla.Value
				exprRead27, err = iface.Read(net6, []tla.Value{tla.MakeTuple(iface.Self(), PUT_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp7, nil, exprRead27)
				if err != nil {
					return err
				}
				var condition27 tla.Value
				condition27, err = iface.Read(resp7, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition27.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition28 tla.Value
				condition28, err = iface.Read(resp7, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition28.ApplyFunction(tla.MakeString("body")), ACK_MSG(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
				}
				var condition29 tla.Value
				condition29, err = iface.Read(resp7, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition29.ApplyFunction(tla.MakeString("srcTyp")), PRIMARY_SRC(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).srcTyp) = (PRIMARY_SRC)", distsys.ErrAssertionFailed)
				}
				var condition30 tla.Value
				condition30, err = iface.Read(resp7, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition30.ApplyFunction(tla.MakeString("typ")), PUT_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
				}
				var condition31 tla.Value
				condition31, err = iface.Read(resp7, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition31.ApplyFunction(tla.MakeString("id")), tla.MakeNumber(1)).AsBool() {
					return fmt.Errorf("%w: ((resp).id) = (1)", distsys.ErrAssertionFailed)
				}
				var toPrint tla.Value
				toPrint, err = iface.Read(resp7, nil)
				if err != nil {
					return err
				}
				tla.MakeTuple(tla.MakeString("PUT RESP: "), toPrint).PCalPrint()
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
			err = iface.Write(idx19, nil, tla.MakeNumber(1))
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
			var condition32 tla.Value
			condition32, err = iface.Read(idx20, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition32, iface.GetConstant("NUM_REPLICAS")()).AsBool() {
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
			var condition33 tla.Value
			condition33, err = iface.Read(idx21, nil)
			if err != nil {
				return err
			}
			var condition34 tla.Value
			condition34, err = iface.Read(fd4, []tla.Value{condition33})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition34, tla.ModuleTRUE).AsBool() {
				err = iface.Write(body1, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("key"), KEY1(iface)},
					{tla.MakeString("value"), TEMP_VAL(iface)},
				}))
				if err != nil {
					return err
				}
				var exprRead28 tla.Value
				exprRead28, err = iface.Read(idx21, nil)
				if err != nil {
					return err
				}
				var exprRead29 tla.Value
				exprRead29, err = iface.Read(body1, nil)
				if err != nil {
					return err
				}
				err = iface.Write(req3, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("from"), iface.Self()},
					{tla.MakeString("to"), exprRead28},
					{tla.MakeString("body"), exprRead29},
					{tla.MakeString("srcTyp"), CLIENT_SRC(iface)},
					{tla.MakeString("typ"), GET_REQ(iface)},
					{tla.MakeString("id"), tla.MakeNumber(2)},
				}))
				if err != nil {
					return err
				}
				var exprRead30 tla.Value
				exprRead30, err = iface.Read(req3, nil)
				if err != nil {
					return err
				}
				var indexRead8 tla.Value
				indexRead8, err = iface.Read(req3, nil)
				if err != nil {
					return err
				}
				var indexRead9 tla.Value
				indexRead9, err = iface.Read(req3, nil)
				if err != nil {
					return err
				}
				err = iface.Write(net7, []tla.Value{tla.MakeTuple(indexRead8.ApplyFunction(tla.MakeString("to")), indexRead9.ApplyFunction(tla.MakeString("typ")))}, exprRead30)
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
			var condition35 tla.Value
			condition35, err = iface.Read(idx23, nil)
			if err != nil {
				return err
			}
			var condition36 tla.Value
			condition36, err = iface.Read(fd5, []tla.Value{condition35})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition36, tla.ModuleTRUE).AsBool() {
				var exprRead31 tla.Value
				exprRead31, err = iface.Read(net8, []tla.Value{tla.MakeTuple(iface.Self(), GET_RESP(iface))})
				if err != nil {
					return err
				}
				err = iface.Write(resp14, nil, exprRead31)
				if err != nil {
					return err
				}
				var condition37 tla.Value
				condition37, err = iface.Read(resp14, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition37.ApplyFunction(tla.MakeString("to")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
				}
				var condition38 tla.Value
				condition38, err = iface.Read(resp14, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition38.ApplyFunction(tla.MakeString("body")), VALUE1(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).body) = (VALUE1)", distsys.ErrAssertionFailed)
				}
				var condition39 tla.Value
				condition39, err = iface.Read(resp14, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition39.ApplyFunction(tla.MakeString("typ")), GET_RESP(iface)).AsBool() {
					return fmt.Errorf("%w: ((resp).typ) = (GET_RESP)", distsys.ErrAssertionFailed)
				}
				var condition40 tla.Value
				condition40, err = iface.Read(resp14, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition40.ApplyFunction(tla.MakeString("id")), tla.MakeNumber(2)).AsBool() {
					return fmt.Errorf("%w: ((resp).id) = (2)", distsys.ErrAssertionFailed)
				}
				var toPrint0 tla.Value
				toPrint0, err = iface.Read(resp14, nil)
				if err != nil {
					return err
				}
				tla.MakeTuple(tla.MakeString("GET RESP: "), toPrint0).PCalPrint()
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
		iface.EnsureArchetypeResourceLocal("AReplica.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.respBody", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.respTyp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.idx", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.repMsg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.rep", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.resp", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.idx", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.body", tla.Value{})
	},
}
