package pbfail

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	BUFFER_SIZE  distsys.TLAValue
	NUM_REPLICAS distsys.TLAValue
	NUM_CLIENTS  distsys.TLAValue
	EXPLORE_FAIL distsys.TLAValue
}

func NUM_NODES(constants Constants) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, constants.NUM_CLIENTS)
}

func CLIENT_SRC(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}

func PRIMARY_SRC(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}

func BACKUP_SRC(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}

func GET_REQ(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}

func GET_RESP(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}

func PUT_REQ(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}

func PUT_RESP(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(4)
}

func ACK_MSG(constants Constants) distsys.TLAValue {
	return distsys.NewTLAString("ack-body")
}

func KEY1(constants Constants) distsys.TLAValue {
	return distsys.NewTLAString("KEY1")
}

func VALUE1(constants Constants) distsys.TLAValue {
	return distsys.NewTLAString("VALUE1")
}

func TEMP_VAL(constants Constants) distsys.TLAValue {
	return distsys.NewTLAString("TEMP")
}

func AReplica(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net distsys.ArchetypeResourceHandle, fs distsys.ArchetypeResourceHandle, fd distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		InitLabelTag = iota
		replicaLoopLabelTag
		rcvMsgLabelTag
		handleBackupLabelTag
		handlePrimaryLabelTag
		sndReplicaMsgLabelTag
		sndMsgLoopLabelTag
		sndMsgLabelTag
		rcvReplicaMsgLabelTag
		rcvMsgLoopLabelTag
		rcvMsgFromReplicaLabelTag
		sndRespLabelTag
		failLabelLabelTag
		DoneLabelTag
	)
	programCounter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag)))
	msg := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg
	respBody := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = respBody
	respTyp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = respTyp
	idx := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = idx
	repMsg := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = repMsg
	rep := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = rep
	resp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = resp
	var fairnessCounter int = 0

	for {
		if err != nil {
			if err == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err = nil
			} else {
				return err
			}
		}
		var labelTag distsys.TLAValue
		labelTag, err = ctx.Read(programCounter, []distsys.TLAValue{})
		if err != nil {
			return err
		}
		switch labelTag.AsNumber() {
		case InitLabelTag:
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaLoopLabelTag))
			if err != nil {
				continue
			}
		case replicaLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(failLabelLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case rcvMsgLabelTag:
			fairnessCounterCurrent := fairnessCounter
			fairnessCounter = fairnessCounter + 1%2
			switch fairnessCounterCurrent {
			case 0:
				var exprRead22 distsys.TLAValue
				exprRead22, err = ctx.Read(net, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
					return GET_REQ(constants)
				}())})
				if err != nil {
					continue
				}
				err = ctx.Write(msg, []distsys.TLAValue{}, exprRead22)
				if err != nil {
					continue
				}
				// no statements
			case 1:
				var exprRead23 distsys.TLAValue
				exprRead23, err = ctx.Read(net, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
					return PUT_REQ(constants)
				}())})
				if err != nil {
					continue
				}
				err = ctx.Write(msg, []distsys.TLAValue{}, exprRead23)
				if err != nil {
					continue
				}
				// no statements
			default:
				panic("current branch of either matches no code paths!")
			}
			var condition distsys.TLAValue
			condition, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if !distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("to")), self).AsBool() {
				err = fmt.Errorf("%w: ((msg).to) = (self)", distsys.ErrAssertionFailed)
				continue
			}
			var condition0 distsys.TLAValue
			condition0, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition0.ApplyFunction(distsys.NewTLAString("srcTyp")), func() distsys.TLAValue {
				return CLIENT_SRC(constants)
			}()).AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(handlePrimaryLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				var condition1 distsys.TLAValue
				condition1, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if distsys.TLA_EqualsSymbol(condition1.ApplyFunction(distsys.NewTLAString("srcTyp")), func() distsys.TLAValue {
					return PRIMARY_SRC(constants)
				}()).AsBool() {
					err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(handleBackupLabelTag))
					if err != nil {
						continue
					}
					err = ctx.Commit()
					if err != nil {
						continue
					}
				} else {
					err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(handleBackupLabelTag))
					if err != nil {
						continue
					}
					err = ctx.Commit()
					if err != nil {
						continue
					}
				}
				// no statements
			}
			// no statements
		case handleBackupLabelTag:
			var condition2 distsys.TLAValue
			condition2, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition2.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
				return GET_REQ(constants)
			}()).AsBool() {
				var exprRead distsys.TLAValue
				exprRead, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead0 distsys.TLAValue
				exprRead0, err = ctx.Read(fs, []distsys.TLAValue{distsys.NewTLATuple(self, exprRead.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))})
				if err != nil {
					continue
				}
				err = ctx.Write(respBody, []distsys.TLAValue{}, exprRead0)
				if err != nil {
					continue
				}
				err = ctx.Write(respTyp, []distsys.TLAValue{}, func() distsys.TLAValue {
					return GET_RESP(constants)
				}())
				if err != nil {
					continue
				}
				// no statements
			} else {
				var condition3 distsys.TLAValue
				condition3, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if distsys.TLA_EqualsSymbol(condition3.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
					return PUT_REQ(constants)
				}()).AsBool() {
					var exprRead1 distsys.TLAValue
					exprRead1, err = ctx.Read(msg, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					var indexRead distsys.TLAValue
					indexRead, err = ctx.Read(msg, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					err = ctx.Write(fs, []distsys.TLAValue{distsys.NewTLATuple(self, indexRead.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))}, exprRead1.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("value")))
					if err != nil {
						continue
					}
					err = ctx.Write(respBody, []distsys.TLAValue{}, func() distsys.TLAValue {
						return ACK_MSG(constants)
					}())
					if err != nil {
						continue
					}
					err = ctx.Write(respTyp, []distsys.TLAValue{}, func() distsys.TLAValue {
						return PUT_RESP(constants)
					}())
					if err != nil {
						continue
					}
					// no statements
				} else {
					// no statements
				}
				// no statements
			}
			var exprRead2 distsys.TLAValue
			exprRead2, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead3 distsys.TLAValue
			exprRead3, err = ctx.Read(respBody, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead4 distsys.TLAValue
			exprRead4, err = ctx.Read(respTyp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead5 distsys.TLAValue
			exprRead5, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(resp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), self},
				{distsys.NewTLAString("to"), exprRead2.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead3},
				{distsys.NewTLAString("srcTyp"), func() distsys.TLAValue {
					return BACKUP_SRC(constants)
				}()},
				{distsys.NewTLAString("typ"), exprRead4},
				{distsys.NewTLAString("id"), exprRead5.ApplyFunction(distsys.NewTLAString("id"))},
			}))
			if err != nil {
				continue
			}
			var exprRead6 distsys.TLAValue
			exprRead6, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead1 distsys.TLAValue
			indexRead1, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(net, []distsys.TLAValue{distsys.NewTLATuple(indexRead0.ApplyFunction(distsys.NewTLAString("to")), indexRead1.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead6)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case handlePrimaryLabelTag:
			var condition4 distsys.TLAValue
			condition4, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition4.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
				return GET_REQ(constants)
			}()).AsBool() {
				var exprRead7 distsys.TLAValue
				exprRead7, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead8 distsys.TLAValue
				exprRead8, err = ctx.Read(fs, []distsys.TLAValue{distsys.NewTLATuple(self, exprRead7.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))})
				if err != nil {
					continue
				}
				err = ctx.Write(respBody, []distsys.TLAValue{}, exprRead8)
				if err != nil {
					continue
				}
				err = ctx.Write(respTyp, []distsys.TLAValue{}, func() distsys.TLAValue {
					return GET_RESP(constants)
				}())
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndRespLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				var condition5 distsys.TLAValue
				condition5, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if distsys.TLA_EqualsSymbol(condition5.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
					return PUT_REQ(constants)
				}()).AsBool() {
					var exprRead9 distsys.TLAValue
					exprRead9, err = ctx.Read(msg, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					var indexRead2 distsys.TLAValue
					indexRead2, err = ctx.Read(msg, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					err = ctx.Write(fs, []distsys.TLAValue{distsys.NewTLATuple(self, indexRead2.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("key")))}, exprRead9.ApplyFunction(distsys.NewTLAString("body")).ApplyFunction(distsys.NewTLAString("value")))
					if err != nil {
						continue
					}
					err = ctx.Write(respBody, []distsys.TLAValue{}, func() distsys.TLAValue {
						return ACK_MSG(constants)
					}())
					if err != nil {
						continue
					}
					err = ctx.Write(respTyp, []distsys.TLAValue{}, func() distsys.TLAValue {
						return PUT_RESP(constants)
					}())
					if err != nil {
						continue
					}
					err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndReplicaMsgLabelTag))
					if err != nil {
						continue
					}
					err = ctx.Commit()
					if err != nil {
						continue
					}
				} else {
					err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndReplicaMsgLabelTag))
					if err != nil {
						continue
					}
					err = ctx.Commit()
					if err != nil {
						continue
					}
				}
				// no statements
			}
			// no statements
		case sndReplicaMsgLabelTag:
			err = ctx.Write(idx, []distsys.TLAValue{}, distsys.NewTLANumber(1))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndMsgLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case sndMsgLoopLabelTag:
			var condition6 distsys.TLAValue
			condition6, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition6, constants.NUM_REPLICAS).AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndMsgLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvReplicaMsgLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case sndMsgLabelTag:
			var condition7 distsys.TLAValue
			condition7, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition8 distsys.TLAValue
			condition8, err = ctx.Read(fd, []distsys.TLAValue{condition7})
			if err != nil {
				continue
			}
			var condition9 distsys.TLAValue
			condition9, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition8, distsys.TLA_TRUE), distsys.TLA_NotEqualsSymbol(condition9, self)).AsBool() {
				var exprRead10 distsys.TLAValue
				exprRead10, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead11 distsys.TLAValue
				exprRead11, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead12 distsys.TLAValue
				exprRead12, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(repMsg, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), self},
					{distsys.NewTLAString("to"), exprRead10},
					{distsys.NewTLAString("body"), exprRead11.ApplyFunction(distsys.NewTLAString("body"))},
					{distsys.NewTLAString("srcTyp"), func() distsys.TLAValue {
						return PRIMARY_SRC(constants)
					}()},
					{distsys.NewTLAString("typ"), func() distsys.TLAValue {
						return PUT_REQ(constants)
					}()},
					{distsys.NewTLAString("id"), exprRead12.ApplyFunction(distsys.NewTLAString("id"))},
				}))
				if err != nil {
					continue
				}
				var exprRead13 distsys.TLAValue
				exprRead13, err = ctx.Read(repMsg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead3 distsys.TLAValue
				indexRead3, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(net, []distsys.TLAValue{distsys.NewTLATuple(indexRead3, func() distsys.TLAValue {
					return PUT_REQ(constants)
				}())}, exprRead13)
				if err != nil {
					continue
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead14 distsys.TLAValue
			exprRead14, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(idx, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead14, distsys.NewTLANumber(1)))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndMsgLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case rcvReplicaMsgLabelTag:
			err = ctx.Write(idx, []distsys.TLAValue{}, distsys.NewTLANumber(1))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case rcvMsgLoopLabelTag:
			var condition10 distsys.TLAValue
			condition10, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition10, constants.NUM_REPLICAS).AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgFromReplicaLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndRespLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case rcvMsgFromReplicaLabelTag:
			var condition11 distsys.TLAValue
			condition11, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition12 distsys.TLAValue
			condition12, err = ctx.Read(fd, []distsys.TLAValue{condition11})
			if err != nil {
				continue
			}
			var condition13 distsys.TLAValue
			condition13, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition12, distsys.TLA_TRUE), distsys.TLA_NotEqualsSymbol(condition13, self)).AsBool() {
				var exprRead15 distsys.TLAValue
				exprRead15, err = ctx.Read(net, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
					return PUT_RESP(constants)
				}())})
				if err != nil {
					continue
				}
				err = ctx.Write(rep, []distsys.TLAValue{}, exprRead15)
				if err != nil {
					continue
				}
				var condition14 distsys.TLAValue
				condition14, err = ctx.Read(rep, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition15 distsys.TLAValue
				condition15, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition14.ApplyFunction(distsys.NewTLAString("from")), condition15).AsBool() {
					err = fmt.Errorf("%w: ((rep).from) = (idx)", distsys.ErrAssertionFailed)
					continue
				}
				var condition16 distsys.TLAValue
				condition16, err = ctx.Read(rep, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition16.ApplyFunction(distsys.NewTLAString("to")), self).AsBool() {
					err = fmt.Errorf("%w: ((rep).to) = (self)", distsys.ErrAssertionFailed)
					continue
				}
				var condition17 distsys.TLAValue
				condition17, err = ctx.Read(rep, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition17.ApplyFunction(distsys.NewTLAString("body")), func() distsys.TLAValue {
					return ACK_MSG(constants)
				}()).AsBool() {
					err = fmt.Errorf("%w: ((rep).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
					continue
				}
				var condition18 distsys.TLAValue
				condition18, err = ctx.Read(rep, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition18.ApplyFunction(distsys.NewTLAString("srcTyp")), func() distsys.TLAValue {
					return BACKUP_SRC(constants)
				}()).AsBool() {
					err = fmt.Errorf("%w: ((rep).srcTyp) = (BACKUP_SRC)", distsys.ErrAssertionFailed)
					continue
				}
				var condition19 distsys.TLAValue
				condition19, err = ctx.Read(rep, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition19.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
					return PUT_RESP(constants)
				}()).AsBool() {
					err = fmt.Errorf("%w: ((rep).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
					continue
				}
				var condition20 distsys.TLAValue
				condition20, err = ctx.Read(rep, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition21 distsys.TLAValue
				condition21, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition20.ApplyFunction(distsys.NewTLAString("id")), condition21.ApplyFunction(distsys.NewTLAString("id"))).AsBool() {
					err = fmt.Errorf("%w: ((rep).id) = ((msg).id)", distsys.ErrAssertionFailed)
					continue
				}
				// no statements
			} else {
				// no statements
			}
			var exprRead16 distsys.TLAValue
			exprRead16, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(idx, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead16, distsys.NewTLANumber(1)))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case sndRespLabelTag:
			var exprRead17 distsys.TLAValue
			exprRead17, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead18 distsys.TLAValue
			exprRead18, err = ctx.Read(respBody, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead19 distsys.TLAValue
			exprRead19, err = ctx.Read(respTyp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead20 distsys.TLAValue
			exprRead20, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(resp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), self},
				{distsys.NewTLAString("to"), exprRead17.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead18},
				{distsys.NewTLAString("srcTyp"), func() distsys.TLAValue {
					return PRIMARY_SRC(constants)
				}()},
				{distsys.NewTLAString("typ"), exprRead19},
				{distsys.NewTLAString("id"), exprRead20.ApplyFunction(distsys.NewTLAString("id"))},
			}))
			if err != nil {
				continue
			}
			var exprRead21 distsys.TLAValue
			exprRead21, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead4 distsys.TLAValue
			indexRead4, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead5 distsys.TLAValue
			indexRead5, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(net, []distsys.TLAValue{distsys.NewTLATuple(indexRead4.ApplyFunction(distsys.NewTLAString("to")), indexRead5.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead21)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case failLabelLabelTag:
			err = ctx.Write(fd, []distsys.TLAValue{self}, distsys.TLA_FALSE)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case DoneLabelTag:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag)
		}
	}
}

func AClient(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net0 distsys.ArchetypeResourceHandle, fd0 distsys.ArchetypeResourceHandle) error {
	var err0 error
	// label tags
	const (
		InitLabelTag0 = iota
		sndPutReqLabelTag
		sndPutReqLoopLabelTag
		sndPutMsgLabelTag
		rcvPutRespLabelTag
		sndGetReqLabelTag
		sndGetReqLoopLabelTag
		sndGetMsgLabelTag
		rcvGetRespLabelTag
		DoneLabelTag0
	)
	programCounter0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag0)))
	req := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = req
	resp0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = resp0
	idx0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = idx0
	body := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = body

	for {
		if err0 != nil {
			if err0 == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err0 = nil
			} else {
				return err0
			}
		}
		var labelTag0 distsys.TLAValue
		labelTag0, err0 = ctx.Read(programCounter0, []distsys.TLAValue{})
		if err0 != nil {
			return err0
		}
		switch labelTag0.AsNumber() {
		case InitLabelTag0:
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndPutReqLabelTag))
			if err0 != nil {
				continue
			}
		case sndPutReqLabelTag:
			err0 = ctx.Write(idx0, []distsys.TLAValue{}, distsys.NewTLANumber(1))
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndPutReqLoopLabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case sndPutReqLoopLabelTag:
			var condition22 distsys.TLAValue
			condition22, err0 = ctx.Read(idx0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition22, constants.NUM_REPLICAS).AsBool() {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndPutMsgLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(rcvPutRespLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case sndPutMsgLabelTag:
			var condition23 distsys.TLAValue
			condition23, err0 = ctx.Read(idx0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition24 distsys.TLAValue
			condition24, err0 = ctx.Read(fd0, []distsys.TLAValue{condition23})
			if err0 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition24, distsys.TLA_TRUE).AsBool() {
				err0 = ctx.Write(body, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("key"), func() distsys.TLAValue {
						return KEY1(constants)
					}()},
					{distsys.NewTLAString("value"), func() distsys.TLAValue {
						return VALUE1(constants)
					}()},
				}))
				if err0 != nil {
					continue
				}
				var exprRead24 distsys.TLAValue
				exprRead24, err0 = ctx.Read(idx0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var exprRead25 distsys.TLAValue
				exprRead25, err0 = ctx.Read(body, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), self},
					{distsys.NewTLAString("to"), exprRead24},
					{distsys.NewTLAString("body"), exprRead25},
					{distsys.NewTLAString("srcTyp"), func() distsys.TLAValue {
						return CLIENT_SRC(constants)
					}()},
					{distsys.NewTLAString("typ"), func() distsys.TLAValue {
						return PUT_REQ(constants)
					}()},
					{distsys.NewTLAString("id"), distsys.NewTLANumber(1)},
				}))
				if err0 != nil {
					continue
				}
				var exprRead26 distsys.TLAValue
				exprRead26, err0 = ctx.Read(req, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var indexRead6 distsys.TLAValue
				indexRead6, err0 = ctx.Read(req, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var indexRead7 distsys.TLAValue
				indexRead7, err0 = ctx.Read(req, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(net0, []distsys.TLAValue{distsys.NewTLATuple(indexRead6.ApplyFunction(distsys.NewTLAString("to")), indexRead7.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead26)
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(rcvPutRespLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndPutReqLoopLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case rcvPutRespLabelTag:
			var condition25 distsys.TLAValue
			condition25, err0 = ctx.Read(idx0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition26 distsys.TLAValue
			condition26, err0 = ctx.Read(fd0, []distsys.TLAValue{condition25})
			if err0 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition26, distsys.TLA_TRUE).AsBool() {
				var exprRead27 distsys.TLAValue
				exprRead27, err0 = ctx.Read(net0, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
					return PUT_RESP(constants)
				}())})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(resp0, []distsys.TLAValue{}, exprRead27)
				if err0 != nil {
					continue
				}
				var condition27 distsys.TLAValue
				condition27, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition27.ApplyFunction(distsys.NewTLAString("to")), self).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
					continue
				}
				var condition28 distsys.TLAValue
				condition28, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition28.ApplyFunction(distsys.NewTLAString("body")), func() distsys.TLAValue {
					return ACK_MSG(constants)
				}()).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).body) = (ACK_MSG)", distsys.ErrAssertionFailed)
					continue
				}
				var condition29 distsys.TLAValue
				condition29, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition29.ApplyFunction(distsys.NewTLAString("srcTyp")), func() distsys.TLAValue {
					return PRIMARY_SRC(constants)
				}()).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).srcTyp) = (PRIMARY_SRC)", distsys.ErrAssertionFailed)
					continue
				}
				var condition30 distsys.TLAValue
				condition30, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition30.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
					return PUT_RESP(constants)
				}()).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).typ) = (PUT_RESP)", distsys.ErrAssertionFailed)
					continue
				}
				var condition31 distsys.TLAValue
				condition31, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition31.ApplyFunction(distsys.NewTLAString("id")), distsys.NewTLANumber(1)).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).id) = (1)", distsys.ErrAssertionFailed)
					continue
				}
				var toPrint distsys.TLAValue
				toPrint, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				distsys.NewTLATuple(distsys.NewTLAString("PUT RESP: "), toPrint).PCalPrint()
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndGetReqLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndPutReqLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case sndGetReqLabelTag:
			err0 = ctx.Write(idx0, []distsys.TLAValue{}, distsys.NewTLANumber(1))
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndGetReqLoopLabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case sndGetReqLoopLabelTag:
			var condition32 distsys.TLAValue
			condition32, err0 = ctx.Read(idx0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition32, constants.NUM_REPLICAS).AsBool() {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndGetMsgLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(rcvGetRespLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case sndGetMsgLabelTag:
			var condition33 distsys.TLAValue
			condition33, err0 = ctx.Read(idx0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition34 distsys.TLAValue
			condition34, err0 = ctx.Read(fd0, []distsys.TLAValue{condition33})
			if err0 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition34, distsys.TLA_TRUE).AsBool() {
				err0 = ctx.Write(body, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("key"), func() distsys.TLAValue {
						return KEY1(constants)
					}()},
					{distsys.NewTLAString("value"), func() distsys.TLAValue {
						return TEMP_VAL(constants)
					}()},
				}))
				if err0 != nil {
					continue
				}
				var exprRead28 distsys.TLAValue
				exprRead28, err0 = ctx.Read(idx0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var exprRead29 distsys.TLAValue
				exprRead29, err0 = ctx.Read(body, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), self},
					{distsys.NewTLAString("to"), exprRead28},
					{distsys.NewTLAString("body"), exprRead29},
					{distsys.NewTLAString("srcTyp"), func() distsys.TLAValue {
						return CLIENT_SRC(constants)
					}()},
					{distsys.NewTLAString("typ"), func() distsys.TLAValue {
						return GET_REQ(constants)
					}()},
					{distsys.NewTLAString("id"), distsys.NewTLANumber(2)},
				}))
				if err0 != nil {
					continue
				}
				var exprRead30 distsys.TLAValue
				exprRead30, err0 = ctx.Read(req, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var indexRead8 distsys.TLAValue
				indexRead8, err0 = ctx.Read(req, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var indexRead9 distsys.TLAValue
				indexRead9, err0 = ctx.Read(req, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(net0, []distsys.TLAValue{distsys.NewTLATuple(indexRead8.ApplyFunction(distsys.NewTLAString("to")), indexRead9.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead30)
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(rcvGetRespLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndGetReqLoopLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case rcvGetRespLabelTag:
			var condition35 distsys.TLAValue
			condition35, err0 = ctx.Read(idx0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition36 distsys.TLAValue
			condition36, err0 = ctx.Read(fd0, []distsys.TLAValue{condition35})
			if err0 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition36, distsys.TLA_TRUE).AsBool() {
				var exprRead31 distsys.TLAValue
				exprRead31, err0 = ctx.Read(net0, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
					return GET_RESP(constants)
				}())})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(resp0, []distsys.TLAValue{}, exprRead31)
				if err0 != nil {
					continue
				}
				var condition37 distsys.TLAValue
				condition37, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition37.ApplyFunction(distsys.NewTLAString("to")), self).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).to) = (self)", distsys.ErrAssertionFailed)
					continue
				}
				var condition38 distsys.TLAValue
				condition38, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition38.ApplyFunction(distsys.NewTLAString("body")), func() distsys.TLAValue {
					return VALUE1(constants)
				}()).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).body) = (VALUE1)", distsys.ErrAssertionFailed)
					continue
				}
				var condition39 distsys.TLAValue
				condition39, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition39.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
					return GET_RESP(constants)
				}()).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).typ) = (GET_RESP)", distsys.ErrAssertionFailed)
					continue
				}
				var condition40 distsys.TLAValue
				condition40, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition40.ApplyFunction(distsys.NewTLAString("id")), distsys.NewTLANumber(2)).AsBool() {
					err0 = fmt.Errorf("%w: ((resp).id) = (2)", distsys.ErrAssertionFailed)
					continue
				}
				var toPrint0 distsys.TLAValue
				toPrint0, err0 = ctx.Read(resp0, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				distsys.NewTLATuple(distsys.NewTLAString("GET RESP: "), toPrint0).PCalPrint()
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag0))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(sndGetReqLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case DoneLabelTag0:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag0)
		}
	}
}
