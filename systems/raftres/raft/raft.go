package raft

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
func Min(iface distsys.ArchetypeInterface, s tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		var e tla.TLAValue = tla.TLAChoose(s, func(element tla.TLAValue) bool {
			var e0 tla.TLAValue = element
			_ = e0
			return tla.TLA_TRUE.AsBool()
		})
		_ = e
		return MinAcc(iface, tla.TLA_BackslashSymbol(s, tla.MakeTLASet(e)), e)
	}()
}
func MinAcc(iface distsys.ArchetypeInterface, s0 tla.TLAValue, e1 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_EqualsSymbol(s0, tla.MakeTLASet()).AsBool() {
			return e1
		} else {
			return func() tla.TLAValue {
				var e2 tla.TLAValue = tla.TLAChoose(s0, func(element0 tla.TLAValue) bool {
					var e20 tla.TLAValue = element0
					_ = e20
					return tla.TLA_TRUE.AsBool()
				})
				_ = e2
				return MinAcc(iface, tla.TLA_BackslashSymbol(s0, tla.MakeTLASet(e2)), func() tla.TLAValue {
					if tla.TLA_LessThanSymbol(e2, e1).AsBool() {
						return e2
					} else {
						return e1
					}
				}())
			}()
		}
	}()
}
func Max(iface distsys.ArchetypeInterface, s1 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		var e3 tla.TLAValue = tla.TLAChoose(s1, func(element1 tla.TLAValue) bool {
			var e4 tla.TLAValue = element1
			_ = e4
			return tla.TLA_TRUE.AsBool()
		})
		_ = e3
		return MaxAcc(iface, tla.TLA_BackslashSymbol(s1, tla.MakeTLASet(e3)), e3)
	}()
}
func MaxAcc(iface distsys.ArchetypeInterface, s2 tla.TLAValue, e10 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_EqualsSymbol(s2, tla.MakeTLASet()).AsBool() {
			return e10
		} else {
			return func() tla.TLAValue {
				var e21 tla.TLAValue = tla.TLAChoose(s2, func(element2 tla.TLAValue) bool {
					var e22 tla.TLAValue = element2
					_ = e22
					return tla.TLA_TRUE.AsBool()
				})
				_ = e21
				return MaxAcc(iface, tla.TLA_BackslashSymbol(s2, tla.MakeTLASet(e21)), func() tla.TLAValue {
					if tla.TLA_GreaterThanSymbol(e21, e10).AsBool() {
						return e21
					} else {
						return e10
					}
				}())
			}()
		}
	}()
}
func IsQuorum(iface distsys.ArchetypeInterface, s3 tla.TLAValue) tla.TLAValue {
	return tla.TLA_GreaterThanSymbol(tla.TLA_AsteriskSymbol(tla.TLA_Cardinality(s3), tla.MakeTLANumber(2)), iface.GetConstant("NumServers")())
}
func ServerSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumServers")())
}
func FindMaxAgreeIndex(iface distsys.ArchetypeInterface, logLocal tla.TLAValue, i tla.TLAValue, matchIndex tla.TLAValue) tla.TLAValue {
	return FindMaxAgreeIndexRec(iface, logLocal, i, matchIndex, tla.TLA_Len(logLocal))
}
func FindMaxAgreeIndexRec(iface distsys.ArchetypeInterface, logLocal0 tla.TLAValue, i0 tla.TLAValue, matchIndex0 tla.TLAValue, index tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_EqualsSymbol(index, tla.MakeTLANumber(0)).AsBool() {
			return Nil(iface)
		} else {
			return func() tla.TLAValue {
				if IsQuorum(iface, tla.TLA_UnionSymbol(tla.MakeTLASet(i0), tla.TLASetRefinement(ServerSet(iface), func(elem tla.TLAValue) bool {
					var k tla.TLAValue = elem
					_ = k
					return tla.TLA_GreaterThanOrEqualSymbol(matchIndex0.ApplyFunction(k), index).AsBool()
				}))).AsBool() {
					return index
				} else {
					return FindMaxAgreeIndexRec(iface, logLocal0, i0, matchIndex0, tla.TLA_MinusSymbol(index, tla.MakeTLANumber(1)))
				}
			}()
		}
	}()
}
func Follower(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("follower")
}
func Candidate(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("candidate")
}
func Leader(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("leader")
}
func RequestVoteRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("rvq")
}
func RequestVoteResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("rvp")
}
func AppendEntriesRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("apq")
}
func AppendEntriesResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("app")
}
func ProposeMessage(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("prm")
}
func AcceptMessage(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("acm")
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
func LastTerm(iface distsys.ArchetypeInterface, xlog tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_EqualsSymbol(tla.TLA_Len(xlog), tla.MakeTLANumber(0)).AsBool() {
			return tla.MakeTLANumber(0)
		} else {
			return xlog.ApplyFunction(tla.TLA_Len(xlog)).ApplyFunction(tla.MakeTLAString("term"))
		}
	}()
}
func ServerRequestVoteSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(2), iface.GetConstant("NumServers")()))
}
func ServerAppendEntriesSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(2), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(3), iface.GetConstant("NumServers")()))
}
func ServerAdvanceCommitIndexSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(3), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(4), iface.GetConstant("NumServers")()))
}
func ServerBecomeLeaderSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(4), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()))
}
func ServerFollowerAdvanceCommitIndexSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(6), iface.GetConstant("NumServers")()))
}
func ServerCrasherSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return func() tla.TLAValue {
		if iface.GetConstant("ExploreFail")().AsBool() {
			return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(6), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(6), iface.GetConstant("NumServers")()), iface.GetConstant("MaxNodeFail")()))
		} else {
			return tla.MakeTLASet()
		}
	}()
}
func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return ServerSet(iface)
}
func KeySet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet()
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m := iface.RequireArchetypeResource("AServer.m")
			net, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			propCh, err := iface.RequireArchetypeResourceRef("AServer.propCh")
			if err != nil {
				return err
			}
			currentTerm, err := iface.RequireArchetypeResourceRef("AServer.currentTerm")
			if err != nil {
				return err
			}
			state, err := iface.RequireArchetypeResourceRef("AServer.state")
			if err != nil {
				return err
			}
			leader, err := iface.RequireArchetypeResourceRef("AServer.leader")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				switch iface.NextFairnessCounter("AServer.serverLoop.0", 2) {
				case 0:
					var exprRead tla.TLAValue
					exprRead, err = iface.Read(net, []tla.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					err = iface.Write(m, []tla.TLAValue{}, exprRead)
					if err != nil {
						return err
					}
					var condition tla.TLAValue
					condition, err = iface.Read(m, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("mdest")), iface.Self()).AsBool() {
						return fmt.Errorf("%w: ((m).mdest) = (self)", distsys.ErrAssertionFailed)
					}
					return iface.Goto("AServer.handleMsg")
				case 1:
					var exprRead0 tla.TLAValue
					exprRead0, err = iface.Read(propCh, []tla.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					err = iface.Write(m, []tla.TLAValue{}, exprRead0)
					if err != nil {
						return err
					}
					if iface.GetConstant("Debug")().AsBool() {
						var toPrint tla.TLAValue
						toPrint, err = iface.Read(currentTerm, []tla.TLAValue{iface.Self()})
						if err != nil {
							return err
						}
						var toPrint0 tla.TLAValue
						toPrint0, err = iface.Read(state, []tla.TLAValue{iface.Self()})
						if err != nil {
							return err
						}
						var toPrint1 tla.TLAValue
						toPrint1, err = iface.Read(leader, []tla.TLAValue{iface.Self()})
						if err != nil {
							return err
						}
						var toPrint2 tla.TLAValue
						toPrint2, err = iface.Read(m, []tla.TLAValue{})
						if err != nil {
							return err
						}
						tla.MakeTLATuple(tla.MakeTLAString("ReceiveProposeMessage"), iface.Self(), toPrint, toPrint0, toPrint1, toPrint2).PCalPrint()
						return iface.Goto("AServer.handleMsg")
					} else {
						return iface.Goto("AServer.handleMsg")
					}
					// no statements
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AServer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.handleMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m3 := iface.RequireArchetypeResource("AServer.m")
			currentTerm0, err := iface.RequireArchetypeResourceRef("AServer.currentTerm")
			if err != nil {
				return err
			}
			state0, err := iface.RequireArchetypeResourceRef("AServer.state")
			if err != nil {
				return err
			}
			votedFor, err := iface.RequireArchetypeResourceRef("AServer.votedFor")
			if err != nil {
				return err
			}
			leader0, err := iface.RequireArchetypeResourceRef("AServer.leader")
			if err != nil {
				return err
			}
			log, err := iface.RequireArchetypeResourceRef("AServer.log")
			if err != nil {
				return err
			}
			net0, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			votesResponded, err := iface.RequireArchetypeResourceRef("AServer.votesResponded")
			if err != nil {
				return err
			}
			votesGranted, err := iface.RequireArchetypeResourceRef("AServer.votesGranted")
			if err != nil {
				return err
			}
			becomeLeaderCh, err := iface.RequireArchetypeResourceRef("AServer.becomeLeaderCh")
			if err != nil {
				return err
			}
			leaderTimeout, err := iface.RequireArchetypeResourceRef("AServer.leaderTimeout")
			if err != nil {
				return err
			}
			plog, err := iface.RequireArchetypeResourceRef("AServer.plog")
			if err != nil {
				return err
			}
			fAdvCommitIdxCh, err := iface.RequireArchetypeResourceRef("AServer.fAdvCommitIdxCh")
			if err != nil {
				return err
			}
			nextIndex, err := iface.RequireArchetypeResourceRef("AServer.nextIndex")
			if err != nil {
				return err
			}
			matchIndex1, err := iface.RequireArchetypeResourceRef("AServer.matchIndex")
			if err != nil {
				return err
			}
			var condition0 tla.TLAValue
			condition0, err = iface.Read(m3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition0.ApplyFunction(tla.MakeTLAString("mtype")), RequestVoteRequest(iface)).AsBool() {
				var condition1 tla.TLAValue
				condition1, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition2 tla.TLAValue
				condition2, err = iface.Read(currentTerm0, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				if tla.TLA_GreaterThanSymbol(condition1.ApplyFunction(tla.MakeTLAString("mterm")), condition2).AsBool() {
					var exprRead1 tla.TLAValue
					exprRead1, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(currentTerm0, []tla.TLAValue{iface.Self()}, exprRead1.ApplyFunction(tla.MakeTLAString("mterm")))
					if err != nil {
						return err
					}
					err = iface.Write(state0, []tla.TLAValue{iface.Self()}, Follower(iface))
					if err != nil {
						return err
					}
					err = iface.Write(votedFor, []tla.TLAValue{iface.Self()}, Nil(iface))
					if err != nil {
						return err
					}
					err = iface.Write(leader0, []tla.TLAValue{iface.Self()}, Nil(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var i1 tla.TLAValue = iface.Self()
				_ = i1
				var jRead tla.TLAValue
				jRead, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var j tla.TLAValue = jRead.ApplyFunction(tla.MakeTLAString("msource"))
				_ = j
				var logOKRead tla.TLAValue
				logOKRead, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead0 tla.TLAValue
				logOKRead0, err = iface.Read(log, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				var logOKRead1 tla.TLAValue
				logOKRead1, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead2 tla.TLAValue
				logOKRead2, err = iface.Read(log, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				var logOKRead3 tla.TLAValue
				logOKRead3, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead4 tla.TLAValue
				logOKRead4, err = iface.Read(log, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				var logOK tla.TLAValue = tla.MakeTLABool(tla.TLA_GreaterThanSymbol(logOKRead.ApplyFunction(tla.MakeTLAString("mlastLogTerm")), LastTerm(iface, logOKRead0)).AsBool() || tla.MakeTLABool(tla.TLA_EqualsSymbol(logOKRead1.ApplyFunction(tla.MakeTLAString("mlastLogTerm")), LastTerm(iface, logOKRead2)).AsBool() && tla.TLA_GreaterThanOrEqualSymbol(logOKRead3.ApplyFunction(tla.MakeTLAString("mlastLogIndex")), tla.TLA_Len(logOKRead4)).AsBool()).AsBool())
				_ = logOK
				var grantRead tla.TLAValue
				grantRead, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var grantRead0 tla.TLAValue
				grantRead0, err = iface.Read(currentTerm0, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				var grantRead1 tla.TLAValue
				grantRead1, err = iface.Read(votedFor, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				var grant tla.TLAValue = tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(grantRead.ApplyFunction(tla.MakeTLAString("mterm")), grantRead0).AsBool() && logOK.AsBool()).AsBool() && tla.TLA_InSymbol(grantRead1, tla.MakeTLASet(Nil(iface), j)).AsBool())
				_ = grant
				var condition3 tla.TLAValue
				condition3, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition4 tla.TLAValue
				condition4, err = iface.Read(currentTerm0, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				if !tla.TLA_LessThanOrEqualSymbol(condition3.ApplyFunction(tla.MakeTLAString("mterm")), condition4).AsBool() {
					return fmt.Errorf("%w: ((m).mterm) <= ((currentTerm)[i])", distsys.ErrAssertionFailed)
				}
				if grant.AsBool() {
					err = iface.Write(votedFor, []tla.TLAValue{i1}, j)
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				switch iface.NextFairnessCounter("AServer.handleMsg.0", 2) {
				case 0:
					var exprRead21 tla.TLAValue
					exprRead21, err = iface.Read(currentTerm0, []tla.TLAValue{i1})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.TLAValue{j}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("mtype"), RequestVoteResponse(iface)},
						{tla.MakeTLAString("mterm"), exprRead21},
						{tla.MakeTLAString("mvoteGranted"), grant},
						{tla.MakeTLAString("msource"), i1},
						{tla.MakeTLAString("mdest"), j},
					}))
					if err != nil {
						return err
					}
					// no statements
				case 1:
					var condition56 tla.TLAValue
					condition56, err = iface.Read(fd, []tla.TLAValue{j})
					if err != nil {
						return err
					}
					if !condition56.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					// no statements
				default:
					panic("current branch of either matches no code paths!")
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint3 tla.TLAValue
					toPrint3, err = iface.Read(currentTerm0, []tla.TLAValue{i1})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("HandleRequestVoteRequest"), i1, j, toPrint3, grant).PCalPrint()
					return iface.Goto("AServer.serverLoop")
				} else {
					return iface.Goto("AServer.serverLoop")
				}
				// no statements
				// no statements
			} else {
				var condition5 tla.TLAValue
				condition5, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition5.ApplyFunction(tla.MakeTLAString("mtype")), RequestVoteResponse(iface)).AsBool() {
					var condition6 tla.TLAValue
					condition6, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition7 tla.TLAValue
					condition7, err = iface.Read(currentTerm0, []tla.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					if tla.TLA_GreaterThanSymbol(condition6.ApplyFunction(tla.MakeTLAString("mterm")), condition7).AsBool() {
						var exprRead2 tla.TLAValue
						exprRead2, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(currentTerm0, []tla.TLAValue{iface.Self()}, exprRead2.ApplyFunction(tla.MakeTLAString("mterm")))
						if err != nil {
							return err
						}
						err = iface.Write(state0, []tla.TLAValue{iface.Self()}, Follower(iface))
						if err != nil {
							return err
						}
						err = iface.Write(votedFor, []tla.TLAValue{iface.Self()}, Nil(iface))
						if err != nil {
							return err
						}
						err = iface.Write(leader0, []tla.TLAValue{iface.Self()}, Nil(iface))
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					var condition8 tla.TLAValue
					condition8, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition9 tla.TLAValue
					condition9, err = iface.Read(currentTerm0, []tla.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					if tla.TLA_LessThanSymbol(condition8.ApplyFunction(tla.MakeTLAString("mterm")), condition9).AsBool() {
						// skip
						return iface.Goto("AServer.serverLoop")
					} else {
						var i2 tla.TLAValue = iface.Self()
						_ = i2
						var jRead0 tla.TLAValue
						jRead0, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var j0 tla.TLAValue = jRead0.ApplyFunction(tla.MakeTLAString("msource"))
						_ = j0
						var condition10 tla.TLAValue
						condition10, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition11 tla.TLAValue
						condition11, err = iface.Read(currentTerm0, []tla.TLAValue{i2})
						if err != nil {
							return err
						}
						if !tla.TLA_EqualsSymbol(condition10.ApplyFunction(tla.MakeTLAString("mterm")), condition11).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
						var exprRead3 tla.TLAValue
						exprRead3, err = iface.Read(votesResponded, []tla.TLAValue{i2})
						if err != nil {
							return err
						}
						err = iface.Write(votesResponded, []tla.TLAValue{i2}, tla.TLA_UnionSymbol(exprRead3, tla.MakeTLASet(j0)))
						if err != nil {
							return err
						}
						var condition12 tla.TLAValue
						condition12, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if condition12.ApplyFunction(tla.MakeTLAString("mvoteGranted")).AsBool() {
							var exprRead4 tla.TLAValue
							exprRead4, err = iface.Read(votesGranted, []tla.TLAValue{i2})
							if err != nil {
								return err
							}
							err = iface.Write(votesGranted, []tla.TLAValue{i2}, tla.TLA_UnionSymbol(exprRead4, tla.MakeTLASet(j0)))
							if err != nil {
								return err
							}
							var condition13 tla.TLAValue
							condition13, err = iface.Read(state0, []tla.TLAValue{i2})
							if err != nil {
								return err
							}
							var condition14 tla.TLAValue
							condition14, err = iface.Read(votesGranted, []tla.TLAValue{i2})
							if err != nil {
								return err
							}
							if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition13, Candidate(iface)).AsBool() && IsQuorum(iface, condition14).AsBool()).AsBool() {
								err = iface.Write(becomeLeaderCh, []tla.TLAValue{i2}, tla.TLA_TRUE)
								if err != nil {
									return err
								}
								return iface.Goto("AServer.serverLoop")
							} else {
								return iface.Goto("AServer.serverLoop")
							}
							// no statements
						} else {
							return iface.Goto("AServer.serverLoop")
						}
						// no statements
						// no statements
					}
					// no statements
				} else {
					var condition15 tla.TLAValue
					condition15, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_EqualsSymbol(condition15.ApplyFunction(tla.MakeTLAString("mtype")), AppendEntriesRequest(iface)).AsBool() {
						var condition16 tla.TLAValue
						condition16, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition17 tla.TLAValue
						condition17, err = iface.Read(currentTerm0, []tla.TLAValue{iface.Self()})
						if err != nil {
							return err
						}
						if tla.TLA_GreaterThanSymbol(condition16.ApplyFunction(tla.MakeTLAString("mterm")), condition17).AsBool() {
							var exprRead5 tla.TLAValue
							exprRead5, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(currentTerm0, []tla.TLAValue{iface.Self()}, exprRead5.ApplyFunction(tla.MakeTLAString("mterm")))
							if err != nil {
								return err
							}
							err = iface.Write(state0, []tla.TLAValue{iface.Self()}, Follower(iface))
							if err != nil {
								return err
							}
							err = iface.Write(votedFor, []tla.TLAValue{iface.Self()}, Nil(iface))
							if err != nil {
								return err
							}
							err = iface.Write(leader0, []tla.TLAValue{iface.Self()}, Nil(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var i3 tla.TLAValue = iface.Self()
						_ = i3
						var jRead1 tla.TLAValue
						jRead1, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var j1 tla.TLAValue = jRead1.ApplyFunction(tla.MakeTLAString("msource"))
						_ = j1
						var logOKRead5 tla.TLAValue
						logOKRead5, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead6 tla.TLAValue
						logOKRead6, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead7 tla.TLAValue
						logOKRead7, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead8 tla.TLAValue
						logOKRead8, err = iface.Read(log, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var logOKRead9 tla.TLAValue
						logOKRead9, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead10 tla.TLAValue
						logOKRead10, err = iface.Read(log, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var logOKRead11 tla.TLAValue
						logOKRead11, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOK0 tla.TLAValue = tla.MakeTLABool(tla.TLA_EqualsSymbol(logOKRead5.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(0)).AsBool() || tla.MakeTLABool(tla.MakeTLABool(tla.TLA_GreaterThanSymbol(logOKRead6.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(0)).AsBool() && tla.TLA_LessThanOrEqualSymbol(logOKRead7.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.TLA_Len(logOKRead8)).AsBool()).AsBool() && tla.TLA_EqualsSymbol(logOKRead9.ApplyFunction(tla.MakeTLAString("mprevLogTerm")), logOKRead10.ApplyFunction(logOKRead11.ApplyFunction(tla.MakeTLAString("mprevLogIndex"))).ApplyFunction(tla.MakeTLAString("term"))).AsBool()).AsBool())
						_ = logOK0
						var condition18 tla.TLAValue
						condition18, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition19 tla.TLAValue
						condition19, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if !tla.TLA_LessThanOrEqualSymbol(condition18.ApplyFunction(tla.MakeTLAString("mterm")), condition19).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) <= ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
						var condition20 tla.TLAValue
						condition20, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition21 tla.TLAValue
						condition21, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if tla.TLA_EqualsSymbol(condition20.ApplyFunction(tla.MakeTLAString("mterm")), condition21).AsBool() {
							var exprRead6 tla.TLAValue
							exprRead6, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(leader0, []tla.TLAValue{i3}, exprRead6.ApplyFunction(tla.MakeTLAString("msource")))
							if err != nil {
								return err
							}
							err = iface.Write(leaderTimeout, []tla.TLAValue{}, iface.GetConstant("LeaderTimeoutReset")())
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition22 tla.TLAValue
						condition22, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition23 tla.TLAValue
						condition23, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var condition24 tla.TLAValue
						condition24, err = iface.Read(state0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition22.ApplyFunction(tla.MakeTLAString("mterm")), condition23).AsBool() && tla.TLA_EqualsSymbol(condition24, Candidate(iface)).AsBool()).AsBool() {
							err = iface.Write(state0, []tla.TLAValue{i3}, Follower(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition25 tla.TLAValue
						condition25, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition26 tla.TLAValue
						condition26, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var condition27 tla.TLAValue
						condition27, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition28 tla.TLAValue
						condition28, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var condition29 tla.TLAValue
						condition29, err = iface.Read(state0, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if tla.MakeTLABool(tla.TLA_LessThanSymbol(condition25.ApplyFunction(tla.MakeTLAString("mterm")), condition26).AsBool() || tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition27.ApplyFunction(tla.MakeTLAString("mterm")), condition28).AsBool() && tla.TLA_EqualsSymbol(condition29, Follower(iface)).AsBool()).AsBool() && tla.TLA_LogicalNotSymbol(logOK0).AsBool()).AsBool()).AsBool() {
							switch iface.NextFairnessCounter("AServer.handleMsg.1", 2) {
							case 0:
								var exprRead22 tla.TLAValue
								exprRead22, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.TLAValue{j1}, tla.MakeTLARecord([]tla.TLARecordField{
									{tla.MakeTLAString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeTLAString("mterm"), exprRead22},
									{tla.MakeTLAString("msuccess"), tla.TLA_FALSE},
									{tla.MakeTLAString("mmatchIndex"), tla.MakeTLANumber(0)},
									{tla.MakeTLAString("msource"), i3},
									{tla.MakeTLAString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServer.serverLoop")
							case 1:
								var condition57 tla.TLAValue
								condition57, err = iface.Read(fd, []tla.TLAValue{j1})
								if err != nil {
									return err
								}
								if !condition57.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServer.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
						} else {
							var condition30 tla.TLAValue
							condition30, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition31 tla.TLAValue
							condition31, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition32 tla.TLAValue
							condition32, err = iface.Read(state0, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							if !tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition30.ApplyFunction(tla.MakeTLAString("mterm")), condition31).AsBool() && tla.TLA_EqualsSymbol(condition32, Follower(iface)).AsBool()).AsBool() && logOK0.AsBool()).AsBool() {
								return fmt.Errorf("%w: ((((m).mterm) = ((currentTerm)[i])) /\\ (((state)[i]) = (Follower))) /\\ (logOK)", distsys.ErrAssertionFailed)
							}
							var indexRead tla.TLAValue
							indexRead, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var index0 tla.TLAValue = tla.TLA_PlusSymbol(indexRead.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(1))
							_ = index0
							var condition33 tla.TLAValue
							condition33, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition34 tla.TLAValue
							condition34, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition35 tla.TLAValue
							condition35, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition36 tla.TLAValue
							condition36, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.MakeTLABool(tla.MakeTLABool(tla.TLA_NotEqualsSymbol(condition33.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()).AsBool() && tla.TLA_GreaterThanOrEqualSymbol(tla.TLA_Len(condition34), index0).AsBool()).AsBool() && tla.TLA_NotEqualsSymbol(condition35.ApplyFunction(index0).ApplyFunction(tla.MakeTLAString("term")), condition36.ApplyFunction(tla.MakeTLAString("mentries")).ApplyFunction(tla.MakeTLANumber(1)).ApplyFunction(tla.MakeTLAString("term"))).AsBool()).AsBool() {
								var exprRead7 tla.TLAValue
								exprRead7, err = iface.Read(log, []tla.TLAValue{i3})
								if err != nil {
									return err
								}
								var exprRead8 tla.TLAValue
								exprRead8, err = iface.Read(log, []tla.TLAValue{i3})
								if err != nil {
									return err
								}
								err = iface.Write(log, []tla.TLAValue{i3}, tla.TLA_SubSeq(exprRead7, tla.MakeTLANumber(1), tla.TLA_MinusSymbol(tla.TLA_Len(exprRead8), tla.MakeTLANumber(1))))
								if err != nil {
									return err
								}
								err = iface.Write(plog, []tla.TLAValue{i3}, tla.MakeTLARecord([]tla.TLARecordField{
									{tla.MakeTLAString("cmd"), iface.GetConstant("LogPop")()},
								}))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition37 tla.TLAValue
							condition37, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition38 tla.TLAValue
							condition38, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition39 tla.TLAValue
							condition39, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.MakeTLABool(tla.TLA_NotEqualsSymbol(condition37.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()).AsBool() && tla.TLA_EqualsSymbol(tla.TLA_Len(condition38), condition39.ApplyFunction(tla.MakeTLAString("mprevLogIndex"))).AsBool()).AsBool() {
								var exprRead9 tla.TLAValue
								exprRead9, err = iface.Read(log, []tla.TLAValue{i3})
								if err != nil {
									return err
								}
								var exprRead10 tla.TLAValue
								exprRead10, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(log, []tla.TLAValue{i3}, tla.TLA_OSymbol(exprRead9, exprRead10.ApplyFunction(tla.MakeTLAString("mentries"))))
								if err != nil {
									return err
								}
								var exprRead11 tla.TLAValue
								exprRead11, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(plog, []tla.TLAValue{i3}, tla.MakeTLARecord([]tla.TLARecordField{
									{tla.MakeTLAString("cmd"), iface.GetConstant("LogConcat")()},
									{tla.MakeTLAString("entries"), exprRead11.ApplyFunction(tla.MakeTLAString("mentries"))},
								}))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition40 tla.TLAValue
							condition40, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition41 tla.TLAValue
							condition41, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition42 tla.TLAValue
							condition42, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition43 tla.TLAValue
							condition43, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition44 tla.TLAValue
							condition44, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition40.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()).AsBool() || tla.MakeTLABool(tla.MakeTLABool(tla.TLA_NotEqualsSymbol(condition41.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()).AsBool() && tla.TLA_GreaterThanOrEqualSymbol(tla.TLA_Len(condition42), index0).AsBool()).AsBool() && tla.TLA_EqualsSymbol(condition43.ApplyFunction(index0).ApplyFunction(tla.MakeTLAString("term")), condition44.ApplyFunction(tla.MakeTLAString("mentries")).ApplyFunction(tla.MakeTLANumber(1)).ApplyFunction(tla.MakeTLAString("term"))).AsBool()).AsBool()).AsBool() {
								var exprRead12 tla.TLAValue
								exprRead12, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(fAdvCommitIdxCh, []tla.TLAValue{i3}, exprRead12)
								if err != nil {
									return err
								}
								switch iface.NextFairnessCounter("AServer.handleMsg.2", 2) {
								case 0:
									var exprRead23 tla.TLAValue
									exprRead23, err = iface.Read(currentTerm0, []tla.TLAValue{i3})
									if err != nil {
										return err
									}
									var exprRead24 tla.TLAValue
									exprRead24, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var exprRead25 tla.TLAValue
									exprRead25, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(net0, []tla.TLAValue{j1}, tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("mtype"), AppendEntriesResponse(iface)},
										{tla.MakeTLAString("mterm"), exprRead23},
										{tla.MakeTLAString("msuccess"), tla.TLA_TRUE},
										{tla.MakeTLAString("mmatchIndex"), tla.TLA_PlusSymbol(exprRead24.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.TLA_Len(exprRead25.ApplyFunction(tla.MakeTLAString("mentries"))))},
										{tla.MakeTLAString("msource"), i3},
										{tla.MakeTLAString("mdest"), j1},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
								case 1:
									var condition58 tla.TLAValue
									condition58, err = iface.Read(fd, []tla.TLAValue{j1})
									if err != nil {
										return err
									}
									if !condition58.AsBool() {
										return distsys.ErrCriticalSectionAborted
									}
									return iface.Goto("AServer.serverLoop")
								default:
									panic("current branch of either matches no code paths!")
								}
								// no statements
							} else {
								return iface.Goto("AServer.serverLoop")
							}
							// no statements
							// no statements
						}
						// no statements
						// no statements
					} else {
						var condition45 tla.TLAValue
						condition45, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_EqualsSymbol(condition45.ApplyFunction(tla.MakeTLAString("mtype")), AppendEntriesResponse(iface)).AsBool() {
							var condition46 tla.TLAValue
							condition46, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition47 tla.TLAValue
							condition47, err = iface.Read(currentTerm0, []tla.TLAValue{iface.Self()})
							if err != nil {
								return err
							}
							if tla.TLA_GreaterThanSymbol(condition46.ApplyFunction(tla.MakeTLAString("mterm")), condition47).AsBool() {
								var exprRead13 tla.TLAValue
								exprRead13, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(currentTerm0, []tla.TLAValue{iface.Self()}, exprRead13.ApplyFunction(tla.MakeTLAString("mterm")))
								if err != nil {
									return err
								}
								err = iface.Write(state0, []tla.TLAValue{iface.Self()}, Follower(iface))
								if err != nil {
									return err
								}
								err = iface.Write(votedFor, []tla.TLAValue{iface.Self()}, Nil(iface))
								if err != nil {
									return err
								}
								err = iface.Write(leader0, []tla.TLAValue{iface.Self()}, Nil(iface))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition48 tla.TLAValue
							condition48, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition49 tla.TLAValue
							condition49, err = iface.Read(currentTerm0, []tla.TLAValue{iface.Self()})
							if err != nil {
								return err
							}
							if tla.TLA_LessThanSymbol(condition48.ApplyFunction(tla.MakeTLAString("mterm")), condition49).AsBool() {
								// skip
								return iface.Goto("AServer.serverLoop")
							} else {
								var i4 tla.TLAValue = iface.Self()
								_ = i4
								var jRead2 tla.TLAValue
								jRead2, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var j2 tla.TLAValue = jRead2.ApplyFunction(tla.MakeTLAString("msource"))
								_ = j2
								var condition50 tla.TLAValue
								condition50, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var condition51 tla.TLAValue
								condition51, err = iface.Read(currentTerm0, []tla.TLAValue{i4})
								if err != nil {
									return err
								}
								if !tla.TLA_EqualsSymbol(condition50.ApplyFunction(tla.MakeTLAString("mterm")), condition51).AsBool() {
									return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
								}
								var condition52 tla.TLAValue
								condition52, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								if condition52.ApplyFunction(tla.MakeTLAString("msuccess")).AsBool() {
									var exprRead14 tla.TLAValue
									exprRead14, err = iface.Read(nextIndex, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									var exprRead15 tla.TLAValue
									exprRead15, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.TLAValue{i4}, tla.TLAFunctionSubstitution(exprRead14, []tla.TLAFunctionSubstitutionRecord{
										{[]tla.TLAValue{j2}, func(anchor tla.TLAValue) tla.TLAValue {
											return tla.TLA_PlusSymbol(exprRead15.ApplyFunction(tla.MakeTLAString("mmatchIndex")), tla.MakeTLANumber(1))
										}},
									}))
									if err != nil {
										return err
									}
									var exprRead16 tla.TLAValue
									exprRead16, err = iface.Read(matchIndex1, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									var exprRead17 tla.TLAValue
									exprRead17, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(matchIndex1, []tla.TLAValue{i4}, tla.TLAFunctionSubstitution(exprRead16, []tla.TLAFunctionSubstitutionRecord{
										{[]tla.TLAValue{j2}, func(anchor0 tla.TLAValue) tla.TLAValue {
											return exprRead17.ApplyFunction(tla.MakeTLAString("mmatchIndex"))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
								} else {
									var exprRead18 tla.TLAValue
									exprRead18, err = iface.Read(nextIndex, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									var exprRead19 tla.TLAValue
									exprRead19, err = iface.Read(nextIndex, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.TLAValue{i4}, tla.TLAFunctionSubstitution(exprRead18, []tla.TLAFunctionSubstitutionRecord{
										{[]tla.TLAValue{j2}, func(anchor1 tla.TLAValue) tla.TLAValue {
											return Max(iface, tla.MakeTLASet(tla.TLA_MinusSymbol(exprRead19.ApplyFunction(j2), tla.MakeTLANumber(1)), tla.MakeTLANumber(1)))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
								}
								// no statements
								// no statements
							}
							// no statements
						} else {
							var condition53 tla.TLAValue
							condition53, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_EqualsSymbol(condition53.ApplyFunction(tla.MakeTLAString("mtype")), ProposeMessage(iface)).AsBool() {
								var i5 tla.TLAValue = iface.Self()
								_ = i5
								if iface.GetConstant("Debug")().AsBool() {
									var toPrint4 tla.TLAValue
									toPrint4, err = iface.Read(currentTerm0, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									var toPrint5 tla.TLAValue
									toPrint5, err = iface.Read(state0, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									var toPrint6 tla.TLAValue
									toPrint6, err = iface.Read(leader0, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									tla.MakeTLATuple(tla.MakeTLAString("HandleProposeMessage"), i5, toPrint4, toPrint5, toPrint6).PCalPrint()
									// no statements
								} else {
									// no statements
								}
								var condition54 tla.TLAValue
								condition54, err = iface.Read(state0, []tla.TLAValue{i5})
								if err != nil {
									return err
								}
								if tla.TLA_EqualsSymbol(condition54, Leader(iface)).AsBool() {
									var entryRead tla.TLAValue
									entryRead, err = iface.Read(currentTerm0, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									var entryRead0 tla.TLAValue
									entryRead0, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entry tla.TLAValue = tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("term"), entryRead},
										{tla.MakeTLAString("cmd"), entryRead0.ApplyFunction(tla.MakeTLAString("mcmd"))},
									})
									_ = entry
									var exprRead20 tla.TLAValue
									exprRead20, err = iface.Read(log, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									err = iface.Write(log, []tla.TLAValue{i5}, tla.TLA_Append(exprRead20, entry))
									if err != nil {
										return err
									}
									err = iface.Write(plog, []tla.TLAValue{i5}, tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("cmd"), iface.GetConstant("LogConcat")()},
										{tla.MakeTLAString("entries"), tla.MakeTLATuple(entry)},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
									// no statements
								} else {
									var condition55 tla.TLAValue
									condition55, err = iface.Read(leader0, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									if tla.TLA_NotEqualsSymbol(condition55, Nil(iface)).AsBool() {
										var jRead3 tla.TLAValue
										jRead3, err = iface.Read(leader0, []tla.TLAValue{i5})
										if err != nil {
											return err
										}
										var j3 tla.TLAValue = jRead3
										_ = j3
										switch iface.NextFairnessCounter("AServer.handleMsg.3", 2) {
										case 0:
											var exprRead26 tla.TLAValue
											exprRead26, err = iface.Read(m3, []tla.TLAValue{})
											if err != nil {
												return err
											}
											err = iface.Write(net0, []tla.TLAValue{j3}, tla.MakeTLARecord([]tla.TLARecordField{
												{tla.MakeTLAString("mtype"), ProposeMessage(iface)},
												{tla.MakeTLAString("mcmd"), exprRead26.ApplyFunction(tla.MakeTLAString("mcmd"))},
												{tla.MakeTLAString("msource"), i5},
												{tla.MakeTLAString("mdest"), j3},
											}))
											if err != nil {
												return err
											}
											return iface.Goto("AServer.serverLoop")
										case 1:
											var condition59 tla.TLAValue
											condition59, err = iface.Read(fd, []tla.TLAValue{j3})
											if err != nil {
												return err
											}
											if !condition59.AsBool() {
												return distsys.ErrCriticalSectionAborted
											}
											return iface.Goto("AServer.serverLoop")
										default:
											panic("current branch of either matches no code paths!")
										}
										// no statements
										// no statements
									} else {
										return iface.Goto("AServer.serverLoop")
									}
									// no statements
								}
								// no statements
								// no statements
							} else {
								return iface.Goto("AServer.serverLoop")
							}
							// no statements
						}
						// no statements
					}
					// no statements
				}
				// no statements
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerRequestVote.serverRequestVoteLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			leaderTimeout0, err := iface.RequireArchetypeResourceRef("AServerRequestVote.leaderTimeout")
			if err != nil {
				return err
			}
			netLen, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netLen")
			if err != nil {
				return err
			}
			srvId := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			state11, err := iface.RequireArchetypeResourceRef("AServerRequestVote.state")
			if err != nil {
				return err
			}
			currentTerm26, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
			if err != nil {
				return err
			}
			votedFor5, err := iface.RequireArchetypeResourceRef("AServerRequestVote.votedFor")
			if err != nil {
				return err
			}
			votesResponded1, err := iface.RequireArchetypeResourceRef("AServerRequestVote.votesResponded")
			if err != nil {
				return err
			}
			votesGranted2, err := iface.RequireArchetypeResourceRef("AServerRequestVote.votesGranted")
			if err != nil {
				return err
			}
			leader8, err := iface.RequireArchetypeResourceRef("AServerRequestVote.leader")
			if err != nil {
				return err
			}
			idx := iface.RequireArchetypeResource("AServerRequestVote.idx")
			if tla.TLA_TRUE.AsBool() {
				var condition60 tla.TLAValue
				condition60, err = iface.Read(leaderTimeout0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !condition60.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition61 tla.TLAValue
				condition61, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition62 tla.TLAValue
				condition62, err = iface.Read(netLen, []tla.TLAValue{condition61})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition62, tla.MakeTLANumber(0)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition63 tla.TLAValue
				condition63, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition64 tla.TLAValue
				condition64, err = iface.Read(state11, []tla.TLAValue{condition63})
				if err != nil {
					return err
				}
				if !tla.TLA_InSymbol(condition64, tla.MakeTLASet(Follower(iface), Candidate(iface))).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead tla.TLAValue
				iRead, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i6 tla.TLAValue = iRead
				_ = i6
				err = iface.Write(state11, []tla.TLAValue{i6}, Candidate(iface))
				if err != nil {
					return err
				}
				var exprRead27 tla.TLAValue
				exprRead27, err = iface.Read(currentTerm26, []tla.TLAValue{i6})
				if err != nil {
					return err
				}
				err = iface.Write(currentTerm26, []tla.TLAValue{i6}, tla.TLA_PlusSymbol(exprRead27, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(votedFor5, []tla.TLAValue{i6}, i6)
				if err != nil {
					return err
				}
				err = iface.Write(votesResponded1, []tla.TLAValue{i6}, tla.MakeTLASet(i6))
				if err != nil {
					return err
				}
				err = iface.Write(votesGranted2, []tla.TLAValue{i6}, tla.MakeTLASet(i6))
				if err != nil {
					return err
				}
				err = iface.Write(leader8, []tla.TLAValue{i6}, Nil(iface))
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint7 tla.TLAValue
					toPrint7, err = iface.Read(currentTerm26, []tla.TLAValue{i6})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ServerTimeout"), i6, toPrint7).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				// no statements
				err = iface.Write(idx, []tla.TLAValue{}, tla.MakeTLANumber(1))
				if err != nil {
					return err
				}
				return iface.Goto("AServerRequestVote.requestVoteLoop")
			} else {
				return iface.Goto("AServerRequestVote.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerRequestVote.requestVoteLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx0 := iface.RequireArchetypeResource("AServerRequestVote.idx")
			srvId2 := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			net4, err := iface.RequireArchetypeResourceRef("AServerRequestVote.net")
			if err != nil {
				return err
			}
			currentTerm29, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
			if err != nil {
				return err
			}
			log16, err := iface.RequireArchetypeResourceRef("AServerRequestVote.log")
			if err != nil {
				return err
			}
			fd3, err := iface.RequireArchetypeResourceRef("AServerRequestVote.fd")
			if err != nil {
				return err
			}
			var condition65 tla.TLAValue
			condition65, err = iface.Read(idx0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition65, iface.GetConstant("NumServers")()).AsBool() {
				var condition66 tla.TLAValue
				condition66, err = iface.Read(idx0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition67 tla.TLAValue
				condition67, err = iface.Read(srvId2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition66, condition67).AsBool() {
					switch iface.NextFairnessCounter("AServerRequestVote.requestVoteLoop.0", 2) {
					case 0:
						var exprRead29 tla.TLAValue
						exprRead29, err = iface.Read(srvId2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead30 tla.TLAValue
						exprRead30, err = iface.Read(currentTerm29, []tla.TLAValue{exprRead29})
						if err != nil {
							return err
						}
						var exprRead31 tla.TLAValue
						exprRead31, err = iface.Read(srvId2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead32 tla.TLAValue
						exprRead32, err = iface.Read(log16, []tla.TLAValue{exprRead31})
						if err != nil {
							return err
						}
						var exprRead33 tla.TLAValue
						exprRead33, err = iface.Read(srvId2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead34 tla.TLAValue
						exprRead34, err = iface.Read(log16, []tla.TLAValue{exprRead33})
						if err != nil {
							return err
						}
						var exprRead35 tla.TLAValue
						exprRead35, err = iface.Read(srvId2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead36 tla.TLAValue
						exprRead36, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead0 tla.TLAValue
						indexRead0, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net4, []tla.TLAValue{indexRead0}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), RequestVoteRequest(iface)},
							{tla.MakeTLAString("mterm"), exprRead30},
							{tla.MakeTLAString("mlastLogTerm"), LastTerm(iface, exprRead32)},
							{tla.MakeTLAString("mlastLogIndex"), tla.TLA_Len(exprRead34)},
							{tla.MakeTLAString("msource"), exprRead35},
							{tla.MakeTLAString("mdest"), exprRead36},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition68 tla.TLAValue
						condition68, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition69 tla.TLAValue
						condition69, err = iface.Read(fd3, []tla.TLAValue{condition68})
						if err != nil {
							return err
						}
						if !condition69.AsBool() {
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
				var exprRead28 tla.TLAValue
				exprRead28, err = iface.Read(idx0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead28, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AServerRequestVote.requestVoteLoop")
			} else {
				return iface.Goto("AServerRequestVote.serverRequestVoteLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerRequestVote.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAppendEntries.serverAppendEntriesLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			appendEntriesCh, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.appendEntriesCh")
			if err != nil {
				return err
			}
			state13, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			srvId7 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			idx7 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			var condition70 tla.TLAValue
			condition70, err = iface.Read(appendEntriesCh, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if condition70.AsBool() {
				var condition71 tla.TLAValue
				condition71, err = iface.Read(srvId7, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition72 tla.TLAValue
				condition72, err = iface.Read(state13, []tla.TLAValue{condition71})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition72, Leader(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				err = iface.Write(idx7, []tla.TLAValue{}, tla.MakeTLANumber(1))
				if err != nil {
					return err
				}
				return iface.Goto("AServerAppendEntries.appendEntriesLoop")
			} else {
				return iface.Goto("AServerAppendEntries.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAppendEntries.appendEntriesLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			state14, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			srvId8 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			idx8 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			nextIndex4, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.nextIndex")
			if err != nil {
				return err
			}
			log18, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.log")
			if err != nil {
				return err
			}
			net5, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.net")
			if err != nil {
				return err
			}
			currentTerm30, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.currentTerm")
			if err != nil {
				return err
			}
			commitIndex, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.commitIndex")
			if err != nil {
				return err
			}
			fd4, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.fd")
			if err != nil {
				return err
			}
			var condition73 tla.TLAValue
			condition73, err = iface.Read(srvId8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition74 tla.TLAValue
			condition74, err = iface.Read(state14, []tla.TLAValue{condition73})
			if err != nil {
				return err
			}
			var condition75 tla.TLAValue
			condition75, err = iface.Read(idx8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition74, Leader(iface)).AsBool() && tla.TLA_LessThanOrEqualSymbol(condition75, iface.GetConstant("NumServers")()).AsBool()).AsBool() {
				var condition76 tla.TLAValue
				condition76, err = iface.Read(idx8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition77 tla.TLAValue
				condition77, err = iface.Read(srvId8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition76, condition77).AsBool() {
					var prevLogIndexRead tla.TLAValue
					prevLogIndexRead, err = iface.Read(srvId8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogIndexRead0 tla.TLAValue
					prevLogIndexRead0, err = iface.Read(nextIndex4, []tla.TLAValue{prevLogIndexRead})
					if err != nil {
						return err
					}
					var prevLogIndexRead1 tla.TLAValue
					prevLogIndexRead1, err = iface.Read(idx8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogIndex tla.TLAValue = tla.TLA_MinusSymbol(prevLogIndexRead0.ApplyFunction(prevLogIndexRead1), tla.MakeTLANumber(1))
					_ = prevLogIndex
					var prevLogTermRead tla.TLAValue
					prevLogTermRead, err = iface.Read(srvId8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogTermRead0 tla.TLAValue
					prevLogTermRead0, err = iface.Read(log18, []tla.TLAValue{prevLogTermRead})
					if err != nil {
						return err
					}
					var prevLogTerm tla.TLAValue = func() tla.TLAValue {
						if tla.TLA_GreaterThanSymbol(prevLogIndex, tla.MakeTLANumber(0)).AsBool() {
							return prevLogTermRead0.ApplyFunction(prevLogIndex).ApplyFunction(tla.MakeTLAString("term"))
						} else {
							return tla.MakeTLANumber(0)
						}
					}()
					_ = prevLogTerm
					var lastEntryRead tla.TLAValue
					lastEntryRead, err = iface.Read(srvId8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var lastEntryRead0 tla.TLAValue
					lastEntryRead0, err = iface.Read(log18, []tla.TLAValue{lastEntryRead})
					if err != nil {
						return err
					}
					var lastEntryRead1 tla.TLAValue
					lastEntryRead1, err = iface.Read(srvId8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var lastEntryRead2 tla.TLAValue
					lastEntryRead2, err = iface.Read(nextIndex4, []tla.TLAValue{lastEntryRead1})
					if err != nil {
						return err
					}
					var lastEntryRead3 tla.TLAValue
					lastEntryRead3, err = iface.Read(idx8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var lastEntry tla.TLAValue = Min(iface, tla.MakeTLASet(tla.TLA_Len(lastEntryRead0), lastEntryRead2.ApplyFunction(lastEntryRead3)))
					_ = lastEntry
					var entriesRead tla.TLAValue
					entriesRead, err = iface.Read(srvId8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entriesRead0 tla.TLAValue
					entriesRead0, err = iface.Read(log18, []tla.TLAValue{entriesRead})
					if err != nil {
						return err
					}
					var entriesRead1 tla.TLAValue
					entriesRead1, err = iface.Read(srvId8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entriesRead2 tla.TLAValue
					entriesRead2, err = iface.Read(nextIndex4, []tla.TLAValue{entriesRead1})
					if err != nil {
						return err
					}
					var entriesRead3 tla.TLAValue
					entriesRead3, err = iface.Read(idx8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entries tla.TLAValue = tla.TLA_SubSeq(entriesRead0, entriesRead2.ApplyFunction(entriesRead3), lastEntry)
					_ = entries
					switch iface.NextFairnessCounter("AServerAppendEntries.appendEntriesLoop.0", 2) {
					case 0:
						var exprRead38 tla.TLAValue
						exprRead38, err = iface.Read(srvId8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead39 tla.TLAValue
						exprRead39, err = iface.Read(currentTerm30, []tla.TLAValue{exprRead38})
						if err != nil {
							return err
						}
						var exprRead40 tla.TLAValue
						exprRead40, err = iface.Read(srvId8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead41 tla.TLAValue
						exprRead41, err = iface.Read(commitIndex, []tla.TLAValue{exprRead40})
						if err != nil {
							return err
						}
						var exprRead42 tla.TLAValue
						exprRead42, err = iface.Read(srvId8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead43 tla.TLAValue
						exprRead43, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead1 tla.TLAValue
						indexRead1, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net5, []tla.TLAValue{indexRead1}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), AppendEntriesRequest(iface)},
							{tla.MakeTLAString("mterm"), exprRead39},
							{tla.MakeTLAString("mprevLogIndex"), prevLogIndex},
							{tla.MakeTLAString("mprevLogTerm"), prevLogTerm},
							{tla.MakeTLAString("mentries"), entries},
							{tla.MakeTLAString("mcommitIndex"), Min(iface, tla.MakeTLASet(exprRead41, lastEntry))},
							{tla.MakeTLAString("msource"), exprRead42},
							{tla.MakeTLAString("mdest"), exprRead43},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition78 tla.TLAValue
						condition78, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition79 tla.TLAValue
						condition79, err = iface.Read(fd4, []tla.TLAValue{condition78})
						if err != nil {
							return err
						}
						if !condition79.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
					// no statements
				} else {
					// no statements
				}
				var exprRead37 tla.TLAValue
				exprRead37, err = iface.Read(idx8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx8, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead37, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AServerAppendEntries.appendEntriesLoop")
			} else {
				return iface.Goto("AServerAppendEntries.serverAppendEntriesLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAppendEntries.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAdvanceCommitIndex.serverAdvanceCommitIndexLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			state15, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.state")
			if err != nil {
				return err
			}
			srvId19 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			log21, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			matchIndex3, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.matchIndex")
			if err != nil {
				return err
			}
			currentTerm31, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.currentTerm")
			if err != nil {
				return err
			}
			commitIndex0, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			newCommitIndex := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			if tla.TLA_TRUE.AsBool() {
				var condition80 tla.TLAValue
				condition80, err = iface.Read(srvId19, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition81 tla.TLAValue
				condition81, err = iface.Read(state15, []tla.TLAValue{condition80})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition81, Leader(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead0 tla.TLAValue
				iRead0, err = iface.Read(srvId19, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i7 tla.TLAValue = iRead0
				_ = i7
				var maxAgreeIndexRead tla.TLAValue
				maxAgreeIndexRead, err = iface.Read(log21, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var maxAgreeIndexRead0 tla.TLAValue
				maxAgreeIndexRead0, err = iface.Read(matchIndex3, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var maxAgreeIndex tla.TLAValue = FindMaxAgreeIndex(iface, maxAgreeIndexRead, i7, maxAgreeIndexRead0)
				_ = maxAgreeIndex
				var nCommitIndexRead tla.TLAValue
				nCommitIndexRead, err = iface.Read(log21, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var nCommitIndexRead0 tla.TLAValue
				nCommitIndexRead0, err = iface.Read(currentTerm31, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var nCommitIndexRead1 tla.TLAValue
				nCommitIndexRead1, err = iface.Read(commitIndex0, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var nCommitIndex tla.TLAValue = func() tla.TLAValue {
					if tla.MakeTLABool(tla.TLA_NotEqualsSymbol(maxAgreeIndex, Nil(iface)).AsBool() && tla.TLA_EqualsSymbol(nCommitIndexRead.ApplyFunction(maxAgreeIndex).ApplyFunction(tla.MakeTLAString("term")), nCommitIndexRead0).AsBool()).AsBool() {
						return maxAgreeIndex
					} else {
						return nCommitIndexRead1
					}
				}()
				_ = nCommitIndex
				err = iface.Write(newCommitIndex, []tla.TLAValue{}, nCommitIndex)
				if err != nil {
					return err
				}
				var condition82 tla.TLAValue
				condition82, err = iface.Read(newCommitIndex, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition83 tla.TLAValue
				condition83, err = iface.Read(commitIndex0, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				if !tla.TLA_GreaterThanOrEqualSymbol(condition82, condition83).AsBool() {
					return fmt.Errorf("%w: (newCommitIndex) >= ((commitIndex)[i])", distsys.ErrAssertionFailed)
				}
				return iface.Goto("AServerAdvanceCommitIndex.applyLoop")
				// no statements
			} else {
				return iface.Goto("AServerAdvanceCommitIndex.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAdvanceCommitIndex.applyLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			commitIndex2, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			srvId21 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			newCommitIndex1 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			log23, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			acctCh, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.acctCh")
			if err != nil {
				return err
			}
			var condition84 tla.TLAValue
			condition84, err = iface.Read(srvId21, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition85 tla.TLAValue
			condition85, err = iface.Read(commitIndex2, []tla.TLAValue{condition84})
			if err != nil {
				return err
			}
			var condition86 tla.TLAValue
			condition86, err = iface.Read(newCommitIndex1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition85, condition86).AsBool() {
				var exprRead44 tla.TLAValue
				exprRead44, err = iface.Read(srvId21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead45 tla.TLAValue
				exprRead45, err = iface.Read(commitIndex2, []tla.TLAValue{exprRead44})
				if err != nil {
					return err
				}
				var indexRead2 tla.TLAValue
				indexRead2, err = iface.Read(srvId21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(commitIndex2, []tla.TLAValue{indexRead2}, tla.TLA_PlusSymbol(exprRead45, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				var iRead1 tla.TLAValue
				iRead1, err = iface.Read(srvId21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i8 tla.TLAValue = iRead1
				_ = i8
				var kRead tla.TLAValue
				kRead, err = iface.Read(commitIndex2, []tla.TLAValue{i8})
				if err != nil {
					return err
				}
				var k0 tla.TLAValue = kRead
				_ = k0
				var entryRead1 tla.TLAValue
				entryRead1, err = iface.Read(log23, []tla.TLAValue{i8})
				if err != nil {
					return err
				}
				var entry0 tla.TLAValue = entryRead1.ApplyFunction(k0)
				_ = entry0
				var cmd tla.TLAValue = entry0.ApplyFunction(tla.MakeTLAString("cmd"))
				_ = cmd
				if iface.GetConstant("Debug")().AsBool() {
					tla.MakeTLATuple(tla.MakeTLAString("ServerAccept"), i8, cmd).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(acctCh, []tla.TLAValue{i8}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("mtype"), AcceptMessage(iface)},
					{tla.MakeTLAString("mcmd"), cmd},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AServerAdvanceCommitIndex.applyLoop")
				// no statements
			} else {
				return iface.Goto("AServerAdvanceCommitIndex.serverAdvanceCommitIndexLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerAdvanceCommitIndex.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerBecomeLeader.serverBecomeLeaderLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			becomeLeaderCh0, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.becomeLeaderCh")
			if err != nil {
				return err
			}
			srvId25 := iface.RequireArchetypeResource("AServerBecomeLeader.srvId")
			state16, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.state")
			if err != nil {
				return err
			}
			votesGranted3, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.votesGranted")
			if err != nil {
				return err
			}
			nextIndex7, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.nextIndex")
			if err != nil {
				return err
			}
			log24, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.log")
			if err != nil {
				return err
			}
			matchIndex4, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.matchIndex")
			if err != nil {
				return err
			}
			leader9, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.leader")
			if err != nil {
				return err
			}
			appendEntriesCh0, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.appendEntriesCh")
			if err != nil {
				return err
			}
			currentTerm32, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.currentTerm")
			if err != nil {
				return err
			}
			var condition87 tla.TLAValue
			condition87, err = iface.Read(srvId25, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition88 tla.TLAValue
			condition88, err = iface.Read(becomeLeaderCh0, []tla.TLAValue{condition87})
			if err != nil {
				return err
			}
			if condition88.AsBool() {
				var condition89 tla.TLAValue
				condition89, err = iface.Read(srvId25, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition90 tla.TLAValue
				condition90, err = iface.Read(state16, []tla.TLAValue{condition89})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition90, Candidate(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition91 tla.TLAValue
				condition91, err = iface.Read(srvId25, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition92 tla.TLAValue
				condition92, err = iface.Read(votesGranted3, []tla.TLAValue{condition91})
				if err != nil {
					return err
				}
				if !IsQuorum(iface, condition92).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead2 tla.TLAValue
				iRead2, err = iface.Read(srvId25, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i9 tla.TLAValue = iRead2
				_ = i9
				err = iface.Write(state16, []tla.TLAValue{i9}, Leader(iface))
				if err != nil {
					return err
				}
				var exprRead46 tla.TLAValue
				exprRead46, err = iface.Read(log24, []tla.TLAValue{i9})
				if err != nil {
					return err
				}
				err = iface.Write(nextIndex7, []tla.TLAValue{i9}, tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args []tla.TLAValue) tla.TLAValue {
					var j4 tla.TLAValue = args[0]
					_ = j4
					return tla.TLA_PlusSymbol(tla.TLA_Len(exprRead46), tla.MakeTLANumber(1))
				}))
				if err != nil {
					return err
				}
				err = iface.Write(matchIndex4, []tla.TLAValue{i9}, tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args0 []tla.TLAValue) tla.TLAValue {
					var j5 tla.TLAValue = args0[0]
					_ = j5
					return tla.MakeTLANumber(0)
				}))
				if err != nil {
					return err
				}
				err = iface.Write(leader9, []tla.TLAValue{i9}, i9)
				if err != nil {
					return err
				}
				err = iface.Write(appendEntriesCh0, []tla.TLAValue{}, tla.TLA_TRUE)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint8 tla.TLAValue
					toPrint8, err = iface.Read(currentTerm32, []tla.TLAValue{i9})
					if err != nil {
						return err
					}
					var toPrint9 tla.TLAValue
					toPrint9, err = iface.Read(state16, []tla.TLAValue{i9})
					if err != nil {
						return err
					}
					var toPrint10 tla.TLAValue
					toPrint10, err = iface.Read(leader9, []tla.TLAValue{i9})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("BecomeLeader"), i9, toPrint8, toPrint9, toPrint10).PCalPrint()
					return iface.Goto("AServerBecomeLeader.serverBecomeLeaderLoop")
				} else {
					return iface.Goto("AServerBecomeLeader.serverBecomeLeaderLoop")
				}
				// no statements
				// no statements
			} else {
				return iface.Goto("AServerBecomeLeader.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerBecomeLeader.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerFollowerAdvanceCommitIndex.serverFollowerAdvanceCommitIndexLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m60 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.m")
			fAdvCommitIdxCh0, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.fAdvCommitIdxCh")
			if err != nil {
				return err
			}
			srvId29 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.srvId")
			if tla.TLA_TRUE.AsBool() {
				var exprRead47 tla.TLAValue
				exprRead47, err = iface.Read(srvId29, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead48 tla.TLAValue
				exprRead48, err = iface.Read(fAdvCommitIdxCh0, []tla.TLAValue{exprRead47})
				if err != nil {
					return err
				}
				err = iface.Write(m60, []tla.TLAValue{}, exprRead48)
				if err != nil {
					return err
				}
				return iface.Goto("AServerFollowerAdvanceCommitIndex.acctLoop")
			} else {
				return iface.Goto("AServerFollowerAdvanceCommitIndex.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerFollowerAdvanceCommitIndex.acctLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			commitIndex6, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			srvId30 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.srvId")
			m61 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.m")
			log25, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			acctCh0, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.acctCh")
			if err != nil {
				return err
			}
			var condition93 tla.TLAValue
			condition93, err = iface.Read(srvId30, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition94 tla.TLAValue
			condition94, err = iface.Read(commitIndex6, []tla.TLAValue{condition93})
			if err != nil {
				return err
			}
			var condition95 tla.TLAValue
			condition95, err = iface.Read(m61, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition94, condition95.ApplyFunction(tla.MakeTLAString("mcommitIndex"))).AsBool() {
				var exprRead49 tla.TLAValue
				exprRead49, err = iface.Read(srvId30, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead50 tla.TLAValue
				exprRead50, err = iface.Read(commitIndex6, []tla.TLAValue{exprRead49})
				if err != nil {
					return err
				}
				var indexRead3 tla.TLAValue
				indexRead3, err = iface.Read(srvId30, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(commitIndex6, []tla.TLAValue{indexRead3}, tla.TLA_PlusSymbol(exprRead50, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				var iRead3 tla.TLAValue
				iRead3, err = iface.Read(srvId30, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i10 tla.TLAValue = iRead3
				_ = i10
				var kRead0 tla.TLAValue
				kRead0, err = iface.Read(commitIndex6, []tla.TLAValue{i10})
				if err != nil {
					return err
				}
				var k1 tla.TLAValue = kRead0
				_ = k1
				var entryRead2 tla.TLAValue
				entryRead2, err = iface.Read(log25, []tla.TLAValue{i10})
				if err != nil {
					return err
				}
				var entry1 tla.TLAValue = entryRead2.ApplyFunction(k1)
				_ = entry1
				var cmd0 tla.TLAValue = entry1.ApplyFunction(tla.MakeTLAString("cmd"))
				_ = cmd0
				if iface.GetConstant("Debug")().AsBool() {
					tla.MakeTLATuple(tla.MakeTLAString("ServerAccept"), i10, cmd0).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(acctCh0, []tla.TLAValue{i10}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("mtype"), AcceptMessage(iface)},
					{tla.MakeTLAString("mcmd"), cmd0},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AServerFollowerAdvanceCommitIndex.acctLoop")
				// no statements
			} else {
				return iface.Goto("AServerFollowerAdvanceCommitIndex.serverFollowerAdvanceCommitIndexLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerFollowerAdvanceCommitIndex.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerCrasher.serverCrash",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled, err := iface.RequireArchetypeResourceRef("AServerCrasher.netEnabled")
			if err != nil {
				return err
			}
			srvId34 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead4 tla.TLAValue
			indexRead4, err = iface.Read(srvId34, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(netEnabled, []tla.TLAValue{indexRead4}, tla.TLA_FALSE)
			if err != nil {
				return err
			}
			return iface.Goto("AServerCrasher.fdUpdate")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerCrasher.fdUpdate",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			fd5, err := iface.RequireArchetypeResourceRef("AServerCrasher.fd")
			if err != nil {
				return err
			}
			srvId35 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead5 tla.TLAValue
			indexRead5, err = iface.Read(srvId35, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(fd5, []tla.TLAValue{indexRead5}, tla.TLA_TRUE)
			if err != nil {
				return err
			}
			return iface.Goto("AServerCrasher.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerCrasher.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProposer.sndReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			propCh0, err := iface.RequireArchetypeResourceRef("AProposer.propCh")
			if err != nil {
				return err
			}
			err = iface.Write(propCh0, []tla.TLAValue{tla.MakeTLANumber(1)}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("mtype"), ProposeMessage(iface)},
				{tla.MakeTLAString("mcmd"), tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("data"), tla.MakeTLAString("hello")},
				})},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("AProposer.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProposer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AServer = distsys.MPCalArchetype{
	Name:              "AServer",
	Label:             "AServer.serverLoop",
	RequiredRefParams: []string{"AServer.net", "AServer.netLen", "AServer.netEnabled", "AServer.fd", "AServer.state", "AServer.currentTerm", "AServer.log", "AServer.plog", "AServer.commitIndex", "AServer.nextIndex", "AServer.matchIndex", "AServer.votedFor", "AServer.votesResponded", "AServer.votesGranted", "AServer.leader", "AServer.propCh", "AServer.acctCh", "AServer.leaderTimeout", "AServer.appendEntriesCh", "AServer.becomeLeaderCh", "AServer.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServer.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.idx", tla.MakeTLANumber(1))
		iface.EnsureArchetypeResourceLocal("AServer.m", tla.TLAValue{})
	},
}

var AServerRequestVote = distsys.MPCalArchetype{
	Name:              "AServerRequestVote",
	Label:             "AServerRequestVote.serverRequestVoteLoop",
	RequiredRefParams: []string{"AServerRequestVote.net", "AServerRequestVote.netLen", "AServerRequestVote.netEnabled", "AServerRequestVote.fd", "AServerRequestVote.state", "AServerRequestVote.currentTerm", "AServerRequestVote.log", "AServerRequestVote.plog", "AServerRequestVote.commitIndex", "AServerRequestVote.nextIndex", "AServerRequestVote.matchIndex", "AServerRequestVote.votedFor", "AServerRequestVote.votesResponded", "AServerRequestVote.votesGranted", "AServerRequestVote.leader", "AServerRequestVote.propCh", "AServerRequestVote.acctCh", "AServerRequestVote.leaderTimeout", "AServerRequestVote.appendEntriesCh", "AServerRequestVote.becomeLeaderCh", "AServerRequestVote.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerRequestVote.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerRequestVote.idx", tla.MakeTLANumber(1))
	},
}

var AServerAppendEntries = distsys.MPCalArchetype{
	Name:              "AServerAppendEntries",
	Label:             "AServerAppendEntries.serverAppendEntriesLoop",
	RequiredRefParams: []string{"AServerAppendEntries.net", "AServerAppendEntries.netLen", "AServerAppendEntries.netEnabled", "AServerAppendEntries.fd", "AServerAppendEntries.state", "AServerAppendEntries.currentTerm", "AServerAppendEntries.log", "AServerAppendEntries.plog", "AServerAppendEntries.commitIndex", "AServerAppendEntries.nextIndex", "AServerAppendEntries.matchIndex", "AServerAppendEntries.votedFor", "AServerAppendEntries.votesResponded", "AServerAppendEntries.votesGranted", "AServerAppendEntries.leader", "AServerAppendEntries.propCh", "AServerAppendEntries.acctCh", "AServerAppendEntries.leaderTimeout", "AServerAppendEntries.appendEntriesCh", "AServerAppendEntries.becomeLeaderCh", "AServerAppendEntries.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerAppendEntries.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerAppendEntries.idx", tla.TLAValue{})
	},
}

var AServerAdvanceCommitIndex = distsys.MPCalArchetype{
	Name:              "AServerAdvanceCommitIndex",
	Label:             "AServerAdvanceCommitIndex.serverAdvanceCommitIndexLoop",
	RequiredRefParams: []string{"AServerAdvanceCommitIndex.net", "AServerAdvanceCommitIndex.netLen", "AServerAdvanceCommitIndex.netEnabled", "AServerAdvanceCommitIndex.fd", "AServerAdvanceCommitIndex.state", "AServerAdvanceCommitIndex.currentTerm", "AServerAdvanceCommitIndex.log", "AServerAdvanceCommitIndex.plog", "AServerAdvanceCommitIndex.commitIndex", "AServerAdvanceCommitIndex.nextIndex", "AServerAdvanceCommitIndex.matchIndex", "AServerAdvanceCommitIndex.votedFor", "AServerAdvanceCommitIndex.votesResponded", "AServerAdvanceCommitIndex.votesGranted", "AServerAdvanceCommitIndex.leader", "AServerAdvanceCommitIndex.propCh", "AServerAdvanceCommitIndex.acctCh", "AServerAdvanceCommitIndex.leaderTimeout", "AServerAdvanceCommitIndex.appendEntriesCh", "AServerAdvanceCommitIndex.becomeLeaderCh", "AServerAdvanceCommitIndex.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerAdvanceCommitIndex.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerAdvanceCommitIndex.newCommitIndex", tla.MakeTLANumber(0))
	},
}

var AServerBecomeLeader = distsys.MPCalArchetype{
	Name:              "AServerBecomeLeader",
	Label:             "AServerBecomeLeader.serverBecomeLeaderLoop",
	RequiredRefParams: []string{"AServerBecomeLeader.net", "AServerBecomeLeader.netLen", "AServerBecomeLeader.netEnabled", "AServerBecomeLeader.fd", "AServerBecomeLeader.state", "AServerBecomeLeader.currentTerm", "AServerBecomeLeader.log", "AServerBecomeLeader.plog", "AServerBecomeLeader.commitIndex", "AServerBecomeLeader.nextIndex", "AServerBecomeLeader.matchIndex", "AServerBecomeLeader.votedFor", "AServerBecomeLeader.votesResponded", "AServerBecomeLeader.votesGranted", "AServerBecomeLeader.leader", "AServerBecomeLeader.propCh", "AServerBecomeLeader.acctCh", "AServerBecomeLeader.leaderTimeout", "AServerBecomeLeader.appendEntriesCh", "AServerBecomeLeader.becomeLeaderCh", "AServerBecomeLeader.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerBecomeLeader.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var AServerFollowerAdvanceCommitIndex = distsys.MPCalArchetype{
	Name:              "AServerFollowerAdvanceCommitIndex",
	Label:             "AServerFollowerAdvanceCommitIndex.serverFollowerAdvanceCommitIndexLoop",
	RequiredRefParams: []string{"AServerFollowerAdvanceCommitIndex.net", "AServerFollowerAdvanceCommitIndex.netLen", "AServerFollowerAdvanceCommitIndex.netEnabled", "AServerFollowerAdvanceCommitIndex.fd", "AServerFollowerAdvanceCommitIndex.state", "AServerFollowerAdvanceCommitIndex.currentTerm", "AServerFollowerAdvanceCommitIndex.log", "AServerFollowerAdvanceCommitIndex.plog", "AServerFollowerAdvanceCommitIndex.commitIndex", "AServerFollowerAdvanceCommitIndex.nextIndex", "AServerFollowerAdvanceCommitIndex.matchIndex", "AServerFollowerAdvanceCommitIndex.votedFor", "AServerFollowerAdvanceCommitIndex.votesResponded", "AServerFollowerAdvanceCommitIndex.votesGranted", "AServerFollowerAdvanceCommitIndex.leader", "AServerFollowerAdvanceCommitIndex.propCh", "AServerFollowerAdvanceCommitIndex.acctCh", "AServerFollowerAdvanceCommitIndex.leaderTimeout", "AServerFollowerAdvanceCommitIndex.appendEntriesCh", "AServerFollowerAdvanceCommitIndex.becomeLeaderCh", "AServerFollowerAdvanceCommitIndex.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerFollowerAdvanceCommitIndex.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerFollowerAdvanceCommitIndex.m", tla.TLAValue{})
	},
}

var AServerCrasher = distsys.MPCalArchetype{
	Name:              "AServerCrasher",
	Label:             "AServerCrasher.serverCrash",
	RequiredRefParams: []string{"AServerCrasher.netEnabled", "AServerCrasher.fd"},
	RequiredValParams: []string{"AServerCrasher.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var AProposer = distsys.MPCalArchetype{
	Name:              "AProposer",
	Label:             "AProposer.sndReq",
	RequiredRefParams: []string{"AProposer.propCh"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
