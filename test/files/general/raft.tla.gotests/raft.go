package raft

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

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
func ClientPutRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("cpq")
}
func Key1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key1")
}
func Value1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value1")
}
func Min(iface distsys.ArchetypeInterface, s tla.TLAValue) tla.TLAValue {
	return tla.TLAChoose(s, func(element tla.TLAValue) bool {
		var x tla.TLAValue = element
		_ = x
		return tla.TLAQuantifiedUniversal([]tla.TLAValue{s}, func(args []tla.TLAValue) bool {
			var y tla.TLAValue = args[0]
			_ = y
			return tla.TLA_LessThanOrEqualSymbol(x, y).AsBool()
		}).AsBool()
	})
}
func Max(iface distsys.ArchetypeInterface, s0 tla.TLAValue) tla.TLAValue {
	return tla.TLAChoose(s0, func(element0 tla.TLAValue) bool {
		var x0 tla.TLAValue = element0
		_ = x0
		return tla.TLAQuantifiedUniversal([]tla.TLAValue{s0}, func(args0 []tla.TLAValue) bool {
			var y0 tla.TLAValue = args0[0]
			_ = y0
			return tla.TLA_GreaterThanOrEqualSymbol(x0, y0).AsBool()
		}).AsBool()
	})
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
func Nil(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
}
func ServerSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumServers")())
}
func ClientSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NumServers")(), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(iface.GetConstant("NumServers")(), iface.GetConstant("NumClients")()))
}
func IsQuorum(iface distsys.ArchetypeInterface, s1 tla.TLAValue) tla.TLAValue {
	return tla.TLA_GreaterThanSymbol(tla.TLA_AsteriskSymbol(tla.TLA_Cardinality(s1), tla.MakeTLANumber(2)), iface.GetConstant("NumServers")())
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
			netEnabled, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			state := iface.RequireArchetypeResource("AServer.state")
			netLen, err := iface.RequireArchetypeResourceRef("AServer.netLen")
			if err != nil {
				return err
			}
			leader := iface.RequireArchetypeResource("AServer.leader")
			fd, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			currentTerm := iface.RequireArchetypeResource("AServer.currentTerm")
			votedFor := iface.RequireArchetypeResource("AServer.votedFor")
			votesResponded := iface.RequireArchetypeResource("AServer.votesResponded")
			votesGranted := iface.RequireArchetypeResource("AServer.votesGranted")
			idx := iface.RequireArchetypeResource("AServer.idx")
			log := iface.RequireArchetypeResource("AServer.log")
			matchIndex := iface.RequireArchetypeResource("AServer.matchIndex")
			commitIndex := iface.RequireArchetypeResource("AServer.commitIndex")
			nextIndex := iface.RequireArchetypeResource("AServer.nextIndex")
			if tla.TLA_TRUE.AsBool() {
				switch iface.NextFairnessCounter("AServer.serverLoop.1", 4) {
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
					if iface.GetConstant("ExploreFail")().AsBool() {
						switch iface.NextFairnessCounter("AServer.serverLoop.0", 2) {
						case 0:
							// skip
							return iface.Goto("AServer.handleMsg")
						case 1:
							err = iface.Write(netEnabled, []tla.TLAValue{iface.Self()}, tla.TLA_FALSE)
							if err != nil {
								return err
							}
							return iface.Goto("AServer.failLabel")
						default:
							panic("current branch of either matches no code paths!")
						}
						// no statements
					} else {
						return iface.Goto("AServer.handleMsg")
					}
					// no statements
				case 1:
					var condition0 tla.TLAValue
					condition0, err = iface.Read(state, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_InSymbol(condition0, tla.MakeTLASet(Follower(iface), Candidate(iface))).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var condition1 tla.TLAValue
					condition1, err = iface.Read(netLen, []tla.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					var condition2 tla.TLAValue
					condition2, err = iface.Read(leader, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition3 tla.TLAValue
					condition3, err = iface.Read(leader, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition4 tla.TLAValue
					condition4, err = iface.Read(leader, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition5 tla.TLAValue
					condition5, err = iface.Read(fd, []tla.TLAValue{condition4})
					if err != nil {
						return err
					}
					if !tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(condition1, tla.MakeTLANumber(0)), tla.TLA_LogicalOrSymbol(tla.TLA_EqualsSymbol(condition2, Nil(iface)), tla.TLA_LogicalAndSymbol(tla.TLA_NotEqualsSymbol(condition3, Nil(iface)), condition5))).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					err = iface.Write(state, []tla.TLAValue{}, Candidate(iface))
					if err != nil {
						return err
					}
					var exprRead0 tla.TLAValue
					exprRead0, err = iface.Read(currentTerm, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(currentTerm, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead0, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					err = iface.Write(votedFor, []tla.TLAValue{}, iface.Self())
					if err != nil {
						return err
					}
					err = iface.Write(votesResponded, []tla.TLAValue{}, tla.MakeTLASet(iface.Self()))
					if err != nil {
						return err
					}
					err = iface.Write(votesGranted, []tla.TLAValue{}, tla.MakeTLASet(iface.Self()))
					if err != nil {
						return err
					}
					err = iface.Write(idx, []tla.TLAValue{}, tla.MakeTLANumber(1))
					if err != nil {
						return err
					}
					return iface.Goto("AServer.requestVoteLoop")
				case 2:
					var condition6 tla.TLAValue
					condition6, err = iface.Read(state, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_EqualsSymbol(condition6, Leader(iface)).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					var agreeIndexesRead tla.TLAValue
					agreeIndexesRead, err = iface.Read(log, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var agreeIndexesRead0 tla.TLAValue
					agreeIndexesRead0, err = iface.Read(matchIndex, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var agreeIndexes tla.TLAValue = tla.TLASetRefinement(tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), tla.TLA_Len(agreeIndexesRead)), func(elem tla.TLAValue) bool {
						var index tla.TLAValue = elem
						_ = index
						return IsQuorum(iface, tla.TLA_UnionSymbol(tla.MakeTLASet(iface.Self()), tla.TLASetRefinement(ServerSet(iface), func(elem0 tla.TLAValue) bool {
							var k tla.TLAValue = elem0
							_ = k
							return tla.TLA_GreaterThanOrEqualSymbol(agreeIndexesRead0.ApplyFunction(k), index).AsBool()
						}))).AsBool()
					})
					_ = agreeIndexes
					var newCommitIndexRead tla.TLAValue
					newCommitIndexRead, err = iface.Read(log, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var newCommitIndexRead0 tla.TLAValue
					newCommitIndexRead0, err = iface.Read(currentTerm, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var newCommitIndexRead1 tla.TLAValue
					newCommitIndexRead1, err = iface.Read(commitIndex, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var newCommitIndex tla.TLAValue = func() tla.TLAValue {
						if tla.TLA_LogicalAndSymbol(tla.TLA_NotEqualsSymbol(agreeIndexes, tla.MakeTLASet()), tla.TLA_EqualsSymbol(newCommitIndexRead.ApplyFunction(Max(iface, agreeIndexes)).ApplyFunction(tla.MakeTLAString("term")), newCommitIndexRead0)).AsBool() {
							return Max(iface, agreeIndexes)
						} else {
							return newCommitIndexRead1
						}
					}()
					_ = newCommitIndex
					var condition7 tla.TLAValue
					condition7, err = iface.Read(commitIndex, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_GreaterThanOrEqualSymbol(newCommitIndex, condition7).AsBool() {
						return fmt.Errorf("%w: (newCommitIndex) >= (commitIndex)", distsys.ErrAssertionFailed)
					}
					err = iface.Write(commitIndex, []tla.TLAValue{}, newCommitIndex)
					if err != nil {
						return err
					}
					// no statements
					err = iface.Write(idx, []tla.TLAValue{}, tla.MakeTLANumber(1))
					if err != nil {
						return err
					}
					return iface.Goto("AServer.appendEntriesLoop")
				case 3:
					var condition8 tla.TLAValue
					condition8, err = iface.Read(state, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition9 tla.TLAValue
					condition9, err = iface.Read(votesGranted, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(condition8, Candidate(iface)), IsQuorum(iface, condition9)).AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					err = iface.Write(state, []tla.TLAValue{}, Leader(iface))
					if err != nil {
						return err
					}
					var exprRead1 tla.TLAValue
					exprRead1, err = iface.Read(log, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(nextIndex, []tla.TLAValue{}, tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args1 []tla.TLAValue) tla.TLAValue {
						var j tla.TLAValue = args1[0]
						_ = j
						return tla.TLA_PlusSymbol(tla.TLA_Len(exprRead1), tla.MakeTLANumber(1))
					}))
					if err != nil {
						return err
					}
					err = iface.Write(matchIndex, []tla.TLAValue{}, tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args2 []tla.TLAValue) tla.TLAValue {
						var j0 tla.TLAValue = args2[0]
						_ = j0
						return tla.MakeTLANumber(0)
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AServer.serverLoop")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				return iface.Goto("AServer.failLabel")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.handleMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m1 := iface.RequireArchetypeResource("AServer.m")
			currentTerm2 := iface.RequireArchetypeResource("AServer.currentTerm")
			state4 := iface.RequireArchetypeResource("AServer.state")
			votedFor0 := iface.RequireArchetypeResource("AServer.votedFor")
			log2 := iface.RequireArchetypeResource("AServer.log")
			net0, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			fd0, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			votesResponded0 := iface.RequireArchetypeResource("AServer.votesResponded")
			votesGranted1 := iface.RequireArchetypeResource("AServer.votesGranted")
			leader2 := iface.RequireArchetypeResource("AServer.leader")
			commitIndex2 := iface.RequireArchetypeResource("AServer.commitIndex")
			nextIndex0 := iface.RequireArchetypeResource("AServer.nextIndex")
			matchIndex1 := iface.RequireArchetypeResource("AServer.matchIndex")
			var condition10 tla.TLAValue
			condition10, err = iface.Read(m1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition10.ApplyFunction(tla.MakeTLAString("mtype")), RequestVoteRequest(iface)).AsBool() {
				var condition11 tla.TLAValue
				condition11, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition12 tla.TLAValue
				condition12, err = iface.Read(currentTerm2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_GreaterThanSymbol(condition11.ApplyFunction(tla.MakeTLAString("mterm")), condition12).AsBool() {
					var exprRead2 tla.TLAValue
					exprRead2, err = iface.Read(m1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(currentTerm2, []tla.TLAValue{}, exprRead2.ApplyFunction(tla.MakeTLAString("mterm")))
					if err != nil {
						return err
					}
					err = iface.Write(state4, []tla.TLAValue{}, Follower(iface))
					if err != nil {
						return err
					}
					err = iface.Write(votedFor0, []tla.TLAValue{}, Nil(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var i tla.TLAValue = iface.Self()
				_ = i
				var jRead tla.TLAValue
				jRead, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var j1 tla.TLAValue = jRead.ApplyFunction(tla.MakeTLAString("msource"))
				_ = j1
				var logOKRead tla.TLAValue
				logOKRead, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead0 tla.TLAValue
				logOKRead0, err = iface.Read(log2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead1 tla.TLAValue
				logOKRead1, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead2 tla.TLAValue
				logOKRead2, err = iface.Read(log2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead3 tla.TLAValue
				logOKRead3, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOKRead4 tla.TLAValue
				logOKRead4, err = iface.Read(log2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var logOK tla.TLAValue = tla.TLA_LogicalOrSymbol(tla.TLA_GreaterThanSymbol(logOKRead.ApplyFunction(tla.MakeTLAString("mlastLogTerm")), LastTerm(iface, logOKRead0)), tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(logOKRead1.ApplyFunction(tla.MakeTLAString("mlastLogTerm")), LastTerm(iface, logOKRead2)), tla.TLA_GreaterThanOrEqualSymbol(logOKRead3.ApplyFunction(tla.MakeTLAString("mlastLogIndex")), tla.TLA_Len(logOKRead4))))
				_ = logOK
				var grantRead tla.TLAValue
				grantRead, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var grantRead0 tla.TLAValue
				grantRead0, err = iface.Read(currentTerm2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var grantRead1 tla.TLAValue
				grantRead1, err = iface.Read(votedFor0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var grant tla.TLAValue = tla.TLA_LogicalAndSymbol(tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(grantRead.ApplyFunction(tla.MakeTLAString("mterm")), grantRead0), logOK), tla.TLA_InSymbol(grantRead1, tla.MakeTLASet(Nil(iface), j1)))
				_ = grant
				var condition13 tla.TLAValue
				condition13, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition14 tla.TLAValue
				condition14, err = iface.Read(currentTerm2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_LessThanOrEqualSymbol(condition13.ApplyFunction(tla.MakeTLAString("mterm")), condition14).AsBool() {
					return fmt.Errorf("%w: ((m).mterm) <= (currentTerm)", distsys.ErrAssertionFailed)
				}
				if grant.AsBool() {
					err = iface.Write(votedFor0, []tla.TLAValue{}, j1)
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				switch iface.NextFairnessCounter("AServer.handleMsg.0", 2) {
				case 0:
					var exprRead18 tla.TLAValue
					exprRead18, err = iface.Read(currentTerm2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.TLAValue{j1}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("mtype"), RequestVoteResponse(iface)},
						{tla.MakeTLAString("mterm"), exprRead18},
						{tla.MakeTLAString("mvoteGranted"), grant},
						{tla.MakeTLAString("msource"), i},
						{tla.MakeTLAString("mdest"), j1},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AServer.serverLoop")
				case 1:
					var condition61 tla.TLAValue
					condition61, err = iface.Read(fd0, []tla.TLAValue{j1})
					if err != nil {
						return err
					}
					if !condition61.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("AServer.serverLoop")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
				// no statements
			} else {
				var condition15 tla.TLAValue
				condition15, err = iface.Read(m1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition15.ApplyFunction(tla.MakeTLAString("mtype")), RequestVoteResponse(iface)).AsBool() {
					var condition16 tla.TLAValue
					condition16, err = iface.Read(m1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition17 tla.TLAValue
					condition17, err = iface.Read(currentTerm2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_GreaterThanSymbol(condition16.ApplyFunction(tla.MakeTLAString("mterm")), condition17).AsBool() {
						var exprRead3 tla.TLAValue
						exprRead3, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(currentTerm2, []tla.TLAValue{}, exprRead3.ApplyFunction(tla.MakeTLAString("mterm")))
						if err != nil {
							return err
						}
						err = iface.Write(state4, []tla.TLAValue{}, Follower(iface))
						if err != nil {
							return err
						}
						err = iface.Write(votedFor0, []tla.TLAValue{}, Nil(iface))
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					var condition18 tla.TLAValue
					condition18, err = iface.Read(m1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition19 tla.TLAValue
					condition19, err = iface.Read(currentTerm2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_LessThanSymbol(condition18.ApplyFunction(tla.MakeTLAString("mterm")), condition19).AsBool() {
						return iface.Goto("AServer.serverLoop")
					} else {
						var i0 tla.TLAValue = iface.Self()
						_ = i0
						var jRead0 tla.TLAValue
						jRead0, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var j2 tla.TLAValue = jRead0.ApplyFunction(tla.MakeTLAString("msource"))
						_ = j2
						var condition20 tla.TLAValue
						condition20, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition21 tla.TLAValue
						condition21, err = iface.Read(currentTerm2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if !tla.TLA_EqualsSymbol(condition20.ApplyFunction(tla.MakeTLAString("mterm")), condition21).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) = (currentTerm)", distsys.ErrAssertionFailed)
						}
						var exprRead4 tla.TLAValue
						exprRead4, err = iface.Read(votesResponded0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(votesResponded0, []tla.TLAValue{}, tla.TLA_UnionSymbol(exprRead4, tla.MakeTLASet(j2)))
						if err != nil {
							return err
						}
						var condition22 tla.TLAValue
						condition22, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if condition22.ApplyFunction(tla.MakeTLAString("mvoteGranted")).AsBool() {
							var exprRead5 tla.TLAValue
							exprRead5, err = iface.Read(votesGranted1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(votesGranted1, []tla.TLAValue{}, tla.TLA_UnionSymbol(exprRead5, tla.MakeTLASet(j2)))
							if err != nil {
								return err
							}
							return iface.Goto("AServer.serverLoop")
						} else {
							return iface.Goto("AServer.serverLoop")
						}
						// no statements
						// no statements
					}
					// no statements
				} else {
					var condition23 tla.TLAValue
					condition23, err = iface.Read(m1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_EqualsSymbol(condition23.ApplyFunction(tla.MakeTLAString("mtype")), AppendEntriesRequest(iface)).AsBool() {
						var condition24 tla.TLAValue
						condition24, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition25 tla.TLAValue
						condition25, err = iface.Read(currentTerm2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_GreaterThanSymbol(condition24.ApplyFunction(tla.MakeTLAString("mterm")), condition25).AsBool() {
							var exprRead6 tla.TLAValue
							exprRead6, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(currentTerm2, []tla.TLAValue{}, exprRead6.ApplyFunction(tla.MakeTLAString("mterm")))
							if err != nil {
								return err
							}
							err = iface.Write(state4, []tla.TLAValue{}, Follower(iface))
							if err != nil {
								return err
							}
							err = iface.Write(votedFor0, []tla.TLAValue{}, Nil(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var exprRead7 tla.TLAValue
						exprRead7, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(leader2, []tla.TLAValue{}, exprRead7.ApplyFunction(tla.MakeTLAString("msource")))
						if err != nil {
							return err
						}
						var i1 tla.TLAValue = iface.Self()
						_ = i1
						var jRead1 tla.TLAValue
						jRead1, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var j3 tla.TLAValue = jRead1.ApplyFunction(tla.MakeTLAString("msource"))
						_ = j3
						var logOKRead5 tla.TLAValue
						logOKRead5, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead6 tla.TLAValue
						logOKRead6, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead7 tla.TLAValue
						logOKRead7, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead8 tla.TLAValue
						logOKRead8, err = iface.Read(log2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead9 tla.TLAValue
						logOKRead9, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead10 tla.TLAValue
						logOKRead10, err = iface.Read(log2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOKRead11 tla.TLAValue
						logOKRead11, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var logOK0 tla.TLAValue = tla.TLA_LogicalOrSymbol(tla.TLA_EqualsSymbol(logOKRead5.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(0)), tla.TLA_LogicalAndSymbol(tla.TLA_LogicalAndSymbol(tla.TLA_GreaterThanSymbol(logOKRead6.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(0)), tla.TLA_LessThanOrEqualSymbol(logOKRead7.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.TLA_Len(logOKRead8))), tla.TLA_EqualsSymbol(logOKRead9.ApplyFunction(tla.MakeTLAString("mprevLogTerm")), logOKRead10.ApplyFunction(logOKRead11.ApplyFunction(tla.MakeTLAString("mprevLogIndex"))).ApplyFunction(tla.MakeTLAString("term")))))
						_ = logOK0
						var condition26 tla.TLAValue
						condition26, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition27 tla.TLAValue
						condition27, err = iface.Read(currentTerm2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if !tla.TLA_LessThanOrEqualSymbol(condition26.ApplyFunction(tla.MakeTLAString("mterm")), condition27).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) <= (currentTerm)", distsys.ErrAssertionFailed)
						}
						var condition28 tla.TLAValue
						condition28, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition29 tla.TLAValue
						condition29, err = iface.Read(currentTerm2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition30 tla.TLAValue
						condition30, err = iface.Read(state4, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(condition28.ApplyFunction(tla.MakeTLAString("mterm")), condition29), tla.TLA_EqualsSymbol(condition30, Candidate(iface))).AsBool() {
							err = iface.Write(state4, []tla.TLAValue{}, Follower(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition31 tla.TLAValue
						condition31, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition32 tla.TLAValue
						condition32, err = iface.Read(currentTerm2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition33 tla.TLAValue
						condition33, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition34 tla.TLAValue
						condition34, err = iface.Read(currentTerm2, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition35 tla.TLAValue
						condition35, err = iface.Read(state4, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_LogicalOrSymbol(tla.TLA_LessThanSymbol(condition31.ApplyFunction(tla.MakeTLAString("mterm")), condition32), tla.TLA_LogicalAndSymbol(tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(condition33.ApplyFunction(tla.MakeTLAString("mterm")), condition34), tla.TLA_EqualsSymbol(condition35, Follower(iface))), tla.TLA_LogicalNotSymbol(logOK0))).AsBool() {
							switch iface.NextFairnessCounter("AServer.handleMsg.1", 2) {
							case 0:
								var exprRead19 tla.TLAValue
								exprRead19, err = iface.Read(currentTerm2, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.TLAValue{j3}, tla.MakeTLARecord([]tla.TLARecordField{
									{tla.MakeTLAString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeTLAString("mterm"), exprRead19},
									{tla.MakeTLAString("msuccess"), tla.TLA_FALSE},
									{tla.MakeTLAString("mmatchIndex"), tla.MakeTLANumber(0)},
									{tla.MakeTLAString("msource"), i1},
									{tla.MakeTLAString("mdest"), j3},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServer.serverLoop")
							case 1:
								var condition62 tla.TLAValue
								condition62, err = iface.Read(fd0, []tla.TLAValue{j3})
								if err != nil {
									return err
								}
								if !condition62.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServer.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
						} else {
							var condition36 tla.TLAValue
							condition36, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition37 tla.TLAValue
							condition37, err = iface.Read(currentTerm2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition38 tla.TLAValue
							condition38, err = iface.Read(state4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if !tla.TLA_LogicalAndSymbol(tla.TLA_LogicalAndSymbol(tla.TLA_EqualsSymbol(condition36.ApplyFunction(tla.MakeTLAString("mterm")), condition37), tla.TLA_EqualsSymbol(condition38, Follower(iface))), logOK0).AsBool() {
								return fmt.Errorf("%w: ((((m).mterm) = (currentTerm)) /\\ ((state) = (Follower))) /\\ (logOK)", distsys.ErrAssertionFailed)
							}
							var indexRead tla.TLAValue
							indexRead, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var index0 tla.TLAValue = tla.TLA_PlusSymbol(indexRead.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(1))
							_ = index0
							var condition39 tla.TLAValue
							condition39, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition40 tla.TLAValue
							condition40, err = iface.Read(log2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition41 tla.TLAValue
							condition41, err = iface.Read(log2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition42 tla.TLAValue
							condition42, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_LogicalAndSymbol(tla.TLA_LogicalAndSymbol(tla.TLA_NotEqualsSymbol(condition39.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()), tla.TLA_GreaterThanOrEqualSymbol(tla.TLA_Len(condition40), index0)), tla.TLA_NotEqualsSymbol(condition41.ApplyFunction(index0).ApplyFunction(tla.MakeTLAString("term")), condition42.ApplyFunction(tla.MakeTLAString("mentries")).ApplyFunction(tla.MakeTLANumber(1)).ApplyFunction(tla.MakeTLAString("term")))).AsBool() {
								var exprRead8 tla.TLAValue
								exprRead8, err = iface.Read(log2, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var exprRead9 tla.TLAValue
								exprRead9, err = iface.Read(log2, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(log2, []tla.TLAValue{}, tla.MakeTLAFunction([]tla.TLAValue{tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), tla.TLA_MinusSymbol(tla.TLA_Len(exprRead8), tla.MakeTLANumber(1)))}, func(args3 []tla.TLAValue) tla.TLAValue {
									var k0 tla.TLAValue = args3[0]
									_ = k0
									return exprRead9.ApplyFunction(k0)
								}))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition43 tla.TLAValue
							condition43, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition44 tla.TLAValue
							condition44, err = iface.Read(log2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition45 tla.TLAValue
							condition45, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_LogicalAndSymbol(tla.TLA_NotEqualsSymbol(condition43.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()), tla.TLA_EqualsSymbol(tla.TLA_Len(condition44), condition45.ApplyFunction(tla.MakeTLAString("mprevLogIndex")))).AsBool() {
								var exprRead10 tla.TLAValue
								exprRead10, err = iface.Read(log2, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var exprRead11 tla.TLAValue
								exprRead11, err = iface.Read(m1, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(log2, []tla.TLAValue{}, tla.TLA_Append(exprRead10, exprRead11.ApplyFunction(tla.MakeTLAString("mentries")).ApplyFunction(tla.MakeTLANumber(1))))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition46 tla.TLAValue
							condition46, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition47 tla.TLAValue
							condition47, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition48 tla.TLAValue
							condition48, err = iface.Read(log2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition49 tla.TLAValue
							condition49, err = iface.Read(log2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition50 tla.TLAValue
							condition50, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_LogicalOrSymbol(tla.TLA_EqualsSymbol(condition46.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()), tla.TLA_LogicalAndSymbol(tla.TLA_LogicalAndSymbol(tla.TLA_NotEqualsSymbol(condition47.ApplyFunction(tla.MakeTLAString("mentries")), tla.MakeTLATuple()), tla.TLA_GreaterThanOrEqualSymbol(tla.TLA_Len(condition48), index0)), tla.TLA_EqualsSymbol(condition49.ApplyFunction(index0).ApplyFunction(tla.MakeTLAString("term")), condition50.ApplyFunction(tla.MakeTLAString("mentries")).ApplyFunction(tla.MakeTLANumber(1)).ApplyFunction(tla.MakeTLAString("term"))))).AsBool() {
								var exprRead12 tla.TLAValue
								exprRead12, err = iface.Read(m1, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(commitIndex2, []tla.TLAValue{}, exprRead12.ApplyFunction(tla.MakeTLAString("mcommitIndex")))
								if err != nil {
									return err
								}
								switch iface.NextFairnessCounter("AServer.handleMsg.2", 2) {
								case 0:
									var exprRead20 tla.TLAValue
									exprRead20, err = iface.Read(currentTerm2, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var exprRead21 tla.TLAValue
									exprRead21, err = iface.Read(m1, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var exprRead22 tla.TLAValue
									exprRead22, err = iface.Read(m1, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(net0, []tla.TLAValue{j3}, tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("mtype"), AppendEntriesResponse(iface)},
										{tla.MakeTLAString("mterm"), exprRead20},
										{tla.MakeTLAString("msuccess"), tla.TLA_TRUE},
										{tla.MakeTLAString("mmatchIndex"), tla.TLA_PlusSymbol(exprRead21.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.TLA_Len(exprRead22.ApplyFunction(tla.MakeTLAString("mentries"))))},
										{tla.MakeTLAString("msource"), i1},
										{tla.MakeTLAString("mdest"), j3},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
								case 1:
									var condition63 tla.TLAValue
									condition63, err = iface.Read(fd0, []tla.TLAValue{j3})
									if err != nil {
										return err
									}
									if !condition63.AsBool() {
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
						var condition51 tla.TLAValue
						condition51, err = iface.Read(m1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_EqualsSymbol(condition51.ApplyFunction(tla.MakeTLAString("mtype")), AppendEntriesResponse(iface)).AsBool() {
							var condition52 tla.TLAValue
							condition52, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition53 tla.TLAValue
							condition53, err = iface.Read(currentTerm2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_GreaterThanSymbol(condition52.ApplyFunction(tla.MakeTLAString("mterm")), condition53).AsBool() {
								var exprRead13 tla.TLAValue
								exprRead13, err = iface.Read(m1, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(currentTerm2, []tla.TLAValue{}, exprRead13.ApplyFunction(tla.MakeTLAString("mterm")))
								if err != nil {
									return err
								}
								err = iface.Write(state4, []tla.TLAValue{}, Follower(iface))
								if err != nil {
									return err
								}
								err = iface.Write(votedFor0, []tla.TLAValue{}, Nil(iface))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition54 tla.TLAValue
							condition54, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition55 tla.TLAValue
							condition55, err = iface.Read(currentTerm2, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_LessThanSymbol(condition54.ApplyFunction(tla.MakeTLAString("mterm")), condition55).AsBool() {
								return iface.Goto("AServer.serverLoop")
							} else {
								var i2 tla.TLAValue = iface.Self()
								_ = i2
								var jRead2 tla.TLAValue
								jRead2, err = iface.Read(m1, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var j4 tla.TLAValue = jRead2.ApplyFunction(tla.MakeTLAString("msource"))
								_ = j4
								var condition56 tla.TLAValue
								condition56, err = iface.Read(m1, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var condition57 tla.TLAValue
								condition57, err = iface.Read(currentTerm2, []tla.TLAValue{})
								if err != nil {
									return err
								}
								if !tla.TLA_EqualsSymbol(condition56.ApplyFunction(tla.MakeTLAString("mterm")), condition57).AsBool() {
									return fmt.Errorf("%w: ((m).mterm) = (currentTerm)", distsys.ErrAssertionFailed)
								}
								var condition58 tla.TLAValue
								condition58, err = iface.Read(m1, []tla.TLAValue{})
								if err != nil {
									return err
								}
								if condition58.ApplyFunction(tla.MakeTLAString("msuccess")).AsBool() {
									var exprRead14 tla.TLAValue
									exprRead14, err = iface.Read(m1, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex0, []tla.TLAValue{j4}, tla.TLA_PlusSymbol(exprRead14.ApplyFunction(tla.MakeTLAString("mmatchIndex")), tla.MakeTLANumber(1)))
									if err != nil {
										return err
									}
									var exprRead15 tla.TLAValue
									exprRead15, err = iface.Read(m1, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(matchIndex1, []tla.TLAValue{j4}, exprRead15.ApplyFunction(tla.MakeTLAString("mmatchIndex")))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
								} else {
									var exprRead16 tla.TLAValue
									exprRead16, err = iface.Read(nextIndex0, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex0, []tla.TLAValue{j4}, Max(iface, tla.MakeTLASet(tla.TLA_MinusSymbol(exprRead16.ApplyFunction(j4), tla.MakeTLANumber(1)), tla.MakeTLANumber(1))))
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
							var condition59 tla.TLAValue
							condition59, err = iface.Read(m1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.TLA_EqualsSymbol(condition59.ApplyFunction(tla.MakeTLAString("mtype")), ClientPutRequest(iface)).AsBool() {
								var condition60 tla.TLAValue
								condition60, err = iface.Read(state4, []tla.TLAValue{})
								if err != nil {
									return err
								}
								if tla.TLA_EqualsSymbol(condition60, Leader(iface)).AsBool() {
									var entryRead tla.TLAValue
									entryRead, err = iface.Read(currentTerm2, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entryRead0 tla.TLAValue
									entryRead0, err = iface.Read(m1, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entryRead1 tla.TLAValue
									entryRead1, err = iface.Read(m1, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entry tla.TLAValue = tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("term"), entryRead},
										{tla.MakeTLAString("key"), entryRead0.ApplyFunction(tla.MakeTLAString("mkey"))},
										{tla.MakeTLAString("value"), entryRead1.ApplyFunction(tla.MakeTLAString("mvalue"))},
									})
									_ = entry
									var exprRead17 tla.TLAValue
									exprRead17, err = iface.Read(log2, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(log2, []tla.TLAValue{}, tla.TLA_Append(exprRead17, entry))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
									// no statements
								} else {
									return iface.Goto("AServer.serverLoop")
								}
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
		Name: "AServer.requestVoteLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx1 := iface.RequireArchetypeResource("AServer.idx")
			net3, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			currentTerm25 := iface.RequireArchetypeResource("AServer.currentTerm")
			log19 := iface.RequireArchetypeResource("AServer.log")
			fd3, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			netEnabled0, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			var condition64 tla.TLAValue
			condition64, err = iface.Read(idx1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition64, iface.GetConstant("NumServers")()).AsBool() {
				var condition65 tla.TLAValue
				condition65, err = iface.Read(idx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition65, iface.Self()).AsBool() {
					switch iface.NextFairnessCounter("AServer.requestVoteLoop.0", 2) {
					case 0:
						var exprRead24 tla.TLAValue
						exprRead24, err = iface.Read(currentTerm25, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead25 tla.TLAValue
						exprRead25, err = iface.Read(log19, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead26 tla.TLAValue
						exprRead26, err = iface.Read(log19, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead27 tla.TLAValue
						exprRead27, err = iface.Read(idx1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead0 tla.TLAValue
						indexRead0, err = iface.Read(idx1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net3, []tla.TLAValue{indexRead0}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), RequestVoteRequest(iface)},
							{tla.MakeTLAString("mterm"), exprRead24},
							{tla.MakeTLAString("mlastLogTerm"), LastTerm(iface, exprRead25)},
							{tla.MakeTLAString("mlastLogIndex"), tla.TLA_Len(exprRead26)},
							{tla.MakeTLAString("msource"), iface.Self()},
							{tla.MakeTLAString("mdest"), exprRead27},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition66 tla.TLAValue
						condition66, err = iface.Read(idx1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition67 tla.TLAValue
						condition67, err = iface.Read(fd3, []tla.TLAValue{condition66})
						if err != nil {
							return err
						}
						if !condition67.AsBool() {
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
				var exprRead23 tla.TLAValue
				exprRead23, err = iface.Read(idx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx1, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead23, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				if iface.GetConstant("ExploreFail")().AsBool() {
					switch iface.NextFairnessCounter("AServer.requestVoteLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AServer.requestVoteLoop")
					case 1:
						err = iface.Write(netEnabled0, []tla.TLAValue{iface.Self()}, tla.TLA_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AServer.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AServer.requestVoteLoop")
				}
				// no statements
			} else {
				return iface.Goto("AServer.serverLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.appendEntriesLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			idx8 := iface.RequireArchetypeResource("AServer.idx")
			nextIndex3 := iface.RequireArchetypeResource("AServer.nextIndex")
			log21 := iface.RequireArchetypeResource("AServer.log")
			net4, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			currentTerm26 := iface.RequireArchetypeResource("AServer.currentTerm")
			commitIndex3 := iface.RequireArchetypeResource("AServer.commitIndex")
			fd4, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			netEnabled1, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			var condition68 tla.TLAValue
			condition68, err = iface.Read(idx8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition68, iface.GetConstant("NumServers")()).AsBool() {
				var condition69 tla.TLAValue
				condition69, err = iface.Read(idx8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition69, iface.Self()).AsBool() {
					var prevLogIndexRead tla.TLAValue
					prevLogIndexRead, err = iface.Read(nextIndex3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogIndexRead0 tla.TLAValue
					prevLogIndexRead0, err = iface.Read(idx8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogIndex tla.TLAValue = tla.TLA_MinusSymbol(prevLogIndexRead.ApplyFunction(prevLogIndexRead0), tla.MakeTLANumber(1))
					_ = prevLogIndex
					var prevLogTermRead tla.TLAValue
					prevLogTermRead, err = iface.Read(log21, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogTerm tla.TLAValue = func() tla.TLAValue {
						if tla.TLA_GreaterThanSymbol(prevLogIndex, tla.MakeTLANumber(0)).AsBool() {
							return prevLogTermRead.ApplyFunction(prevLogIndex).ApplyFunction(tla.MakeTLAString("term"))
						} else {
							return tla.MakeTLANumber(0)
						}
					}()
					_ = prevLogTerm
					var lastEntryRead tla.TLAValue
					lastEntryRead, err = iface.Read(log21, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var lastEntryRead0 tla.TLAValue
					lastEntryRead0, err = iface.Read(nextIndex3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var lastEntryRead1 tla.TLAValue
					lastEntryRead1, err = iface.Read(idx8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var lastEntry tla.TLAValue = Min(iface, tla.MakeTLASet(tla.TLA_Len(lastEntryRead), lastEntryRead0.ApplyFunction(lastEntryRead1)))
					_ = lastEntry
					var entriesRead tla.TLAValue
					entriesRead, err = iface.Read(log21, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entriesRead0 tla.TLAValue
					entriesRead0, err = iface.Read(nextIndex3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entriesRead1 tla.TLAValue
					entriesRead1, err = iface.Read(idx8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entries tla.TLAValue = tla.TLA_SubSeq(entriesRead, entriesRead0.ApplyFunction(entriesRead1), lastEntry)
					_ = entries
					switch iface.NextFairnessCounter("AServer.appendEntriesLoop.0", 2) {
					case 0:
						var exprRead29 tla.TLAValue
						exprRead29, err = iface.Read(currentTerm26, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead30 tla.TLAValue
						exprRead30, err = iface.Read(commitIndex3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead31 tla.TLAValue
						exprRead31, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead1 tla.TLAValue
						indexRead1, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net4, []tla.TLAValue{indexRead1}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), AppendEntriesRequest(iface)},
							{tla.MakeTLAString("mterm"), exprRead29},
							{tla.MakeTLAString("mprevLogIndex"), prevLogIndex},
							{tla.MakeTLAString("mprevLogTerm"), prevLogTerm},
							{tla.MakeTLAString("mentries"), entries},
							{tla.MakeTLAString("mcommitIndex"), Min(iface, tla.MakeTLASet(exprRead30, lastEntry))},
							{tla.MakeTLAString("msource"), iface.Self()},
							{tla.MakeTLAString("mdest"), exprRead31},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition70 tla.TLAValue
						condition70, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition71 tla.TLAValue
						condition71, err = iface.Read(fd4, []tla.TLAValue{condition70})
						if err != nil {
							return err
						}
						if !condition71.AsBool() {
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
				var exprRead28 tla.TLAValue
				exprRead28, err = iface.Read(idx8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx8, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead28, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				if iface.GetConstant("ExploreFail")().AsBool() {
					switch iface.NextFairnessCounter("AServer.appendEntriesLoop.1", 2) {
					case 0:
						// skip
						return iface.Goto("AServer.appendEntriesLoop")
					case 1:
						err = iface.Write(netEnabled1, []tla.TLAValue{iface.Self()}, tla.TLA_FALSE)
						if err != nil {
							return err
						}
						return iface.Goto("AServer.failLabel")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AServer.appendEntriesLoop")
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
			fd5, err := iface.RequireArchetypeResourceRef("AServer.fd")
			if err != nil {
				return err
			}
			err = iface.Write(fd5, []tla.TLAValue{iface.Self()}, tla.TLA_TRUE)
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
		Name: "AClient.sndPutReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net5, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			var srv tla.TLAValue = tla.MakeTLANumber(1)
			_ = srv
			err = iface.Write(net5, []tla.TLAValue{srv}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("mtype"), ClientPutRequest(iface)},
				{tla.MakeTLAString("mkey"), Key1(iface)},
				{tla.MakeTLAString("mvalue"), Value1(iface)},
				{tla.MakeTLAString("msource"), iface.Self()},
				{tla.MakeTLAString("mdest"), srv},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("AClient.clientBlock")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.clientBlock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if !tla.TLA_FALSE.AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			return iface.Goto("AClient.Done")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AServer = distsys.MPCalArchetype{
	Name:              "AServer",
	Label:             "AServer.serverLoop",
	RequiredRefParams: []string{"AServer.net", "AServer.fd", "AServer.netLen", "AServer.netEnabled"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.currentTerm", tla.MakeTLANumber(1))
		iface.EnsureArchetypeResourceLocal("AServer.state", Follower(iface))
		iface.EnsureArchetypeResourceLocal("AServer.votedFor", Nil(iface))
		iface.EnsureArchetypeResourceLocal("AServer.log", tla.MakeTLATuple())
		iface.EnsureArchetypeResourceLocal("AServer.commitIndex", tla.MakeTLANumber(0))
		iface.EnsureArchetypeResourceLocal("AServer.nextIndex", tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args4 []tla.TLAValue) tla.TLAValue {
			var i3 tla.TLAValue = args4[0]
			_ = i3
			return tla.MakeTLANumber(1)
		}))
		iface.EnsureArchetypeResourceLocal("AServer.matchIndex", tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args5 []tla.TLAValue) tla.TLAValue {
			var i4 tla.TLAValue = args5[0]
			_ = i4
			return tla.MakeTLANumber(0)
		}))
		iface.EnsureArchetypeResourceLocal("AServer.votesResponded", tla.MakeTLASet())
		iface.EnsureArchetypeResourceLocal("AServer.votesGranted", tla.MakeTLASet())
		iface.EnsureArchetypeResourceLocal("AServer.leader", Nil(iface))
		iface.EnsureArchetypeResourceLocal("AServer.idx", tla.MakeTLANumber(1))
		iface.EnsureArchetypeResourceLocal("AServer.m", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.sndPutReq",
	RequiredRefParams: []string{"AClient.net"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
