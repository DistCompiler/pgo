package raft

import (
	"fmt"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func Nil(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func Min(iface distsys.ArchetypeInterface, s tla.Value) tla.Value {
	return func() tla.Value {
		var e tla.Value = tla.Choose(s, func(element tla.Value) bool {
			var e0 tla.Value = element
			_ = e0
			return tla.ModuleTRUE.AsBool()
		})
		_ = e
		return MinAcc(iface, tla.ModuleBackslashSymbol(s, tla.MakeSet(e)), e)
	}()
}
func MinAcc(iface distsys.ArchetypeInterface, s0 tla.Value, e1 tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleEqualsSymbol(s0, tla.MakeSet()).AsBool() {
			return e1
		} else {
			return func() tla.Value {
				var e2 tla.Value = tla.Choose(s0, func(element0 tla.Value) bool {
					var e20 tla.Value = element0
					_ = e20
					return tla.ModuleTRUE.AsBool()
				})
				_ = e2
				return MinAcc(iface, tla.ModuleBackslashSymbol(s0, tla.MakeSet(e2)), func() tla.Value {
					if tla.ModuleLessThanSymbol(e2, e1).AsBool() {
						return e2
					} else {
						return e1
					}
				}())
			}()
		}
	}()
}
func Max(iface distsys.ArchetypeInterface, s1 tla.Value) tla.Value {
	return func() tla.Value {
		var e3 tla.Value = tla.Choose(s1, func(element1 tla.Value) bool {
			var e4 tla.Value = element1
			_ = e4
			return tla.ModuleTRUE.AsBool()
		})
		_ = e3
		return MaxAcc(iface, tla.ModuleBackslashSymbol(s1, tla.MakeSet(e3)), e3)
	}()
}
func MaxAcc(iface distsys.ArchetypeInterface, s2 tla.Value, e10 tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleEqualsSymbol(s2, tla.MakeSet()).AsBool() {
			return e10
		} else {
			return func() tla.Value {
				var e21 tla.Value = tla.Choose(s2, func(element2 tla.Value) bool {
					var e22 tla.Value = element2
					_ = e22
					return tla.ModuleTRUE.AsBool()
				})
				_ = e21
				return MaxAcc(iface, tla.ModuleBackslashSymbol(s2, tla.MakeSet(e21)), func() tla.Value {
					if tla.ModuleGreaterThanSymbol(e21, e10).AsBool() {
						return e21
					} else {
						return e10
					}
				}())
			}()
		}
	}()
}
func IsQuorum(iface distsys.ArchetypeInterface, s3 tla.Value) tla.Value {
	return tla.ModuleGreaterThanSymbol(tla.ModuleAsteriskSymbol(tla.ModuleCardinality(s3), tla.MakeNumber(2)), iface.GetConstant("NumServers")())
}
func ServerSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NumServers")())
}
func FindMaxAgreeIndex(iface distsys.ArchetypeInterface, logLocal tla.Value, i tla.Value, matchIndex tla.Value) tla.Value {
	return FindMaxAgreeIndexRec(iface, logLocal, i, matchIndex, tla.ModuleLen(logLocal))
}
func FindMaxAgreeIndexRec(iface distsys.ArchetypeInterface, logLocal0 tla.Value, i0 tla.Value, matchIndex0 tla.Value, index tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleEqualsSymbol(index, tla.MakeNumber(0)).AsBool() {
			return Nil(iface)
		} else {
			return func() tla.Value {
				if IsQuorum(iface, tla.ModuleUnionSymbol(tla.MakeSet(i0), tla.SetRefinement(ServerSet(iface), func(elem tla.Value) bool {
					var k tla.Value = elem
					_ = k
					return tla.ModuleGreaterThanOrEqualSymbol(matchIndex0.ApplyFunction(k), index).AsBool()
				}))).AsBool() {
					return index
				} else {
					return FindMaxAgreeIndexRec(iface, logLocal0, i0, matchIndex0, tla.ModuleMinusSymbol(index, tla.MakeNumber(1)))
				}
			}()
		}
	}()
}
func Follower(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("follower")
}
func Candidate(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("candidate")
}
func Leader(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("leader")
}
func RequestVoteRequest(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("rvq")
}
func RequestVoteResponse(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("rvp")
}
func AppendEntriesRequest(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("apq")
}
func AppendEntriesResponse(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("app")
}
func ProposeMessage(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("prm")
}
func AcceptMessage(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("acm")
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
func LastTerm(iface distsys.ArchetypeInterface, xlog tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleEqualsSymbol(tla.ModuleLen(xlog), tla.MakeNumber(0)).AsBool() {
			return tla.MakeNumber(0)
		} else {
			return xlog.ApplyFunction(tla.ModuleLen(xlog)).ApplyFunction(tla.MakeString("term"))
		}
	}()
}
func ServerNetListenerSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(0), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(1), iface.GetConstant("NumServers")()))
}
func ServerPropChListenerSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(1), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(2), iface.GetConstant("NumServers")()))
}
func ServerRequestVoteSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(2), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(3), iface.GetConstant("NumServers")()))
}
func ServerAppendEntriesSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(3), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(4), iface.GetConstant("NumServers")()))
}
func ServerAdvanceCommitIndexSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(4), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(5), iface.GetConstant("NumServers")()))
}
func ServerBecomeLeaderSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(5), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(6), iface.GetConstant("NumServers")()))
}
func ServerFollowerAdvanceCommitIndexSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(6), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(7), iface.GetConstant("NumServers")()))
}
func ServerCrasherSet(iface distsys.ArchetypeInterface) tla.Value {
	return func() tla.Value {
		if iface.GetConstant("ExploreFail")().AsBool() {
			return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(7), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(7), iface.GetConstant("NumServers")()), iface.GetConstant("MaxNodeFail")()))
		} else {
			return tla.MakeSet()
		}
	}()
}
func NodeSet(iface distsys.ArchetypeInterface) tla.Value {
	return ServerSet(iface)
}
func KeySet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet()
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServerNetListener.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled, err := iface.RequireArchetypeResourceRef("AServerNetListener.netEnabled")
			if err != nil {
				return err
			}
			srvId := iface.RequireArchetypeResource("AServerNetListener.srvId")
			m := iface.RequireArchetypeResource("AServerNetListener.m")
			net, err := iface.RequireArchetypeResourceRef("AServerNetListener.net")
			if err != nil {
				return err
			}
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition tla.Value
					condition, err = iface.Read(srvId, nil)
					if err != nil {
						return err
					}
					var condition0 tla.Value
					condition0, err = iface.Read(netEnabled, []tla.Value{condition})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition0).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead tla.Value
				exprRead, err = iface.Read(net, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(m, nil, exprRead)
				if err != nil {
					return err
				}
				var condition1 tla.Value
				condition1, err = iface.Read(m, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition1.ApplyFunction(tla.MakeString("mdest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((m).mdest) = (self)", distsys.ErrAssertionFailed)
				}
				return iface.Goto("AServerNetListener.handleMsg")
			} else {
				return iface.Goto("AServerNetListener.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerNetListener.handleMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled0, err := iface.RequireArchetypeResourceRef("AServerNetListener.netEnabled")
			if err != nil {
				return err
			}
			srvId0 := iface.RequireArchetypeResource("AServerNetListener.srvId")
			m1 := iface.RequireArchetypeResource("AServerNetListener.m")
			currentTerm, err := iface.RequireArchetypeResourceRef("AServerNetListener.currentTerm")
			if err != nil {
				return err
			}
			state, err := iface.RequireArchetypeResourceRef("AServerNetListener.state")
			if err != nil {
				return err
			}
			votedFor, err := iface.RequireArchetypeResourceRef("AServerNetListener.votedFor")
			if err != nil {
				return err
			}
			leader, err := iface.RequireArchetypeResourceRef("AServerNetListener.leader")
			if err != nil {
				return err
			}
			log, err := iface.RequireArchetypeResourceRef("AServerNetListener.log")
			if err != nil {
				return err
			}
			net0, err := iface.RequireArchetypeResourceRef("AServerNetListener.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AServerNetListener.fd")
			if err != nil {
				return err
			}
			votesResponded, err := iface.RequireArchetypeResourceRef("AServerNetListener.votesResponded")
			if err != nil {
				return err
			}
			votesGranted, err := iface.RequireArchetypeResourceRef("AServerNetListener.votesGranted")
			if err != nil {
				return err
			}
			becomeLeaderCh, err := iface.RequireArchetypeResourceRef("AServerNetListener.becomeLeaderCh")
			if err != nil {
				return err
			}
			leaderTimeout, err := iface.RequireArchetypeResourceRef("AServerNetListener.leaderTimeout")
			if err != nil {
				return err
			}
			plog, err := iface.RequireArchetypeResourceRef("AServerNetListener.plog")
			if err != nil {
				return err
			}
			fAdvCommitIdxCh, err := iface.RequireArchetypeResourceRef("AServerNetListener.fAdvCommitIdxCh")
			if err != nil {
				return err
			}
			nextIndex, err := iface.RequireArchetypeResourceRef("AServerNetListener.nextIndex")
			if err != nil {
				return err
			}
			matchIndex1, err := iface.RequireArchetypeResourceRef("AServerNetListener.matchIndex")
			if err != nil {
				return err
			}
			appendEntriesCh, err := iface.RequireArchetypeResourceRef("AServerNetListener.appendEntriesCh")
			if err != nil {
				return err
			}
			if iface.GetConstant("ExploreFail")().AsBool() {
				var condition2 tla.Value
				condition2, err = iface.Read(srvId0, nil)
				if err != nil {
					return err
				}
				var condition3 tla.Value
				condition3, err = iface.Read(netEnabled0, []tla.Value{condition2})
				if err != nil {
					return err
				}
				if tla.ModuleLogicalNotSymbol(condition3).AsBool() {
					if !tla.ModuleFALSE.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					// no statements
				} else {
					// no statements
				}
				// no statements
			} else {
				// no statements
			}
			var condition4 tla.Value
			condition4, err = iface.Read(m1, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition4.ApplyFunction(tla.MakeString("mtype")), RequestVoteRequest(iface)).AsBool() {
				var condition5 tla.Value
				condition5, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var condition6 tla.Value
				condition6, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				if tla.ModuleGreaterThanSymbol(condition5.ApplyFunction(tla.MakeString("mterm")), condition6).AsBool() {
					var exprRead0 tla.Value
					exprRead0, err = iface.Read(m1, nil)
					if err != nil {
						return err
					}
					err = iface.Write(currentTerm, []tla.Value{iface.Self()}, exprRead0.ApplyFunction(tla.MakeString("mterm")))
					if err != nil {
						return err
					}
					err = iface.Write(state, []tla.Value{iface.Self()}, Follower(iface))
					if err != nil {
						return err
					}
					err = iface.Write(votedFor, []tla.Value{iface.Self()}, Nil(iface))
					if err != nil {
						return err
					}
					err = iface.Write(leader, []tla.Value{iface.Self()}, Nil(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var i1 tla.Value = iface.Self()
				_ = i1
				var jRead tla.Value
				jRead, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var j tla.Value = jRead.ApplyFunction(tla.MakeString("msource"))
				_ = j
				var logOKRead tla.Value
				logOKRead, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var logOKRead0 tla.Value
				logOKRead0, err = iface.Read(log, []tla.Value{i1})
				if err != nil {
					return err
				}
				var logOKRead1 tla.Value
				logOKRead1, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var logOKRead2 tla.Value
				logOKRead2, err = iface.Read(log, []tla.Value{i1})
				if err != nil {
					return err
				}
				var logOKRead3 tla.Value
				logOKRead3, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var logOKRead4 tla.Value
				logOKRead4, err = iface.Read(log, []tla.Value{i1})
				if err != nil {
					return err
				}
				var logOK tla.Value = tla.MakeBool(tla.ModuleGreaterThanSymbol(logOKRead.ApplyFunction(tla.MakeString("mlastLogTerm")), LastTerm(iface, logOKRead0)).AsBool() || tla.MakeBool(tla.ModuleEqualsSymbol(logOKRead1.ApplyFunction(tla.MakeString("mlastLogTerm")), LastTerm(iface, logOKRead2)).AsBool() && tla.ModuleGreaterThanOrEqualSymbol(logOKRead3.ApplyFunction(tla.MakeString("mlastLogIndex")), tla.ModuleLen(logOKRead4)).AsBool()).AsBool())
				_ = logOK
				var grantRead tla.Value
				grantRead, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var grantRead0 tla.Value
				grantRead0, err = iface.Read(currentTerm, []tla.Value{i1})
				if err != nil {
					return err
				}
				var grantRead1 tla.Value
				grantRead1, err = iface.Read(votedFor, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				var grant tla.Value = tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(grantRead.ApplyFunction(tla.MakeString("mterm")), grantRead0).AsBool() && logOK.AsBool()).AsBool() && tla.ModuleInSymbol(grantRead1, tla.MakeSet(Nil(iface), j)).AsBool())
				_ = grant
				var condition7 tla.Value
				condition7, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var condition8 tla.Value
				condition8, err = iface.Read(currentTerm, []tla.Value{i1})
				if err != nil {
					return err
				}
				if !tla.ModuleLessThanOrEqualSymbol(condition7.ApplyFunction(tla.MakeString("mterm")), condition8).AsBool() {
					return fmt.Errorf("%w: ((m).mterm) <= ((currentTerm)[i])", distsys.ErrAssertionFailed)
				}
				if grant.AsBool() {
					err = iface.Write(votedFor, []tla.Value{i1}, j)
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				switch iface.NextFairnessCounter("AServerNetListener.handleMsg.0", 2) {
				case 0:
					var exprRead22 tla.Value
					exprRead22, err = iface.Read(currentTerm, []tla.Value{i1})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.Value{j}, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("mtype"), RequestVoteResponse(iface)},
						{tla.MakeString("mterm"), exprRead22},
						{tla.MakeString("mvoteGranted"), grant},
						{tla.MakeString("msource"), i1},
						{tla.MakeString("mdest"), j},
					}))
					if err != nil {
						return err
					}
					// no statements
				case 1:
					var condition50 tla.Value
					condition50, err = iface.Read(fd, []tla.Value{j})
					if err != nil {
						return err
					}
					if !condition50.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					// no statements
				default:
					panic("current branch of either matches no code paths!")
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint tla.Value
					toPrint, err = iface.Read(currentTerm, []tla.Value{i1})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("HandleRequestVoteRequest"), i1, j, toPrint, grant).PCalPrint()
					return iface.Goto("AServerNetListener.serverLoop")
				} else {
					return iface.Goto("AServerNetListener.serverLoop")
				}
				// no statements
				// no statements
			} else {
				var condition9 tla.Value
				condition9, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition9.ApplyFunction(tla.MakeString("mtype")), RequestVoteResponse(iface)).AsBool() {
					var condition10 tla.Value
					condition10, err = iface.Read(m1, nil)
					if err != nil {
						return err
					}
					var condition11 tla.Value
					condition11, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
					if err != nil {
						return err
					}
					if tla.ModuleGreaterThanSymbol(condition10.ApplyFunction(tla.MakeString("mterm")), condition11).AsBool() {
						var exprRead1 tla.Value
						exprRead1, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						err = iface.Write(currentTerm, []tla.Value{iface.Self()}, exprRead1.ApplyFunction(tla.MakeString("mterm")))
						if err != nil {
							return err
						}
						err = iface.Write(state, []tla.Value{iface.Self()}, Follower(iface))
						if err != nil {
							return err
						}
						err = iface.Write(votedFor, []tla.Value{iface.Self()}, Nil(iface))
						if err != nil {
							return err
						}
						err = iface.Write(leader, []tla.Value{iface.Self()}, Nil(iface))
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					var condition12 tla.Value
					condition12, err = iface.Read(m1, nil)
					if err != nil {
						return err
					}
					var condition13 tla.Value
					condition13, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
					if err != nil {
						return err
					}
					if tla.ModuleLessThanSymbol(condition12.ApplyFunction(tla.MakeString("mterm")), condition13).AsBool() {
						// skip
						return iface.Goto("AServerNetListener.serverLoop")
					} else {
						var i2 tla.Value = iface.Self()
						_ = i2
						var jRead0 tla.Value
						jRead0, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var j0 tla.Value = jRead0.ApplyFunction(tla.MakeString("msource"))
						_ = j0
						var condition14 tla.Value
						condition14, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition15 tla.Value
						condition15, err = iface.Read(currentTerm, []tla.Value{i2})
						if err != nil {
							return err
						}
						if !tla.ModuleEqualsSymbol(condition14.ApplyFunction(tla.MakeString("mterm")), condition15).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
						var exprRead2 tla.Value
						exprRead2, err = iface.Read(votesResponded, []tla.Value{i2})
						if err != nil {
							return err
						}
						err = iface.Write(votesResponded, []tla.Value{i2}, tla.ModuleUnionSymbol(exprRead2, tla.MakeSet(j0)))
						if err != nil {
							return err
						}
						var condition16 tla.Value
						condition16, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						if condition16.ApplyFunction(tla.MakeString("mvoteGranted")).AsBool() {
							var exprRead3 tla.Value
							exprRead3, err = iface.Read(votesGranted, []tla.Value{i2})
							if err != nil {
								return err
							}
							err = iface.Write(votesGranted, []tla.Value{i2}, tla.ModuleUnionSymbol(exprRead3, tla.MakeSet(j0)))
							if err != nil {
								return err
							}
							var condition17 tla.Value
							condition17, err = iface.Read(state, []tla.Value{i2})
							if err != nil {
								return err
							}
							var condition18 tla.Value
							condition18, err = iface.Read(votesGranted, []tla.Value{i2})
							if err != nil {
								return err
							}
							if tla.MakeBool(tla.ModuleEqualsSymbol(condition17, Candidate(iface)).AsBool() && IsQuorum(iface, condition18).AsBool()).AsBool() {
								err = iface.Write(becomeLeaderCh, []tla.Value{i2}, tla.ModuleTRUE)
								if err != nil {
									return err
								}
								return iface.Goto("AServerNetListener.serverLoop")
							} else {
								return iface.Goto("AServerNetListener.serverLoop")
							}
							// no statements
						} else {
							return iface.Goto("AServerNetListener.serverLoop")
						}
						// no statements
						// no statements
					}
					// no statements
				} else {
					var condition19 tla.Value
					condition19, err = iface.Read(m1, nil)
					if err != nil {
						return err
					}
					if tla.ModuleEqualsSymbol(condition19.ApplyFunction(tla.MakeString("mtype")), AppendEntriesRequest(iface)).AsBool() {
						var condition20 tla.Value
						condition20, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition21 tla.Value
						condition21, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
						if err != nil {
							return err
						}
						if tla.ModuleGreaterThanSymbol(condition20.ApplyFunction(tla.MakeString("mterm")), condition21).AsBool() {
							var exprRead4 tla.Value
							exprRead4, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(currentTerm, []tla.Value{iface.Self()}, exprRead4.ApplyFunction(tla.MakeString("mterm")))
							if err != nil {
								return err
							}
							err = iface.Write(state, []tla.Value{iface.Self()}, Follower(iface))
							if err != nil {
								return err
							}
							err = iface.Write(votedFor, []tla.Value{iface.Self()}, Nil(iface))
							if err != nil {
								return err
							}
							err = iface.Write(leader, []tla.Value{iface.Self()}, Nil(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var i3 tla.Value = iface.Self()
						_ = i3
						var jRead1 tla.Value
						jRead1, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var j1 tla.Value = jRead1.ApplyFunction(tla.MakeString("msource"))
						_ = j1
						var logOKRead5 tla.Value
						logOKRead5, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var logOKRead6 tla.Value
						logOKRead6, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var logOKRead7 tla.Value
						logOKRead7, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var logOKRead8 tla.Value
						logOKRead8, err = iface.Read(log, []tla.Value{i3})
						if err != nil {
							return err
						}
						var logOKRead9 tla.Value
						logOKRead9, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var logOKRead10 tla.Value
						logOKRead10, err = iface.Read(log, []tla.Value{i3})
						if err != nil {
							return err
						}
						var logOKRead11 tla.Value
						logOKRead11, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var logOK0 tla.Value = tla.MakeBool(tla.ModuleEqualsSymbol(logOKRead5.ApplyFunction(tla.MakeString("mprevLogIndex")), tla.MakeNumber(0)).AsBool() || tla.MakeBool(tla.MakeBool(tla.ModuleGreaterThanSymbol(logOKRead6.ApplyFunction(tla.MakeString("mprevLogIndex")), tla.MakeNumber(0)).AsBool() && tla.ModuleLessThanOrEqualSymbol(logOKRead7.ApplyFunction(tla.MakeString("mprevLogIndex")), tla.ModuleLen(logOKRead8)).AsBool()).AsBool() && tla.ModuleEqualsSymbol(logOKRead9.ApplyFunction(tla.MakeString("mprevLogTerm")), logOKRead10.ApplyFunction(logOKRead11.ApplyFunction(tla.MakeString("mprevLogIndex"))).ApplyFunction(tla.MakeString("term"))).AsBool()).AsBool())
						_ = logOK0
						var condition22 tla.Value
						condition22, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition23 tla.Value
						condition23, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
						}
						if !tla.ModuleLessThanOrEqualSymbol(condition22.ApplyFunction(tla.MakeString("mterm")), condition23).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) <= ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
						var condition24 tla.Value
						condition24, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition25 tla.Value
						condition25, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
						}
						if tla.ModuleEqualsSymbol(condition24.ApplyFunction(tla.MakeString("mterm")), condition25).AsBool() {
							var exprRead5 tla.Value
							exprRead5, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(leader, []tla.Value{i3}, exprRead5.ApplyFunction(tla.MakeString("msource")))
							if err != nil {
								return err
							}
							err = iface.Write(leaderTimeout, nil, iface.GetConstant("LeaderTimeoutReset")())
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition26 tla.Value
						condition26, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition27 tla.Value
						condition27, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
						}
						var condition28 tla.Value
						condition28, err = iface.Read(state, []tla.Value{i3})
						if err != nil {
							return err
						}
						if tla.MakeBool(tla.ModuleEqualsSymbol(condition26.ApplyFunction(tla.MakeString("mterm")), condition27).AsBool() && tla.ModuleEqualsSymbol(condition28, Candidate(iface)).AsBool()).AsBool() {
							err = iface.Write(state, []tla.Value{i3}, Follower(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition29 tla.Value
						condition29, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition30 tla.Value
						condition30, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
						}
						var condition31 tla.Value
						condition31, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition32 tla.Value
						condition32, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
						}
						var condition33 tla.Value
						condition33, err = iface.Read(state, []tla.Value{i3})
						if err != nil {
							return err
						}
						if tla.MakeBool(tla.ModuleLessThanSymbol(condition29.ApplyFunction(tla.MakeString("mterm")), condition30).AsBool() || tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition31.ApplyFunction(tla.MakeString("mterm")), condition32).AsBool() && tla.ModuleEqualsSymbol(condition33, Follower(iface)).AsBool()).AsBool() && tla.ModuleLogicalNotSymbol(logOK0).AsBool()).AsBool()).AsBool() {
							switch iface.NextFairnessCounter("AServerNetListener.handleMsg.1", 2) {
							case 0:
								var exprRead23 tla.Value
								exprRead23, err = iface.Read(currentTerm, []tla.Value{i3})
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.Value{j1}, tla.MakeRecord([]tla.RecordField{
									{tla.MakeString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeString("mterm"), exprRead23},
									{tla.MakeString("msuccess"), tla.ModuleFALSE},
									{tla.MakeString("mmatchIndex"), tla.MakeNumber(0)},
									{tla.MakeString("msource"), i3},
									{tla.MakeString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServerNetListener.serverLoop")
							case 1:
								var condition51 tla.Value
								condition51, err = iface.Read(fd, []tla.Value{j1})
								if err != nil {
									return err
								}
								if !condition51.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServerNetListener.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
						} else {
							var condition34 tla.Value
							condition34, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition35 tla.Value
							condition35, err = iface.Read(currentTerm, []tla.Value{i3})
							if err != nil {
								return err
							}
							var condition36 tla.Value
							condition36, err = iface.Read(state, []tla.Value{i3})
							if err != nil {
								return err
							}
							if !tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition34.ApplyFunction(tla.MakeString("mterm")), condition35).AsBool() && tla.ModuleEqualsSymbol(condition36, Follower(iface)).AsBool()).AsBool() && logOK0.AsBool()).AsBool() {
								return fmt.Errorf("%w: ((((m).mterm) = ((currentTerm)[i])) /\\ (((state)[i]) = (Follower))) /\\ (logOK)", distsys.ErrAssertionFailed)
							}
							var indexRead tla.Value
							indexRead, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var index0 tla.Value = tla.ModulePlusSymbol(indexRead.ApplyFunction(tla.MakeString("mprevLogIndex")), tla.MakeNumber(1))
							_ = index0
							var exprRead6 tla.Value
							exprRead6, err = iface.Read(log, []tla.Value{i3})
							if err != nil {
								return err
							}
							var exprRead7 tla.Value
							exprRead7, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(plog, []tla.Value{i3}, tla.MakeRecord([]tla.RecordField{
								{tla.MakeString("cmd"), iface.GetConstant("LogPop")()},
								{tla.MakeString("cnt"), tla.ModuleMinusSymbol(tla.ModuleLen(exprRead6), exprRead7.ApplyFunction(tla.MakeString("mprevLogIndex")))},
							}))
							if err != nil {
								return err
							}
							var exprRead8 tla.Value
							exprRead8, err = iface.Read(log, []tla.Value{i3})
							if err != nil {
								return err
							}
							var exprRead9 tla.Value
							exprRead9, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(log, []tla.Value{i3}, tla.ModuleSubSeq(exprRead8, tla.MakeNumber(1), exprRead9.ApplyFunction(tla.MakeString("mprevLogIndex"))))
							if err != nil {
								return err
							}
							var exprRead10 tla.Value
							exprRead10, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(plog, []tla.Value{i3}, tla.MakeRecord([]tla.RecordField{
								{tla.MakeString("cmd"), iface.GetConstant("LogConcat")()},
								{tla.MakeString("entries"), exprRead10.ApplyFunction(tla.MakeString("mentries"))},
							}))
							if err != nil {
								return err
							}
							var exprRead11 tla.Value
							exprRead11, err = iface.Read(log, []tla.Value{i3})
							if err != nil {
								return err
							}
							var exprRead12 tla.Value
							exprRead12, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(log, []tla.Value{i3}, tla.ModuleOSymbol(exprRead11, exprRead12.ApplyFunction(tla.MakeString("mentries"))))
							if err != nil {
								return err
							}
							var condition37 tla.Value
							condition37, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition38 tla.Value
							condition38, err = iface.Read(log, []tla.Value{i3})
							if err != nil {
								return err
							}
							if !tla.ModuleLessThanOrEqualSymbol(condition37.ApplyFunction(tla.MakeString("mcommitIndex")), tla.ModuleLen(condition38)).AsBool() {
								return fmt.Errorf("%w: ((m).mcommitIndex) <= (Len((log)[i]))", distsys.ErrAssertionFailed)
							}
							var exprRead13 tla.Value
							exprRead13, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(fAdvCommitIdxCh, []tla.Value{i3}, exprRead13)
							if err != nil {
								return err
							}
							switch iface.NextFairnessCounter("AServerNetListener.handleMsg.2", 2) {
							case 0:
								var exprRead24 tla.Value
								exprRead24, err = iface.Read(currentTerm, []tla.Value{i3})
								if err != nil {
									return err
								}
								var exprRead25 tla.Value
								exprRead25, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								var exprRead26 tla.Value
								exprRead26, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.Value{j1}, tla.MakeRecord([]tla.RecordField{
									{tla.MakeString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeString("mterm"), exprRead24},
									{tla.MakeString("msuccess"), tla.ModuleTRUE},
									{tla.MakeString("mmatchIndex"), tla.ModulePlusSymbol(exprRead25.ApplyFunction(tla.MakeString("mprevLogIndex")), tla.ModuleLen(exprRead26.ApplyFunction(tla.MakeString("mentries"))))},
									{tla.MakeString("msource"), i3},
									{tla.MakeString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServerNetListener.serverLoop")
							case 1:
								var condition52 tla.Value
								condition52, err = iface.Read(fd, []tla.Value{j1})
								if err != nil {
									return err
								}
								if !condition52.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServerNetListener.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
							// no statements
						}
						// no statements
						// no statements
					} else {
						var condition39 tla.Value
						condition39, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						if tla.ModuleEqualsSymbol(condition39.ApplyFunction(tla.MakeString("mtype")), AppendEntriesResponse(iface)).AsBool() {
							var condition40 tla.Value
							condition40, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition41 tla.Value
							condition41, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
							if err != nil {
								return err
							}
							if tla.ModuleGreaterThanSymbol(condition40.ApplyFunction(tla.MakeString("mterm")), condition41).AsBool() {
								var exprRead14 tla.Value
								exprRead14, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								err = iface.Write(currentTerm, []tla.Value{iface.Self()}, exprRead14.ApplyFunction(tla.MakeString("mterm")))
								if err != nil {
									return err
								}
								err = iface.Write(state, []tla.Value{iface.Self()}, Follower(iface))
								if err != nil {
									return err
								}
								err = iface.Write(votedFor, []tla.Value{iface.Self()}, Nil(iface))
								if err != nil {
									return err
								}
								err = iface.Write(leader, []tla.Value{iface.Self()}, Nil(iface))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition42 tla.Value
							condition42, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition43 tla.Value
							condition43, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
							if err != nil {
								return err
							}
							if tla.ModuleLessThanSymbol(condition42.ApplyFunction(tla.MakeString("mterm")), condition43).AsBool() {
								// skip
								return iface.Goto("AServerNetListener.serverLoop")
							} else {
								var i4 tla.Value = iface.Self()
								_ = i4
								var jRead2 tla.Value
								jRead2, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								var j2 tla.Value = jRead2.ApplyFunction(tla.MakeString("msource"))
								_ = j2
								var condition44 tla.Value
								condition44, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								var condition45 tla.Value
								condition45, err = iface.Read(currentTerm, []tla.Value{i4})
								if err != nil {
									return err
								}
								if !tla.ModuleEqualsSymbol(condition44.ApplyFunction(tla.MakeString("mterm")), condition45).AsBool() {
									return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
								}
								var condition46 tla.Value
								condition46, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								if condition46.ApplyFunction(tla.MakeString("msuccess")).AsBool() {
									var exprRead15 tla.Value
									exprRead15, err = iface.Read(nextIndex, []tla.Value{i4})
									if err != nil {
										return err
									}
									var exprRead16 tla.Value
									exprRead16, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.Value{i4}, tla.FunctionSubstitution(exprRead15, []tla.FunctionSubstitutionRecord{
										{[]tla.Value{j2}, func(anchor tla.Value) tla.Value {
											return tla.ModulePlusSymbol(exprRead16.ApplyFunction(tla.MakeString("mmatchIndex")), tla.MakeNumber(1))
										}},
									}))
									if err != nil {
										return err
									}
									var exprRead17 tla.Value
									exprRead17, err = iface.Read(matchIndex1, []tla.Value{i4})
									if err != nil {
										return err
									}
									var exprRead18 tla.Value
									exprRead18, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									err = iface.Write(matchIndex1, []tla.Value{i4}, tla.FunctionSubstitution(exprRead17, []tla.FunctionSubstitutionRecord{
										{[]tla.Value{j2}, func(anchor0 tla.Value) tla.Value {
											return exprRead18.ApplyFunction(tla.MakeString("mmatchIndex"))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServerNetListener.serverLoop")
								} else {
									var exprRead19 tla.Value
									exprRead19, err = iface.Read(nextIndex, []tla.Value{i4})
									if err != nil {
										return err
									}
									var exprRead20 tla.Value
									exprRead20, err = iface.Read(nextIndex, []tla.Value{i4})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.Value{i4}, tla.FunctionSubstitution(exprRead19, []tla.FunctionSubstitutionRecord{
										{[]tla.Value{j2}, func(anchor1 tla.Value) tla.Value {
											return Max(iface, tla.MakeSet(tla.ModuleMinusSymbol(exprRead20.ApplyFunction(j2), tla.MakeNumber(1)), tla.MakeNumber(1)))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServerNetListener.serverLoop")
								}
								// no statements
								// no statements
							}
							// no statements
						} else {
							var condition47 tla.Value
							condition47, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							if tla.ModuleEqualsSymbol(condition47.ApplyFunction(tla.MakeString("mtype")), ProposeMessage(iface)).AsBool() {
								var i5 tla.Value = iface.Self()
								_ = i5
								if iface.GetConstant("Debug")().AsBool() {
									var toPrint0 tla.Value
									toPrint0, err = iface.Read(currentTerm, []tla.Value{i5})
									if err != nil {
										return err
									}
									var toPrint1 tla.Value
									toPrint1, err = iface.Read(state, []tla.Value{i5})
									if err != nil {
										return err
									}
									var toPrint2 tla.Value
									toPrint2, err = iface.Read(leader, []tla.Value{i5})
									if err != nil {
										return err
									}
									tla.MakeTuple(tla.MakeString("HandleProposeMessage"), i5, toPrint0, toPrint1, toPrint2).PCalPrint()
									// no statements
								} else {
									// no statements
								}
								var condition48 tla.Value
								condition48, err = iface.Read(state, []tla.Value{i5})
								if err != nil {
									return err
								}
								if tla.ModuleEqualsSymbol(condition48, Leader(iface)).AsBool() {
									var entryRead tla.Value
									entryRead, err = iface.Read(currentTerm, []tla.Value{i5})
									if err != nil {
										return err
									}
									var entryRead0 tla.Value
									entryRead0, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var entry tla.Value = tla.MakeRecord([]tla.RecordField{
										{tla.MakeString("term"), entryRead},
										{tla.MakeString("cmd"), entryRead0.ApplyFunction(tla.MakeString("mcmd"))},
									})
									_ = entry
									var exprRead21 tla.Value
									exprRead21, err = iface.Read(log, []tla.Value{i5})
									if err != nil {
										return err
									}
									err = iface.Write(log, []tla.Value{i5}, tla.ModuleAppend(exprRead21, entry))
									if err != nil {
										return err
									}
									err = iface.Write(plog, []tla.Value{i5}, tla.MakeRecord([]tla.RecordField{
										{tla.MakeString("cmd"), iface.GetConstant("LogConcat")()},
										{tla.MakeString("entries"), tla.MakeTuple(entry)},
									}))
									if err != nil {
										return err
									}
									err = iface.Write(appendEntriesCh, []tla.Value{i5}, tla.ModuleTRUE)
									if err != nil {
										return err
									}
									return iface.Goto("AServerNetListener.serverLoop")
									// no statements
								} else {
									var condition49 tla.Value
									condition49, err = iface.Read(leader, []tla.Value{i5})
									if err != nil {
										return err
									}
									if tla.ModuleNotEqualsSymbol(condition49, Nil(iface)).AsBool() {
										var jRead3 tla.Value
										jRead3, err = iface.Read(leader, []tla.Value{i5})
										if err != nil {
											return err
										}
										var j3 tla.Value = jRead3
										_ = j3
										switch iface.NextFairnessCounter("AServerNetListener.handleMsg.3", 2) {
										case 0:
											var exprRead27 tla.Value
											exprRead27, err = iface.Read(m1, nil)
											if err != nil {
												return err
											}
											err = iface.Write(net0, []tla.Value{j3}, tla.MakeRecord([]tla.RecordField{
												{tla.MakeString("mtype"), ProposeMessage(iface)},
												{tla.MakeString("mcmd"), exprRead27.ApplyFunction(tla.MakeString("mcmd"))},
												{tla.MakeString("msource"), i5},
												{tla.MakeString("mdest"), j3},
											}))
											if err != nil {
												return err
											}
											return iface.Goto("AServerNetListener.serverLoop")
										case 1:
											var condition53 tla.Value
											condition53, err = iface.Read(fd, []tla.Value{j3})
											if err != nil {
												return err
											}
											if !condition53.AsBool() {
												return distsys.ErrCriticalSectionAborted
											}
											return iface.Goto("AServerNetListener.serverLoop")
										default:
											panic("current branch of either matches no code paths!")
										}
										// no statements
										// no statements
									} else {
										return iface.Goto("AServerNetListener.serverLoop")
									}
									// no statements
								}
								// no statements
								// no statements
							} else {
								return iface.Goto("AServerNetListener.serverLoop")
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
		Name: "AServerNetListener.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerPropChListener.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled1, err := iface.RequireArchetypeResourceRef("AServerPropChListener.netEnabled")
			if err != nil {
				return err
			}
			srvId1 := iface.RequireArchetypeResource("AServerPropChListener.srvId")
			m54 := iface.RequireArchetypeResource("AServerPropChListener.m")
			propCh, err := iface.RequireArchetypeResourceRef("AServerPropChListener.propCh")
			if err != nil {
				return err
			}
			currentTerm25, err := iface.RequireArchetypeResourceRef("AServerPropChListener.currentTerm")
			if err != nil {
				return err
			}
			state10, err := iface.RequireArchetypeResourceRef("AServerPropChListener.state")
			if err != nil {
				return err
			}
			leader7, err := iface.RequireArchetypeResourceRef("AServerPropChListener.leader")
			if err != nil {
				return err
			}
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition54 tla.Value
					condition54, err = iface.Read(srvId1, nil)
					if err != nil {
						return err
					}
					var condition55 tla.Value
					condition55, err = iface.Read(netEnabled1, []tla.Value{condition54})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition55).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var iRead tla.Value
				iRead, err = iface.Read(srvId1, nil)
				if err != nil {
					return err
				}
				var i6 tla.Value = iRead
				_ = i6
				var exprRead28 tla.Value
				exprRead28, err = iface.Read(propCh, []tla.Value{i6})
				if err != nil {
					return err
				}
				err = iface.Write(m54, nil, exprRead28)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint3 tla.Value
					toPrint3, err = iface.Read(currentTerm25, []tla.Value{i6})
					if err != nil {
						return err
					}
					var toPrint4 tla.Value
					toPrint4, err = iface.Read(state10, []tla.Value{i6})
					if err != nil {
						return err
					}
					var toPrint5 tla.Value
					toPrint5, err = iface.Read(leader7, []tla.Value{i6})
					if err != nil {
						return err
					}
					var toPrint6 tla.Value
					toPrint6, err = iface.Read(m54, nil)
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ReceiveProposeMessage"), i6, toPrint3, toPrint4, toPrint5, toPrint6).PCalPrint()
					return iface.Goto("AServerPropChListener.handleMsg")
				} else {
					return iface.Goto("AServerPropChListener.handleMsg")
				}
				// no statements
				// no statements
			} else {
				return iface.Goto("AServerPropChListener.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerPropChListener.handleMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled2, err := iface.RequireArchetypeResourceRef("AServerPropChListener.netEnabled")
			if err != nil {
				return err
			}
			srvId3 := iface.RequireArchetypeResource("AServerPropChListener.srvId")
			m56 := iface.RequireArchetypeResource("AServerPropChListener.m")
			currentTerm26, err := iface.RequireArchetypeResourceRef("AServerPropChListener.currentTerm")
			if err != nil {
				return err
			}
			state11, err := iface.RequireArchetypeResourceRef("AServerPropChListener.state")
			if err != nil {
				return err
			}
			leader8, err := iface.RequireArchetypeResourceRef("AServerPropChListener.leader")
			if err != nil {
				return err
			}
			log12, err := iface.RequireArchetypeResourceRef("AServerPropChListener.log")
			if err != nil {
				return err
			}
			plog2, err := iface.RequireArchetypeResourceRef("AServerPropChListener.plog")
			if err != nil {
				return err
			}
			appendEntriesCh0, err := iface.RequireArchetypeResourceRef("AServerPropChListener.appendEntriesCh")
			if err != nil {
				return err
			}
			net4, err := iface.RequireArchetypeResourceRef("AServerPropChListener.net")
			if err != nil {
				return err
			}
			fd3, err := iface.RequireArchetypeResourceRef("AServerPropChListener.fd")
			if err != nil {
				return err
			}
			if iface.GetConstant("ExploreFail")().AsBool() {
				var condition56 tla.Value
				condition56, err = iface.Read(srvId3, nil)
				if err != nil {
					return err
				}
				var condition57 tla.Value
				condition57, err = iface.Read(netEnabled2, []tla.Value{condition56})
				if err != nil {
					return err
				}
				if tla.ModuleLogicalNotSymbol(condition57).AsBool() {
					if !tla.ModuleFALSE.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					// no statements
				} else {
					// no statements
				}
				// no statements
			} else {
				// no statements
			}
			var condition58 tla.Value
			condition58, err = iface.Read(m56, nil)
			if err != nil {
				return err
			}
			if !tla.ModuleEqualsSymbol(condition58.ApplyFunction(tla.MakeString("mtype")), ProposeMessage(iface)).AsBool() {
				return fmt.Errorf("%w: ((m).mtype) = (ProposeMessage)", distsys.ErrAssertionFailed)
			}
			var iRead0 tla.Value
			iRead0, err = iface.Read(srvId3, nil)
			if err != nil {
				return err
			}
			var i7 tla.Value = iRead0
			_ = i7
			if iface.GetConstant("Debug")().AsBool() {
				var toPrint7 tla.Value
				toPrint7, err = iface.Read(currentTerm26, []tla.Value{i7})
				if err != nil {
					return err
				}
				var toPrint8 tla.Value
				toPrint8, err = iface.Read(state11, []tla.Value{i7})
				if err != nil {
					return err
				}
				var toPrint9 tla.Value
				toPrint9, err = iface.Read(leader8, []tla.Value{i7})
				if err != nil {
					return err
				}
				tla.MakeTuple(tla.MakeString("HandleProposeMessage"), i7, toPrint7, toPrint8, toPrint9).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			var condition59 tla.Value
			condition59, err = iface.Read(state11, []tla.Value{i7})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition59, Leader(iface)).AsBool() {
				var entryRead1 tla.Value
				entryRead1, err = iface.Read(currentTerm26, []tla.Value{i7})
				if err != nil {
					return err
				}
				var entryRead2 tla.Value
				entryRead2, err = iface.Read(m56, nil)
				if err != nil {
					return err
				}
				var entry0 tla.Value = tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("term"), entryRead1},
					{tla.MakeString("cmd"), entryRead2.ApplyFunction(tla.MakeString("mcmd"))},
				})
				_ = entry0
				var exprRead29 tla.Value
				exprRead29, err = iface.Read(log12, []tla.Value{i7})
				if err != nil {
					return err
				}
				err = iface.Write(log12, []tla.Value{i7}, tla.ModuleAppend(exprRead29, entry0))
				if err != nil {
					return err
				}
				err = iface.Write(plog2, []tla.Value{i7}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("cmd"), iface.GetConstant("LogConcat")()},
					{tla.MakeString("entries"), tla.MakeTuple(entry0)},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(appendEntriesCh0, []tla.Value{i7}, tla.ModuleTRUE)
				if err != nil {
					return err
				}
				return iface.Goto("AServerPropChListener.serverLoop")
				// no statements
			} else {
				var condition60 tla.Value
				condition60, err = iface.Read(leader8, []tla.Value{i7})
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition60, Nil(iface)).AsBool() {
					var jRead4 tla.Value
					jRead4, err = iface.Read(leader8, []tla.Value{i7})
					if err != nil {
						return err
					}
					var j4 tla.Value = jRead4
					_ = j4
					switch iface.NextFairnessCounter("AServerPropChListener.handleMsg.0", 2) {
					case 0:
						var exprRead30 tla.Value
						exprRead30, err = iface.Read(m56, nil)
						if err != nil {
							return err
						}
						err = iface.Write(net4, []tla.Value{j4}, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("mtype"), ProposeMessage(iface)},
							{tla.MakeString("mcmd"), exprRead30.ApplyFunction(tla.MakeString("mcmd"))},
							{tla.MakeString("msource"), i7},
							{tla.MakeString("mdest"), j4},
						}))
						if err != nil {
							return err
						}
						return iface.Goto("AServerPropChListener.serverLoop")
					case 1:
						var condition61 tla.Value
						condition61, err = iface.Read(fd3, []tla.Value{j4})
						if err != nil {
							return err
						}
						if !condition61.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						return iface.Goto("AServerPropChListener.serverLoop")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
					// no statements
				} else {
					return iface.Goto("AServerPropChListener.serverLoop")
				}
				// no statements
			}
			// no statements
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerPropChListener.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerRequestVote.serverRequestVoteLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled3, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netEnabled")
			if err != nil {
				return err
			}
			srvId5 := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			leaderTimeout0, err := iface.RequireArchetypeResourceRef("AServerRequestVote.leaderTimeout")
			if err != nil {
				return err
			}
			netLen, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netLen")
			if err != nil {
				return err
			}
			state13, err := iface.RequireArchetypeResourceRef("AServerRequestVote.state")
			if err != nil {
				return err
			}
			currentTerm28, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
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
			leader11, err := iface.RequireArchetypeResourceRef("AServerRequestVote.leader")
			if err != nil {
				return err
			}
			idx := iface.RequireArchetypeResource("AServerRequestVote.idx")
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition62 tla.Value
					condition62, err = iface.Read(srvId5, nil)
					if err != nil {
						return err
					}
					var condition63 tla.Value
					condition63, err = iface.Read(netEnabled3, []tla.Value{condition62})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition63).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var condition64 tla.Value
				condition64, err = iface.Read(leaderTimeout0, nil)
				if err != nil {
					return err
				}
				if !condition64.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition65 tla.Value
				condition65, err = iface.Read(srvId5, nil)
				if err != nil {
					return err
				}
				var condition66 tla.Value
				condition66, err = iface.Read(netLen, []tla.Value{condition65})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition66, tla.MakeNumber(0)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition67 tla.Value
				condition67, err = iface.Read(srvId5, nil)
				if err != nil {
					return err
				}
				var condition68 tla.Value
				condition68, err = iface.Read(state13, []tla.Value{condition67})
				if err != nil {
					return err
				}
				if !tla.ModuleInSymbol(condition68, tla.MakeSet(Follower(iface), Candidate(iface))).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead1 tla.Value
				iRead1, err = iface.Read(srvId5, nil)
				if err != nil {
					return err
				}
				var i8 tla.Value = iRead1
				_ = i8
				err = iface.Write(state13, []tla.Value{i8}, Candidate(iface))
				if err != nil {
					return err
				}
				var exprRead31 tla.Value
				exprRead31, err = iface.Read(currentTerm28, []tla.Value{i8})
				if err != nil {
					return err
				}
				err = iface.Write(currentTerm28, []tla.Value{i8}, tla.ModulePlusSymbol(exprRead31, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(votedFor5, []tla.Value{i8}, i8)
				if err != nil {
					return err
				}
				err = iface.Write(votesResponded1, []tla.Value{i8}, tla.MakeSet(i8))
				if err != nil {
					return err
				}
				err = iface.Write(votesGranted2, []tla.Value{i8}, tla.MakeSet(i8))
				if err != nil {
					return err
				}
				err = iface.Write(leader11, []tla.Value{i8}, Nil(iface))
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint10 tla.Value
					toPrint10, err = iface.Read(currentTerm28, []tla.Value{i8})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ServerTimeout"), i8, toPrint10).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				// no statements
				err = iface.Write(idx, nil, tla.MakeNumber(1))
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
			netEnabled4, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netEnabled")
			if err != nil {
				return err
			}
			srvId9 := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			net5, err := iface.RequireArchetypeResourceRef("AServerRequestVote.net")
			if err != nil {
				return err
			}
			currentTerm31, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
			if err != nil {
				return err
			}
			log14, err := iface.RequireArchetypeResourceRef("AServerRequestVote.log")
			if err != nil {
				return err
			}
			fd4, err := iface.RequireArchetypeResourceRef("AServerRequestVote.fd")
			if err != nil {
				return err
			}
			var condition69 tla.Value
			condition69, err = iface.Read(idx0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition69, iface.GetConstant("NumServers")()).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition70 tla.Value
					condition70, err = iface.Read(srvId9, nil)
					if err != nil {
						return err
					}
					var condition71 tla.Value
					condition71, err = iface.Read(netEnabled4, []tla.Value{condition70})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition71).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var condition72 tla.Value
				condition72, err = iface.Read(idx0, nil)
				if err != nil {
					return err
				}
				var condition73 tla.Value
				condition73, err = iface.Read(srvId9, nil)
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition72, condition73).AsBool() {
					switch iface.NextFairnessCounter("AServerRequestVote.requestVoteLoop.0", 2) {
					case 0:
						var exprRead33 tla.Value
						exprRead33, err = iface.Read(srvId9, nil)
						if err != nil {
							return err
						}
						var exprRead34 tla.Value
						exprRead34, err = iface.Read(currentTerm31, []tla.Value{exprRead33})
						if err != nil {
							return err
						}
						var exprRead35 tla.Value
						exprRead35, err = iface.Read(srvId9, nil)
						if err != nil {
							return err
						}
						var exprRead36 tla.Value
						exprRead36, err = iface.Read(log14, []tla.Value{exprRead35})
						if err != nil {
							return err
						}
						var exprRead37 tla.Value
						exprRead37, err = iface.Read(srvId9, nil)
						if err != nil {
							return err
						}
						var exprRead38 tla.Value
						exprRead38, err = iface.Read(log14, []tla.Value{exprRead37})
						if err != nil {
							return err
						}
						var exprRead39 tla.Value
						exprRead39, err = iface.Read(srvId9, nil)
						if err != nil {
							return err
						}
						var exprRead40 tla.Value
						exprRead40, err = iface.Read(idx0, nil)
						if err != nil {
							return err
						}
						var indexRead0 tla.Value
						indexRead0, err = iface.Read(idx0, nil)
						if err != nil {
							return err
						}
						err = iface.Write(net5, []tla.Value{indexRead0}, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("mtype"), RequestVoteRequest(iface)},
							{tla.MakeString("mterm"), exprRead34},
							{tla.MakeString("mlastLogTerm"), LastTerm(iface, exprRead36)},
							{tla.MakeString("mlastLogIndex"), tla.ModuleLen(exprRead38)},
							{tla.MakeString("msource"), exprRead39},
							{tla.MakeString("mdest"), exprRead40},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition74 tla.Value
						condition74, err = iface.Read(idx0, nil)
						if err != nil {
							return err
						}
						var condition75 tla.Value
						condition75, err = iface.Read(fd4, []tla.Value{condition74})
						if err != nil {
							return err
						}
						if !condition75.AsBool() {
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
				var exprRead32 tla.Value
				exprRead32, err = iface.Read(idx0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(idx0, nil, tla.ModulePlusSymbol(exprRead32, tla.MakeNumber(1)))
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
			appendEntriesCh1, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.appendEntriesCh")
			if err != nil {
				return err
			}
			srvId15 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			netEnabled5, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.netEnabled")
			if err != nil {
				return err
			}
			state15, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			idx7 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			var condition76 tla.Value
			condition76, err = iface.Read(srvId15, nil)
			if err != nil {
				return err
			}
			var condition77 tla.Value
			condition77, err = iface.Read(appendEntriesCh1, []tla.Value{condition76})
			if err != nil {
				return err
			}
			if condition77.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition78 tla.Value
					condition78, err = iface.Read(srvId15, nil)
					if err != nil {
						return err
					}
					var condition79 tla.Value
					condition79, err = iface.Read(netEnabled5, []tla.Value{condition78})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition79).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var condition80 tla.Value
				condition80, err = iface.Read(srvId15, nil)
				if err != nil {
					return err
				}
				var condition81 tla.Value
				condition81, err = iface.Read(state15, []tla.Value{condition80})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition81, Leader(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				err = iface.Write(idx7, nil, tla.MakeNumber(1))
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
			state16, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			srvId18 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			idx8 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			netEnabled6, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.netEnabled")
			if err != nil {
				return err
			}
			nextIndex4, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.nextIndex")
			if err != nil {
				return err
			}
			log16, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.log")
			if err != nil {
				return err
			}
			net6, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.net")
			if err != nil {
				return err
			}
			currentTerm32, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.currentTerm")
			if err != nil {
				return err
			}
			commitIndex, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.commitIndex")
			if err != nil {
				return err
			}
			fd5, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.fd")
			if err != nil {
				return err
			}
			var condition82 tla.Value
			condition82, err = iface.Read(srvId18, nil)
			if err != nil {
				return err
			}
			var condition83 tla.Value
			condition83, err = iface.Read(state16, []tla.Value{condition82})
			if err != nil {
				return err
			}
			var condition84 tla.Value
			condition84, err = iface.Read(idx8, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleEqualsSymbol(condition83, Leader(iface)).AsBool() && tla.ModuleLessThanOrEqualSymbol(condition84, iface.GetConstant("NumServers")()).AsBool()).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition85 tla.Value
					condition85, err = iface.Read(srvId18, nil)
					if err != nil {
						return err
					}
					var condition86 tla.Value
					condition86, err = iface.Read(netEnabled6, []tla.Value{condition85})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition86).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var condition87 tla.Value
				condition87, err = iface.Read(idx8, nil)
				if err != nil {
					return err
				}
				var condition88 tla.Value
				condition88, err = iface.Read(srvId18, nil)
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition87, condition88).AsBool() {
					var prevLogIndexRead tla.Value
					prevLogIndexRead, err = iface.Read(srvId18, nil)
					if err != nil {
						return err
					}
					var prevLogIndexRead0 tla.Value
					prevLogIndexRead0, err = iface.Read(nextIndex4, []tla.Value{prevLogIndexRead})
					if err != nil {
						return err
					}
					var prevLogIndexRead1 tla.Value
					prevLogIndexRead1, err = iface.Read(idx8, nil)
					if err != nil {
						return err
					}
					var prevLogIndex tla.Value = tla.ModuleMinusSymbol(prevLogIndexRead0.ApplyFunction(prevLogIndexRead1), tla.MakeNumber(1))
					_ = prevLogIndex
					var prevLogTermRead tla.Value
					prevLogTermRead, err = iface.Read(srvId18, nil)
					if err != nil {
						return err
					}
					var prevLogTermRead0 tla.Value
					prevLogTermRead0, err = iface.Read(log16, []tla.Value{prevLogTermRead})
					if err != nil {
						return err
					}
					var prevLogTerm tla.Value = func() tla.Value {
						if tla.ModuleGreaterThanSymbol(prevLogIndex, tla.MakeNumber(0)).AsBool() {
							return prevLogTermRead0.ApplyFunction(prevLogIndex).ApplyFunction(tla.MakeString("term"))
						} else {
							return tla.MakeNumber(0)
						}
					}()
					_ = prevLogTerm
					var entriesRead tla.Value
					entriesRead, err = iface.Read(srvId18, nil)
					if err != nil {
						return err
					}
					var entriesRead0 tla.Value
					entriesRead0, err = iface.Read(log16, []tla.Value{entriesRead})
					if err != nil {
						return err
					}
					var entriesRead1 tla.Value
					entriesRead1, err = iface.Read(srvId18, nil)
					if err != nil {
						return err
					}
					var entriesRead2 tla.Value
					entriesRead2, err = iface.Read(nextIndex4, []tla.Value{entriesRead1})
					if err != nil {
						return err
					}
					var entriesRead3 tla.Value
					entriesRead3, err = iface.Read(idx8, nil)
					if err != nil {
						return err
					}
					var entriesRead4 tla.Value
					entriesRead4, err = iface.Read(srvId18, nil)
					if err != nil {
						return err
					}
					var entriesRead5 tla.Value
					entriesRead5, err = iface.Read(log16, []tla.Value{entriesRead4})
					if err != nil {
						return err
					}
					var entries tla.Value = tla.ModuleSubSeq(entriesRead0, entriesRead2.ApplyFunction(entriesRead3), tla.ModuleLen(entriesRead5))
					_ = entries
					switch iface.NextFairnessCounter("AServerAppendEntries.appendEntriesLoop.0", 2) {
					case 0:
						var exprRead42 tla.Value
						exprRead42, err = iface.Read(srvId18, nil)
						if err != nil {
							return err
						}
						var exprRead43 tla.Value
						exprRead43, err = iface.Read(currentTerm32, []tla.Value{exprRead42})
						if err != nil {
							return err
						}
						var exprRead44 tla.Value
						exprRead44, err = iface.Read(srvId18, nil)
						if err != nil {
							return err
						}
						var exprRead45 tla.Value
						exprRead45, err = iface.Read(commitIndex, []tla.Value{exprRead44})
						if err != nil {
							return err
						}
						var exprRead46 tla.Value
						exprRead46, err = iface.Read(srvId18, nil)
						if err != nil {
							return err
						}
						var exprRead47 tla.Value
						exprRead47, err = iface.Read(idx8, nil)
						if err != nil {
							return err
						}
						var indexRead1 tla.Value
						indexRead1, err = iface.Read(idx8, nil)
						if err != nil {
							return err
						}
						err = iface.Write(net6, []tla.Value{indexRead1}, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("mtype"), AppendEntriesRequest(iface)},
							{tla.MakeString("mterm"), exprRead43},
							{tla.MakeString("mprevLogIndex"), prevLogIndex},
							{tla.MakeString("mprevLogTerm"), prevLogTerm},
							{tla.MakeString("mentries"), entries},
							{tla.MakeString("mcommitIndex"), exprRead45},
							{tla.MakeString("msource"), exprRead46},
							{tla.MakeString("mdest"), exprRead47},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition89 tla.Value
						condition89, err = iface.Read(idx8, nil)
						if err != nil {
							return err
						}
						var condition90 tla.Value
						condition90, err = iface.Read(fd5, []tla.Value{condition89})
						if err != nil {
							return err
						}
						if !condition90.AsBool() {
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
				var exprRead41 tla.Value
				exprRead41, err = iface.Read(idx8, nil)
				if err != nil {
					return err
				}
				err = iface.Write(idx8, nil, tla.ModulePlusSymbol(exprRead41, tla.MakeNumber(1)))
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
			netEnabled7, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.netEnabled")
			if err != nil {
				return err
			}
			srvId29 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			state17, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.state")
			if err != nil {
				return err
			}
			log19, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			matchIndex3, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.matchIndex")
			if err != nil {
				return err
			}
			currentTerm33, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.currentTerm")
			if err != nil {
				return err
			}
			commitIndex0, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			newCommitIndex := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition91 tla.Value
					condition91, err = iface.Read(srvId29, nil)
					if err != nil {
						return err
					}
					var condition92 tla.Value
					condition92, err = iface.Read(netEnabled7, []tla.Value{condition91})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition92).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var condition93 tla.Value
				condition93, err = iface.Read(srvId29, nil)
				if err != nil {
					return err
				}
				var condition94 tla.Value
				condition94, err = iface.Read(state17, []tla.Value{condition93})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition94, Leader(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead2 tla.Value
				iRead2, err = iface.Read(srvId29, nil)
				if err != nil {
					return err
				}
				var i9 tla.Value = iRead2
				_ = i9
				var maxAgreeIndexRead tla.Value
				maxAgreeIndexRead, err = iface.Read(log19, []tla.Value{i9})
				if err != nil {
					return err
				}
				var maxAgreeIndexRead0 tla.Value
				maxAgreeIndexRead0, err = iface.Read(matchIndex3, []tla.Value{i9})
				if err != nil {
					return err
				}
				var maxAgreeIndex tla.Value = FindMaxAgreeIndex(iface, maxAgreeIndexRead, i9, maxAgreeIndexRead0)
				_ = maxAgreeIndex
				var nCommitIndexRead tla.Value
				nCommitIndexRead, err = iface.Read(log19, []tla.Value{i9})
				if err != nil {
					return err
				}
				var nCommitIndexRead0 tla.Value
				nCommitIndexRead0, err = iface.Read(currentTerm33, []tla.Value{i9})
				if err != nil {
					return err
				}
				var nCommitIndexRead1 tla.Value
				nCommitIndexRead1, err = iface.Read(commitIndex0, []tla.Value{i9})
				if err != nil {
					return err
				}
				var nCommitIndex tla.Value = func() tla.Value {
					if tla.MakeBool(tla.ModuleNotEqualsSymbol(maxAgreeIndex, Nil(iface)).AsBool() && tla.ModuleEqualsSymbol(nCommitIndexRead.ApplyFunction(maxAgreeIndex).ApplyFunction(tla.MakeString("term")), nCommitIndexRead0).AsBool()).AsBool() {
						return maxAgreeIndex
					} else {
						return nCommitIndexRead1
					}
				}()
				_ = nCommitIndex
				err = iface.Write(newCommitIndex, nil, nCommitIndex)
				if err != nil {
					return err
				}
				var condition95 tla.Value
				condition95, err = iface.Read(newCommitIndex, nil)
				if err != nil {
					return err
				}
				var condition96 tla.Value
				condition96, err = iface.Read(commitIndex0, []tla.Value{i9})
				if err != nil {
					return err
				}
				if !tla.ModuleGreaterThanOrEqualSymbol(condition95, condition96).AsBool() {
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
			srvId32 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			newCommitIndex1 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			netEnabled8, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.netEnabled")
			if err != nil {
				return err
			}
			log21, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			acctCh, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.acctCh")
			if err != nil {
				return err
			}
			var condition97 tla.Value
			condition97, err = iface.Read(srvId32, nil)
			if err != nil {
				return err
			}
			var condition98 tla.Value
			condition98, err = iface.Read(commitIndex2, []tla.Value{condition97})
			if err != nil {
				return err
			}
			var condition99 tla.Value
			condition99, err = iface.Read(newCommitIndex1, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition98, condition99).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition100 tla.Value
					condition100, err = iface.Read(srvId32, nil)
					if err != nil {
						return err
					}
					var condition101 tla.Value
					condition101, err = iface.Read(netEnabled8, []tla.Value{condition100})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition101).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead48 tla.Value
				exprRead48, err = iface.Read(srvId32, nil)
				if err != nil {
					return err
				}
				var exprRead49 tla.Value
				exprRead49, err = iface.Read(commitIndex2, []tla.Value{exprRead48})
				if err != nil {
					return err
				}
				var indexRead2 tla.Value
				indexRead2, err = iface.Read(srvId32, nil)
				if err != nil {
					return err
				}
				err = iface.Write(commitIndex2, []tla.Value{indexRead2}, tla.ModulePlusSymbol(exprRead49, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				var iRead3 tla.Value
				iRead3, err = iface.Read(srvId32, nil)
				if err != nil {
					return err
				}
				var i10 tla.Value = iRead3
				_ = i10
				var kRead tla.Value
				kRead, err = iface.Read(commitIndex2, []tla.Value{i10})
				if err != nil {
					return err
				}
				var k0 tla.Value = kRead
				_ = k0
				var entryRead3 tla.Value
				entryRead3, err = iface.Read(log21, []tla.Value{i10})
				if err != nil {
					return err
				}
				var entry1 tla.Value = entryRead3.ApplyFunction(k0)
				_ = entry1
				var cmd tla.Value = entry1.ApplyFunction(tla.MakeString("cmd"))
				_ = cmd
				if iface.GetConstant("Debug")().AsBool() {
					tla.MakeTuple(tla.MakeString("ServerAccept"), i10, cmd).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(acctCh, []tla.Value{i10}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("mtype"), AcceptMessage(iface)},
					{tla.MakeString("mcmd"), cmd},
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
			srvId37 := iface.RequireArchetypeResource("AServerBecomeLeader.srvId")
			netEnabled9, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.netEnabled")
			if err != nil {
				return err
			}
			state18, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.state")
			if err != nil {
				return err
			}
			votesGranted3, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.votesGranted")
			if err != nil {
				return err
			}
			nextIndex6, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.nextIndex")
			if err != nil {
				return err
			}
			log22, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.log")
			if err != nil {
				return err
			}
			matchIndex4, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.matchIndex")
			if err != nil {
				return err
			}
			leader12, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.leader")
			if err != nil {
				return err
			}
			appendEntriesCh2, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.appendEntriesCh")
			if err != nil {
				return err
			}
			currentTerm34, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.currentTerm")
			if err != nil {
				return err
			}
			var condition102 tla.Value
			condition102, err = iface.Read(srvId37, nil)
			if err != nil {
				return err
			}
			var condition103 tla.Value
			condition103, err = iface.Read(becomeLeaderCh0, []tla.Value{condition102})
			if err != nil {
				return err
			}
			if condition103.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition104 tla.Value
					condition104, err = iface.Read(srvId37, nil)
					if err != nil {
						return err
					}
					var condition105 tla.Value
					condition105, err = iface.Read(netEnabled9, []tla.Value{condition104})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition105).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var condition106 tla.Value
				condition106, err = iface.Read(srvId37, nil)
				if err != nil {
					return err
				}
				var condition107 tla.Value
				condition107, err = iface.Read(state18, []tla.Value{condition106})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition107, Candidate(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition108 tla.Value
				condition108, err = iface.Read(srvId37, nil)
				if err != nil {
					return err
				}
				var condition109 tla.Value
				condition109, err = iface.Read(votesGranted3, []tla.Value{condition108})
				if err != nil {
					return err
				}
				if !IsQuorum(iface, condition109).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead4 tla.Value
				iRead4, err = iface.Read(srvId37, nil)
				if err != nil {
					return err
				}
				var i11 tla.Value = iRead4
				_ = i11
				err = iface.Write(state18, []tla.Value{i11}, Leader(iface))
				if err != nil {
					return err
				}
				var exprRead50 tla.Value
				exprRead50, err = iface.Read(log22, []tla.Value{i11})
				if err != nil {
					return err
				}
				err = iface.Write(nextIndex6, []tla.Value{i11}, tla.MakeFunction([]tla.Value{ServerSet(iface)}, func(args []tla.Value) tla.Value {
					var j5 tla.Value = args[0]
					_ = j5
					return tla.ModulePlusSymbol(tla.ModuleLen(exprRead50), tla.MakeNumber(1))
				}))
				if err != nil {
					return err
				}
				err = iface.Write(matchIndex4, []tla.Value{i11}, tla.MakeFunction([]tla.Value{ServerSet(iface)}, func(args0 []tla.Value) tla.Value {
					var j6 tla.Value = args0[0]
					_ = j6
					return tla.MakeNumber(0)
				}))
				if err != nil {
					return err
				}
				err = iface.Write(leader12, []tla.Value{i11}, i11)
				if err != nil {
					return err
				}
				err = iface.Write(appendEntriesCh2, []tla.Value{i11}, tla.ModuleTRUE)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint11 tla.Value
					toPrint11, err = iface.Read(currentTerm34, []tla.Value{i11})
					if err != nil {
						return err
					}
					var toPrint12 tla.Value
					toPrint12, err = iface.Read(state18, []tla.Value{i11})
					if err != nil {
						return err
					}
					var toPrint13 tla.Value
					toPrint13, err = iface.Read(leader12, []tla.Value{i11})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("BecomeLeader"), i11, toPrint11, toPrint12, toPrint13).PCalPrint()
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
			netEnabled10, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.netEnabled")
			if err != nil {
				return err
			}
			srvId42 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.srvId")
			m59 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.m")
			fAdvCommitIdxCh0, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.fAdvCommitIdxCh")
			if err != nil {
				return err
			}
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition110 tla.Value
					condition110, err = iface.Read(srvId42, nil)
					if err != nil {
						return err
					}
					var condition111 tla.Value
					condition111, err = iface.Read(netEnabled10, []tla.Value{condition110})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition111).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead51 tla.Value
				exprRead51, err = iface.Read(srvId42, nil)
				if err != nil {
					return err
				}
				var exprRead52 tla.Value
				exprRead52, err = iface.Read(fAdvCommitIdxCh0, []tla.Value{exprRead51})
				if err != nil {
					return err
				}
				err = iface.Write(m59, nil, exprRead52)
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
			srvId44 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.srvId")
			m60 := iface.RequireArchetypeResource("AServerFollowerAdvanceCommitIndex.m")
			netEnabled11, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.netEnabled")
			if err != nil {
				return err
			}
			log23, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			acctCh0, err := iface.RequireArchetypeResourceRef("AServerFollowerAdvanceCommitIndex.acctCh")
			if err != nil {
				return err
			}
			var condition112 tla.Value
			condition112, err = iface.Read(srvId44, nil)
			if err != nil {
				return err
			}
			var condition113 tla.Value
			condition113, err = iface.Read(commitIndex6, []tla.Value{condition112})
			if err != nil {
				return err
			}
			var condition114 tla.Value
			condition114, err = iface.Read(m60, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition113, condition114.ApplyFunction(tla.MakeString("mcommitIndex"))).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition115 tla.Value
					condition115, err = iface.Read(srvId44, nil)
					if err != nil {
						return err
					}
					var condition116 tla.Value
					condition116, err = iface.Read(netEnabled11, []tla.Value{condition115})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition116).AsBool() {
						if !tla.ModuleFALSE.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead53 tla.Value
				exprRead53, err = iface.Read(srvId44, nil)
				if err != nil {
					return err
				}
				var exprRead54 tla.Value
				exprRead54, err = iface.Read(commitIndex6, []tla.Value{exprRead53})
				if err != nil {
					return err
				}
				var indexRead3 tla.Value
				indexRead3, err = iface.Read(srvId44, nil)
				if err != nil {
					return err
				}
				err = iface.Write(commitIndex6, []tla.Value{indexRead3}, tla.ModulePlusSymbol(exprRead54, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				var iRead5 tla.Value
				iRead5, err = iface.Read(srvId44, nil)
				if err != nil {
					return err
				}
				var i12 tla.Value = iRead5
				_ = i12
				var kRead0 tla.Value
				kRead0, err = iface.Read(commitIndex6, []tla.Value{i12})
				if err != nil {
					return err
				}
				var k1 tla.Value = kRead0
				_ = k1
				var entryRead4 tla.Value
				entryRead4, err = iface.Read(log23, []tla.Value{i12})
				if err != nil {
					return err
				}
				var entry2 tla.Value = entryRead4.ApplyFunction(k1)
				_ = entry2
				var cmd0 tla.Value = entry2.ApplyFunction(tla.MakeString("cmd"))
				_ = cmd0
				if iface.GetConstant("Debug")().AsBool() {
					tla.MakeTuple(tla.MakeString("ServerAccept"), i12, cmd0).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(acctCh0, []tla.Value{i12}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("mtype"), AcceptMessage(iface)},
					{tla.MakeString("mcmd"), cmd0},
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
			netEnabled12, err := iface.RequireArchetypeResourceRef("AServerCrasher.netEnabled")
			if err != nil {
				return err
			}
			srvId49 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead4 tla.Value
			indexRead4, err = iface.Read(srvId49, nil)
			if err != nil {
				return err
			}
			err = iface.Write(netEnabled12, []tla.Value{indexRead4}, tla.ModuleFALSE)
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
			fd6, err := iface.RequireArchetypeResourceRef("AServerCrasher.fd")
			if err != nil {
				return err
			}
			srvId50 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead5 tla.Value
			indexRead5, err = iface.Read(srvId50, nil)
			if err != nil {
				return err
			}
			err = iface.Write(fd6, []tla.Value{indexRead5}, tla.ModuleTRUE)
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
			err = iface.Write(propCh0, []tla.Value{tla.MakeNumber(1)}, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("mtype"), ProposeMessage(iface)},
				{tla.MakeString("mcmd"), tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("data"), tla.MakeString("hello")},
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

var AServerNetListener = distsys.MPCalArchetype{
	Name:              "AServerNetListener",
	Label:             "AServerNetListener.serverLoop",
	RequiredRefParams: []string{"AServerNetListener.net", "AServerNetListener.netLen", "AServerNetListener.netEnabled", "AServerNetListener.fd", "AServerNetListener.state", "AServerNetListener.currentTerm", "AServerNetListener.log", "AServerNetListener.plog", "AServerNetListener.commitIndex", "AServerNetListener.nextIndex", "AServerNetListener.matchIndex", "AServerNetListener.votedFor", "AServerNetListener.votesResponded", "AServerNetListener.votesGranted", "AServerNetListener.leader", "AServerNetListener.propCh", "AServerNetListener.acctCh", "AServerNetListener.leaderTimeout", "AServerNetListener.appendEntriesCh", "AServerNetListener.becomeLeaderCh", "AServerNetListener.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerNetListener.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerNetListener.idx", tla.MakeNumber(1))
		iface.EnsureArchetypeResourceLocal("AServerNetListener.m", tla.Value{})
	},
}

var AServerPropChListener = distsys.MPCalArchetype{
	Name:              "AServerPropChListener",
	Label:             "AServerPropChListener.serverLoop",
	RequiredRefParams: []string{"AServerPropChListener.net", "AServerPropChListener.netLen", "AServerPropChListener.netEnabled", "AServerPropChListener.fd", "AServerPropChListener.state", "AServerPropChListener.currentTerm", "AServerPropChListener.log", "AServerPropChListener.plog", "AServerPropChListener.commitIndex", "AServerPropChListener.nextIndex", "AServerPropChListener.matchIndex", "AServerPropChListener.votedFor", "AServerPropChListener.votesResponded", "AServerPropChListener.votesGranted", "AServerPropChListener.leader", "AServerPropChListener.propCh", "AServerPropChListener.acctCh", "AServerPropChListener.leaderTimeout", "AServerPropChListener.appendEntriesCh", "AServerPropChListener.becomeLeaderCh", "AServerPropChListener.fAdvCommitIdxCh"},
	RequiredValParams: []string{"AServerPropChListener.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerPropChListener.idx", tla.MakeNumber(1))
		iface.EnsureArchetypeResourceLocal("AServerPropChListener.m", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("AServerRequestVote.idx", tla.MakeNumber(1))
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
		iface.EnsureArchetypeResourceLocal("AServerAppendEntries.idx", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("AServerAdvanceCommitIndex.newCommitIndex", tla.MakeNumber(0))
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
		iface.EnsureArchetypeResourceLocal("AServerFollowerAdvanceCommitIndex.m", tla.Value{})
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
