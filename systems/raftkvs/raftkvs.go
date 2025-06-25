package raftkvs

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
func Put(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("put")
}
func Get(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("get")
}
func ApplyLogEntry(iface distsys.ArchetypeInterface, xentry tla.Value, xsm tla.Value, xsmDomain tla.Value) tla.Value {
	return func() tla.Value {
		var cmd tla.Value = xentry.ApplyFunction(tla.MakeString("cmd"))
		_ = cmd
		return func() tla.Value {
			if tla.ModuleEqualsSymbol(cmd.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
				return tla.MakeTuple(tla.ModuleDoubleAtSignSymbol(tla.ModuleColonGreaterThanSymbol(cmd.ApplyFunction(tla.MakeString("key")), cmd.ApplyFunction(tla.MakeString("value"))), xsm), tla.ModuleUnionSymbol(xsmDomain, tla.MakeSet(cmd.ApplyFunction(tla.MakeString("key")))))
			} else {
				return tla.MakeTuple(xsm, xsmDomain)
			}
		}()
	}()
}
func ApplyLog(iface distsys.ArchetypeInterface, xlog tla.Value, start tla.Value, end tla.Value, xsm0 tla.Value, xsmDomain0 tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleGreaterThanSymbol(start, end).AsBool() {
			return tla.MakeTuple(xsm0, xsmDomain0)
		} else {
			return func() tla.Value {
				var result tla.Value = ApplyLogEntry(iface, xlog.ApplyFunction(start), xsm0, xsmDomain0)
				_ = result
				return ApplyLog(iface, xlog, tla.ModulePlusSymbol(start, tla.MakeNumber(1)), end, result.ApplyFunction(tla.MakeNumber(1)), result.ApplyFunction(tla.MakeNumber(2)))
			}()
		}
	}()
}
func AllReqs(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleUnionSymbol(tla.MakeRecordSet([]tla.RecordField{
		{tla.MakeString("type"), tla.MakeSet(Put(iface))},
		{tla.MakeString("key"), iface.GetConstant("AllStrings")()},
		{tla.MakeString("value"), iface.GetConstant("AllStrings")()},
	}), tla.MakeRecordSet([]tla.RecordField{
		{tla.MakeString("type"), tla.MakeSet(Get(iface))},
		{tla.MakeString("key"), iface.GetConstant("AllStrings")()},
	}))
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
func ClientPutRequest(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("cpq")
}
func ClientPutResponse(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("cpp")
}
func ClientGetRequest(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("cgq")
}
func ClientGetResponse(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeString("cgp")
}
func LastTerm(iface distsys.ArchetypeInterface, xlog0 tla.Value) tla.Value {
	return func() tla.Value {
		if tla.ModuleEqualsSymbol(tla.ModuleLen(xlog0), tla.MakeNumber(0)).AsBool() {
			return tla.MakeNumber(0)
		} else {
			return xlog0.ApplyFunction(tla.ModuleLen(xlog0)).ApplyFunction(tla.MakeString("term"))
		}
	}()
}
func ServerRequestVoteSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(1), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(2), iface.GetConstant("NumServers")()))
}
func ServerAppendEntriesSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(2), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(3), iface.GetConstant("NumServers")()))
}
func ServerAdvanceCommitIndexSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(3), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(4), iface.GetConstant("NumServers")()))
}
func ServerBecomeLeaderSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(4), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModuleAsteriskSymbol(tla.MakeNumber(5), iface.GetConstant("NumServers")()))
}
func ServerCrasherSet(iface distsys.ArchetypeInterface) tla.Value {
	return func() tla.Value {
		if iface.GetConstant("ExploreFail")().AsBool() {
			return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(5), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(5), iface.GetConstant("NumServers")()), iface.GetConstant("MaxNodeFail")()))
		} else {
			return tla.MakeSet()
		}
	}()
}
func ClientSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(6), iface.GetConstant("NumServers")()), tla.MakeNumber(1)), tla.ModulePlusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(6), iface.GetConstant("NumServers")()), iface.GetConstant("NumClients")()))
}
func NodeSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleUnionSymbol(ServerSet(iface), ClientSet(iface))
}
func KeySet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet()
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			m := iface.RequireArchetypeResource("AServer.m")
			net, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition tla.Value
					condition, err = iface.Read(netEnabled, []tla.Value{iface.Self()})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition).AsBool() {
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
				var condition0 tla.Value
				condition0, err = iface.Read(m, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition0.ApplyFunction(tla.MakeString("mdest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((m).mdest) = (self)", distsys.ErrAssertionFailed)
				}
				return iface.Goto("AServer.handleMsg")
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
			netEnabled0, err := iface.RequireArchetypeResourceRef("AServer.netEnabled")
			if err != nil {
				return err
			}
			m1 := iface.RequireArchetypeResource("AServer.m")
			currentTerm, err := iface.RequireArchetypeResourceRef("AServer.currentTerm")
			if err != nil {
				return err
			}
			state, err := iface.RequireArchetypeResourceRef("AServer.state")
			if err != nil {
				return err
			}
			votedFor, err := iface.RequireArchetypeResourceRef("AServer.votedFor")
			if err != nil {
				return err
			}
			leader, err := iface.RequireArchetypeResourceRef("AServer.leader")
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
			leaderTimeout, err := iface.RequireArchetypeResourceRef("AServer.leaderTimeout")
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
			plog, err := iface.RequireArchetypeResourceRef("AServer.plog")
			if err != nil {
				return err
			}
			commitIndex, err := iface.RequireArchetypeResourceRef("AServer.commitIndex")
			if err != nil {
				return err
			}
			sm, err := iface.RequireArchetypeResourceRef("AServer.sm")
			if err != nil {
				return err
			}
			smDomain, err := iface.RequireArchetypeResourceRef("AServer.smDomain")
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
			appendEntriesCh, err := iface.RequireArchetypeResourceRef("AServer.appendEntriesCh")
			if err != nil {
				return err
			}
			if iface.GetConstant("ExploreFail")().AsBool() {
				var condition1 tla.Value
				condition1, err = iface.Read(netEnabled0, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				if tla.ModuleLogicalNotSymbol(condition1).AsBool() {
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
			var condition2 tla.Value
			condition2, err = iface.Read(m1, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition2.ApplyFunction(tla.MakeString("mtype")), RequestVoteRequest(iface)).AsBool() {
				var condition3 tla.Value
				condition3, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var condition4 tla.Value
				condition4, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				if tla.ModuleGreaterThanSymbol(condition3.ApplyFunction(tla.MakeString("mterm")), condition4).AsBool() {
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
				var condition5 tla.Value
				condition5, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				var condition6 tla.Value
				condition6, err = iface.Read(currentTerm, []tla.Value{i1})
				if err != nil {
					return err
				}
				if !tla.ModuleLessThanOrEqualSymbol(condition5.ApplyFunction(tla.MakeString("mterm")), condition6).AsBool() {
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
				switch iface.NextFairnessCounter("AServer.handleMsg.0", 2) {
				case 0:
					var exprRead26 tla.Value
					exprRead26, err = iface.Read(currentTerm, []tla.Value{i1})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.Value{j}, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("mtype"), RequestVoteResponse(iface)},
						{tla.MakeString("mterm"), exprRead26},
						{tla.MakeString("mvoteGranted"), grant},
						{tla.MakeString("msource"), i1},
						{tla.MakeString("mdest"), j},
					}))
					if err != nil {
						return err
					}
					// no statements
				case 1:
					var condition48 tla.Value
					condition48, err = iface.Read(fd, []tla.Value{j})
					if err != nil {
						return err
					}
					if !condition48.AsBool() {
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
					return iface.Goto("AServer.serverLoop")
				} else {
					return iface.Goto("AServer.serverLoop")
				}
				// no statements
				// no statements
			} else {
				var condition7 tla.Value
				condition7, err = iface.Read(m1, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition7.ApplyFunction(tla.MakeString("mtype")), RequestVoteResponse(iface)).AsBool() {
					var condition8 tla.Value
					condition8, err = iface.Read(m1, nil)
					if err != nil {
						return err
					}
					var condition9 tla.Value
					condition9, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
					if err != nil {
						return err
					}
					if tla.ModuleGreaterThanSymbol(condition8.ApplyFunction(tla.MakeString("mterm")), condition9).AsBool() {
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
					if tla.ModuleLessThanSymbol(condition10.ApplyFunction(tla.MakeString("mterm")), condition11).AsBool() {
						// skip
						return iface.Goto("AServer.serverLoop")
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
						var condition12 tla.Value
						condition12, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition13 tla.Value
						condition13, err = iface.Read(currentTerm, []tla.Value{i2})
						if err != nil {
							return err
						}
						if !tla.ModuleEqualsSymbol(condition12.ApplyFunction(tla.MakeString("mterm")), condition13).AsBool() {
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
						var condition14 tla.Value
						condition14, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						if condition14.ApplyFunction(tla.MakeString("mvoteGranted")).AsBool() {
							err = iface.Write(leaderTimeout, nil, iface.GetConstant("LeaderTimeoutReset")())
							if err != nil {
								return err
							}
							var exprRead3 tla.Value
							exprRead3, err = iface.Read(votesGranted, []tla.Value{i2})
							if err != nil {
								return err
							}
							err = iface.Write(votesGranted, []tla.Value{i2}, tla.ModuleUnionSymbol(exprRead3, tla.MakeSet(j0)))
							if err != nil {
								return err
							}
							var condition15 tla.Value
							condition15, err = iface.Read(state, []tla.Value{i2})
							if err != nil {
								return err
							}
							var condition16 tla.Value
							condition16, err = iface.Read(votesGranted, []tla.Value{i2})
							if err != nil {
								return err
							}
							if tla.MakeBool(tla.ModuleEqualsSymbol(condition15, Candidate(iface)).AsBool() && IsQuorum(iface, condition16).AsBool()).AsBool() {
								err = iface.Write(becomeLeaderCh, []tla.Value{i2}, tla.ModuleTRUE)
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
					var condition17 tla.Value
					condition17, err = iface.Read(m1, nil)
					if err != nil {
						return err
					}
					if tla.ModuleEqualsSymbol(condition17.ApplyFunction(tla.MakeString("mtype")), AppendEntriesRequest(iface)).AsBool() {
						var condition18 tla.Value
						condition18, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition19 tla.Value
						condition19, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
						if err != nil {
							return err
						}
						if tla.ModuleGreaterThanSymbol(condition18.ApplyFunction(tla.MakeString("mterm")), condition19).AsBool() {
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
						var condition20 tla.Value
						condition20, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition21 tla.Value
						condition21, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
						}
						if !tla.ModuleLessThanOrEqualSymbol(condition20.ApplyFunction(tla.MakeString("mterm")), condition21).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) <= ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
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
						if tla.ModuleEqualsSymbol(condition22.ApplyFunction(tla.MakeString("mterm")), condition23).AsBool() {
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
						var condition26 tla.Value
						condition26, err = iface.Read(state, []tla.Value{i3})
						if err != nil {
							return err
						}
						if tla.MakeBool(tla.ModuleEqualsSymbol(condition24.ApplyFunction(tla.MakeString("mterm")), condition25).AsBool() && tla.ModuleEqualsSymbol(condition26, Candidate(iface)).AsBool()).AsBool() {
							err = iface.Write(state, []tla.Value{i3}, Follower(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition27 tla.Value
						condition27, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						var condition28 tla.Value
						condition28, err = iface.Read(currentTerm, []tla.Value{i3})
						if err != nil {
							return err
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
						condition31, err = iface.Read(state, []tla.Value{i3})
						if err != nil {
							return err
						}
						if tla.MakeBool(tla.ModuleLessThanSymbol(condition27.ApplyFunction(tla.MakeString("mterm")), condition28).AsBool() || tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition29.ApplyFunction(tla.MakeString("mterm")), condition30).AsBool() && tla.ModuleEqualsSymbol(condition31, Follower(iface)).AsBool()).AsBool() && tla.ModuleLogicalNotSymbol(logOK0).AsBool()).AsBool()).AsBool() {
							switch iface.NextFairnessCounter("AServer.handleMsg.1", 2) {
							case 0:
								var exprRead27 tla.Value
								exprRead27, err = iface.Read(currentTerm, []tla.Value{i3})
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.Value{j1}, tla.MakeRecord([]tla.RecordField{
									{tla.MakeString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeString("mterm"), exprRead27},
									{tla.MakeString("msuccess"), tla.ModuleFALSE},
									{tla.MakeString("mmatchIndex"), tla.MakeNumber(0)},
									{tla.MakeString("msource"), i3},
									{tla.MakeString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServer.serverLoop")
							case 1:
								var condition49 tla.Value
								condition49, err = iface.Read(fd, []tla.Value{j1})
								if err != nil {
									return err
								}
								if !condition49.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServer.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
						} else {
							var condition32 tla.Value
							condition32, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition33 tla.Value
							condition33, err = iface.Read(currentTerm, []tla.Value{i3})
							if err != nil {
								return err
							}
							var condition34 tla.Value
							condition34, err = iface.Read(state, []tla.Value{i3})
							if err != nil {
								return err
							}
							if !tla.MakeBool(tla.MakeBool(tla.ModuleEqualsSymbol(condition32.ApplyFunction(tla.MakeString("mterm")), condition33).AsBool() && tla.ModuleEqualsSymbol(condition34, Follower(iface)).AsBool()).AsBool() && logOK0.AsBool()).AsBool() {
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
							var condition35 tla.Value
							condition35, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition36 tla.Value
							condition36, err = iface.Read(log, []tla.Value{i3})
							if err != nil {
								return err
							}
							if !tla.ModuleLessThanOrEqualSymbol(condition35.ApplyFunction(tla.MakeString("mcommitIndex")), tla.ModuleLen(condition36)).AsBool() {
								return fmt.Errorf("%w: ((m).mcommitIndex) <= (Len((log)[i]))", distsys.ErrAssertionFailed)
							}
							var resultRead tla.Value
							resultRead, err = iface.Read(log, []tla.Value{i3})
							if err != nil {
								return err
							}
							var resultRead0 tla.Value
							resultRead0, err = iface.Read(commitIndex, []tla.Value{i3})
							if err != nil {
								return err
							}
							var resultRead1 tla.Value
							resultRead1, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var resultRead2 tla.Value
							resultRead2, err = iface.Read(sm, []tla.Value{i3})
							if err != nil {
								return err
							}
							var resultRead3 tla.Value
							resultRead3, err = iface.Read(smDomain, []tla.Value{i3})
							if err != nil {
								return err
							}
							var result0 tla.Value = ApplyLog(iface, resultRead, tla.ModulePlusSymbol(resultRead0, tla.MakeNumber(1)), resultRead1.ApplyFunction(tla.MakeString("mcommitIndex")), resultRead2, resultRead3)
							_ = result0
							err = iface.Write(sm, []tla.Value{i3}, result0.ApplyFunction(tla.MakeNumber(1)))
							if err != nil {
								return err
							}
							err = iface.Write(smDomain, []tla.Value{i3}, result0.ApplyFunction(tla.MakeNumber(2)))
							if err != nil {
								return err
							}
							// no statements
							var exprRead13 tla.Value
							exprRead13, err = iface.Read(commitIndex, []tla.Value{i3})
							if err != nil {
								return err
							}
							var exprRead14 tla.Value
							exprRead14, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							err = iface.Write(commitIndex, []tla.Value{i3}, Max(iface, tla.MakeSet(exprRead13, exprRead14.ApplyFunction(tla.MakeString("mcommitIndex")))))
							if err != nil {
								return err
							}
							switch iface.NextFairnessCounter("AServer.handleMsg.2", 2) {
							case 0:
								var exprRead28 tla.Value
								exprRead28, err = iface.Read(currentTerm, []tla.Value{i3})
								if err != nil {
									return err
								}
								var exprRead29 tla.Value
								exprRead29, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								var exprRead30 tla.Value
								exprRead30, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.Value{j1}, tla.MakeRecord([]tla.RecordField{
									{tla.MakeString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeString("mterm"), exprRead28},
									{tla.MakeString("msuccess"), tla.ModuleTRUE},
									{tla.MakeString("mmatchIndex"), tla.ModulePlusSymbol(exprRead29.ApplyFunction(tla.MakeString("mprevLogIndex")), tla.ModuleLen(exprRead30.ApplyFunction(tla.MakeString("mentries"))))},
									{tla.MakeString("msource"), i3},
									{tla.MakeString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServer.serverLoop")
							case 1:
								var condition50 tla.Value
								condition50, err = iface.Read(fd, []tla.Value{j1})
								if err != nil {
									return err
								}
								if !condition50.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServer.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
							// no statements
						}
						// no statements
						// no statements
					} else {
						var condition37 tla.Value
						condition37, err = iface.Read(m1, nil)
						if err != nil {
							return err
						}
						if tla.ModuleEqualsSymbol(condition37.ApplyFunction(tla.MakeString("mtype")), AppendEntriesResponse(iface)).AsBool() {
							var condition38 tla.Value
							condition38, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition39 tla.Value
							condition39, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
							if err != nil {
								return err
							}
							if tla.ModuleGreaterThanSymbol(condition38.ApplyFunction(tla.MakeString("mterm")), condition39).AsBool() {
								var exprRead15 tla.Value
								exprRead15, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								err = iface.Write(currentTerm, []tla.Value{iface.Self()}, exprRead15.ApplyFunction(tla.MakeString("mterm")))
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
							if tla.ModuleLessThanSymbol(condition40.ApplyFunction(tla.MakeString("mterm")), condition41).AsBool() {
								// skip
								return iface.Goto("AServer.serverLoop")
							} else {
								err = iface.Write(leaderTimeout, nil, iface.GetConstant("LeaderTimeoutReset")())
								if err != nil {
									return err
								}
								var i4 tla.Value = iface.Self()
								_ = i4
								var jRead2 tla.Value
								jRead2, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								var j2 tla.Value = jRead2.ApplyFunction(tla.MakeString("msource"))
								_ = j2
								var condition42 tla.Value
								condition42, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								var condition43 tla.Value
								condition43, err = iface.Read(currentTerm, []tla.Value{i4})
								if err != nil {
									return err
								}
								if !tla.ModuleEqualsSymbol(condition42.ApplyFunction(tla.MakeString("mterm")), condition43).AsBool() {
									return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
								}
								var condition44 tla.Value
								condition44, err = iface.Read(m1, nil)
								if err != nil {
									return err
								}
								if condition44.ApplyFunction(tla.MakeString("msuccess")).AsBool() {
									var exprRead16 tla.Value
									exprRead16, err = iface.Read(nextIndex, []tla.Value{i4})
									if err != nil {
										return err
									}
									var exprRead17 tla.Value
									exprRead17, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.Value{i4}, tla.FunctionSubstitution(exprRead16, []tla.FunctionSubstitutionRecord{
										{[]tla.Value{j2}, func(anchor tla.Value) tla.Value {
											return tla.ModulePlusSymbol(exprRead17.ApplyFunction(tla.MakeString("mmatchIndex")), tla.MakeNumber(1))
										}},
									}))
									if err != nil {
										return err
									}
									var exprRead18 tla.Value
									exprRead18, err = iface.Read(matchIndex1, []tla.Value{i4})
									if err != nil {
										return err
									}
									var exprRead19 tla.Value
									exprRead19, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									err = iface.Write(matchIndex1, []tla.Value{i4}, tla.FunctionSubstitution(exprRead18, []tla.FunctionSubstitutionRecord{
										{[]tla.Value{j2}, func(anchor0 tla.Value) tla.Value {
											return exprRead19.ApplyFunction(tla.MakeString("mmatchIndex"))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
								} else {
									var exprRead20 tla.Value
									exprRead20, err = iface.Read(nextIndex, []tla.Value{i4})
									if err != nil {
										return err
									}
									var exprRead21 tla.Value
									exprRead21, err = iface.Read(nextIndex, []tla.Value{i4})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.Value{i4}, tla.FunctionSubstitution(exprRead20, []tla.FunctionSubstitutionRecord{
										{[]tla.Value{j2}, func(anchor1 tla.Value) tla.Value {
											return Max(iface, tla.MakeSet(tla.ModuleMinusSymbol(exprRead21.ApplyFunction(j2), tla.MakeNumber(1)), tla.MakeNumber(1)))
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
							var condition45 tla.Value
							condition45, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							var condition46 tla.Value
							condition46, err = iface.Read(m1, nil)
							if err != nil {
								return err
							}
							if tla.MakeBool(tla.ModuleEqualsSymbol(condition45.ApplyFunction(tla.MakeString("mtype")), ClientPutRequest(iface)).AsBool() || tla.ModuleEqualsSymbol(condition46.ApplyFunction(tla.MakeString("mtype")), ClientGetRequest(iface)).AsBool()).AsBool() {
								var condition47 tla.Value
								condition47, err = iface.Read(state, []tla.Value{iface.Self()})
								if err != nil {
									return err
								}
								if tla.ModuleEqualsSymbol(condition47, Leader(iface)).AsBool() {
									var entryRead tla.Value
									entryRead, err = iface.Read(currentTerm, []tla.Value{iface.Self()})
									if err != nil {
										return err
									}
									var entryRead0 tla.Value
									entryRead0, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var entryRead1 tla.Value
									entryRead1, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var entry tla.Value = tla.MakeRecord([]tla.RecordField{
										{tla.MakeString("term"), entryRead},
										{tla.MakeString("cmd"), entryRead0.ApplyFunction(tla.MakeString("mcmd"))},
										{tla.MakeString("client"), entryRead1.ApplyFunction(tla.MakeString("msource"))},
									})
									_ = entry
									var exprRead22 tla.Value
									exprRead22, err = iface.Read(log, []tla.Value{iface.Self()})
									if err != nil {
										return err
									}
									err = iface.Write(log, []tla.Value{iface.Self()}, tla.ModuleAppend(exprRead22, entry))
									if err != nil {
										return err
									}
									err = iface.Write(plog, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
										{tla.MakeString("cmd"), iface.GetConstant("LogConcat")()},
										{tla.MakeString("entries"), tla.MakeTuple(entry)},
									}))
									if err != nil {
										return err
									}
									err = iface.Write(appendEntriesCh, []tla.Value{iface.Self()}, tla.ModuleTRUE)
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
									// no statements
								} else {
									var i5 tla.Value = iface.Self()
									_ = i5
									var jRead3 tla.Value
									jRead3, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var j3 tla.Value = jRead3.ApplyFunction(tla.MakeString("msource"))
									_ = j3
									var respTypeRead tla.Value
									respTypeRead, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var respType tla.Value = func() tla.Value {
										if tla.ModuleEqualsSymbol(respTypeRead.ApplyFunction(tla.MakeString("mcmd")).ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
											return ClientPutResponse(iface)
										} else {
											return ClientGetResponse(iface)
										}
									}()
									_ = respType
									var exprRead23 tla.Value
									exprRead23, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var exprRead24 tla.Value
									exprRead24, err = iface.Read(m1, nil)
									if err != nil {
										return err
									}
									var exprRead25 tla.Value
									exprRead25, err = iface.Read(leader, []tla.Value{i5})
									if err != nil {
										return err
									}
									err = iface.Write(net0, []tla.Value{j3}, tla.MakeRecord([]tla.RecordField{
										{tla.MakeString("mtype"), respType},
										{tla.MakeString("msuccess"), tla.ModuleFALSE},
										{tla.MakeString("mresponse"), tla.MakeRecord([]tla.RecordField{
											{tla.MakeString("idx"), exprRead23.ApplyFunction(tla.MakeString("mcmd")).ApplyFunction(tla.MakeString("idx"))},
											{tla.MakeString("key"), exprRead24.ApplyFunction(tla.MakeString("mcmd")).ApplyFunction(tla.MakeString("key"))},
										})},
										{tla.MakeString("mleaderHint"), exprRead25},
										{tla.MakeString("msource"), i5},
										{tla.MakeString("mdest"), j3},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServer.serverLoop")
									// no statements
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
			netEnabled1, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netEnabled")
			if err != nil {
				return err
			}
			srvId := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			leaderTimeout2, err := iface.RequireArchetypeResourceRef("AServerRequestVote.leaderTimeout")
			if err != nil {
				return err
			}
			netLen, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netLen")
			if err != nil {
				return err
			}
			state9, err := iface.RequireArchetypeResourceRef("AServerRequestVote.state")
			if err != nil {
				return err
			}
			currentTerm24, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
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
			leader5, err := iface.RequireArchetypeResourceRef("AServerRequestVote.leader")
			if err != nil {
				return err
			}
			idx := iface.RequireArchetypeResource("AServerRequestVote.idx")
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition51 tla.Value
					condition51, err = iface.Read(srvId, nil)
					if err != nil {
						return err
					}
					var condition52 tla.Value
					condition52, err = iface.Read(netEnabled1, []tla.Value{condition51})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition52).AsBool() {
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
				var condition53 tla.Value
				condition53, err = iface.Read(leaderTimeout2, nil)
				if err != nil {
					return err
				}
				if !condition53.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition54 tla.Value
				condition54, err = iface.Read(srvId, nil)
				if err != nil {
					return err
				}
				var condition55 tla.Value
				condition55, err = iface.Read(netLen, []tla.Value{condition54})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition55, tla.MakeNumber(0)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition56 tla.Value
				condition56, err = iface.Read(srvId, nil)
				if err != nil {
					return err
				}
				var condition57 tla.Value
				condition57, err = iface.Read(state9, []tla.Value{condition56})
				if err != nil {
					return err
				}
				if !tla.ModuleInSymbol(condition57, tla.MakeSet(Follower(iface), Candidate(iface))).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead tla.Value
				iRead, err = iface.Read(srvId, nil)
				if err != nil {
					return err
				}
				var i6 tla.Value = iRead
				_ = i6
				err = iface.Write(state9, []tla.Value{i6}, Candidate(iface))
				if err != nil {
					return err
				}
				var exprRead31 tla.Value
				exprRead31, err = iface.Read(currentTerm24, []tla.Value{i6})
				if err != nil {
					return err
				}
				err = iface.Write(currentTerm24, []tla.Value{i6}, tla.ModulePlusSymbol(exprRead31, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(votedFor5, []tla.Value{i6}, i6)
				if err != nil {
					return err
				}
				err = iface.Write(votesResponded1, []tla.Value{i6}, tla.MakeSet(i6))
				if err != nil {
					return err
				}
				err = iface.Write(votesGranted2, []tla.Value{i6}, tla.MakeSet(i6))
				if err != nil {
					return err
				}
				err = iface.Write(leader5, []tla.Value{i6}, Nil(iface))
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint0 tla.Value
					toPrint0, err = iface.Read(currentTerm24, []tla.Value{i6})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ServerTimeout"), i6, toPrint0).PCalPrint()
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
			netEnabled2, err := iface.RequireArchetypeResourceRef("AServerRequestVote.netEnabled")
			if err != nil {
				return err
			}
			srvId3 := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			net4, err := iface.RequireArchetypeResourceRef("AServerRequestVote.net")
			if err != nil {
				return err
			}
			currentTerm27, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
			if err != nil {
				return err
			}
			log13, err := iface.RequireArchetypeResourceRef("AServerRequestVote.log")
			if err != nil {
				return err
			}
			fd2, err := iface.RequireArchetypeResourceRef("AServerRequestVote.fd")
			if err != nil {
				return err
			}
			var condition58 tla.Value
			condition58, err = iface.Read(idx0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition58, iface.GetConstant("NumServers")()).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition59 tla.Value
					condition59, err = iface.Read(srvId3, nil)
					if err != nil {
						return err
					}
					var condition60 tla.Value
					condition60, err = iface.Read(netEnabled2, []tla.Value{condition59})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition60).AsBool() {
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
				var condition61 tla.Value
				condition61, err = iface.Read(idx0, nil)
				if err != nil {
					return err
				}
				var condition62 tla.Value
				condition62, err = iface.Read(srvId3, nil)
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition61, condition62).AsBool() {
					switch iface.NextFairnessCounter("AServerRequestVote.requestVoteLoop.0", 2) {
					case 0:
						var exprRead33 tla.Value
						exprRead33, err = iface.Read(srvId3, nil)
						if err != nil {
							return err
						}
						var exprRead34 tla.Value
						exprRead34, err = iface.Read(currentTerm27, []tla.Value{exprRead33})
						if err != nil {
							return err
						}
						var exprRead35 tla.Value
						exprRead35, err = iface.Read(srvId3, nil)
						if err != nil {
							return err
						}
						var exprRead36 tla.Value
						exprRead36, err = iface.Read(log13, []tla.Value{exprRead35})
						if err != nil {
							return err
						}
						var exprRead37 tla.Value
						exprRead37, err = iface.Read(srvId3, nil)
						if err != nil {
							return err
						}
						var exprRead38 tla.Value
						exprRead38, err = iface.Read(log13, []tla.Value{exprRead37})
						if err != nil {
							return err
						}
						var exprRead39 tla.Value
						exprRead39, err = iface.Read(srvId3, nil)
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
						err = iface.Write(net4, []tla.Value{indexRead0}, tla.MakeRecord([]tla.RecordField{
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
						var condition63 tla.Value
						condition63, err = iface.Read(idx0, nil)
						if err != nil {
							return err
						}
						var condition64 tla.Value
						condition64, err = iface.Read(fd2, []tla.Value{condition63})
						if err != nil {
							return err
						}
						if !condition64.AsBool() {
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
			appendEntriesCh0, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.appendEntriesCh")
			if err != nil {
				return err
			}
			srvId9 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			netEnabled3, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.netEnabled")
			if err != nil {
				return err
			}
			state11, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			idx7 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			var condition65 tla.Value
			condition65, err = iface.Read(srvId9, nil)
			if err != nil {
				return err
			}
			var condition66 tla.Value
			condition66, err = iface.Read(appendEntriesCh0, []tla.Value{condition65})
			if err != nil {
				return err
			}
			if condition66.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition67 tla.Value
					condition67, err = iface.Read(srvId9, nil)
					if err != nil {
						return err
					}
					var condition68 tla.Value
					condition68, err = iface.Read(netEnabled3, []tla.Value{condition67})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition68).AsBool() {
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
				var condition69 tla.Value
				condition69, err = iface.Read(srvId9, nil)
				if err != nil {
					return err
				}
				var condition70 tla.Value
				condition70, err = iface.Read(state11, []tla.Value{condition69})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition70, Leader(iface)).AsBool() {
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
			state12, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			srvId12 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			idx8 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			netEnabled4, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.netEnabled")
			if err != nil {
				return err
			}
			nextIndex4, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.nextIndex")
			if err != nil {
				return err
			}
			log15, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.log")
			if err != nil {
				return err
			}
			net5, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.net")
			if err != nil {
				return err
			}
			currentTerm28, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.currentTerm")
			if err != nil {
				return err
			}
			commitIndex2, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.commitIndex")
			if err != nil {
				return err
			}
			fd3, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.fd")
			if err != nil {
				return err
			}
			var condition71 tla.Value
			condition71, err = iface.Read(srvId12, nil)
			if err != nil {
				return err
			}
			var condition72 tla.Value
			condition72, err = iface.Read(state12, []tla.Value{condition71})
			if err != nil {
				return err
			}
			var condition73 tla.Value
			condition73, err = iface.Read(idx8, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleEqualsSymbol(condition72, Leader(iface)).AsBool() && tla.ModuleLessThanOrEqualSymbol(condition73, iface.GetConstant("NumServers")()).AsBool()).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition74 tla.Value
					condition74, err = iface.Read(srvId12, nil)
					if err != nil {
						return err
					}
					var condition75 tla.Value
					condition75, err = iface.Read(netEnabled4, []tla.Value{condition74})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition75).AsBool() {
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
				var condition76 tla.Value
				condition76, err = iface.Read(idx8, nil)
				if err != nil {
					return err
				}
				var condition77 tla.Value
				condition77, err = iface.Read(srvId12, nil)
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition76, condition77).AsBool() {
					var prevLogIndexRead tla.Value
					prevLogIndexRead, err = iface.Read(srvId12, nil)
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
					prevLogTermRead, err = iface.Read(srvId12, nil)
					if err != nil {
						return err
					}
					var prevLogTermRead0 tla.Value
					prevLogTermRead0, err = iface.Read(log15, []tla.Value{prevLogTermRead})
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
					entriesRead, err = iface.Read(srvId12, nil)
					if err != nil {
						return err
					}
					var entriesRead0 tla.Value
					entriesRead0, err = iface.Read(log15, []tla.Value{entriesRead})
					if err != nil {
						return err
					}
					var entriesRead1 tla.Value
					entriesRead1, err = iface.Read(srvId12, nil)
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
					entriesRead4, err = iface.Read(srvId12, nil)
					if err != nil {
						return err
					}
					var entriesRead5 tla.Value
					entriesRead5, err = iface.Read(log15, []tla.Value{entriesRead4})
					if err != nil {
						return err
					}
					var entries tla.Value = tla.ModuleSubSeq(entriesRead0, entriesRead2.ApplyFunction(entriesRead3), tla.ModuleLen(entriesRead5))
					_ = entries
					switch iface.NextFairnessCounter("AServerAppendEntries.appendEntriesLoop.0", 2) {
					case 0:
						var exprRead42 tla.Value
						exprRead42, err = iface.Read(srvId12, nil)
						if err != nil {
							return err
						}
						var exprRead43 tla.Value
						exprRead43, err = iface.Read(currentTerm28, []tla.Value{exprRead42})
						if err != nil {
							return err
						}
						var exprRead44 tla.Value
						exprRead44, err = iface.Read(srvId12, nil)
						if err != nil {
							return err
						}
						var exprRead45 tla.Value
						exprRead45, err = iface.Read(commitIndex2, []tla.Value{exprRead44})
						if err != nil {
							return err
						}
						var exprRead46 tla.Value
						exprRead46, err = iface.Read(srvId12, nil)
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
						err = iface.Write(net5, []tla.Value{indexRead1}, tla.MakeRecord([]tla.RecordField{
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
						var condition78 tla.Value
						condition78, err = iface.Read(idx8, nil)
						if err != nil {
							return err
						}
						var condition79 tla.Value
						condition79, err = iface.Read(fd3, []tla.Value{condition78})
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
			netEnabled5, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.netEnabled")
			if err != nil {
				return err
			}
			srvId23 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			state13, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.state")
			if err != nil {
				return err
			}
			log18, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			matchIndex3, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.matchIndex")
			if err != nil {
				return err
			}
			currentTerm29, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.currentTerm")
			if err != nil {
				return err
			}
			commitIndex3, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			newCommitIndex := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			if tla.ModuleTRUE.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition80 tla.Value
					condition80, err = iface.Read(srvId23, nil)
					if err != nil {
						return err
					}
					var condition81 tla.Value
					condition81, err = iface.Read(netEnabled5, []tla.Value{condition80})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition81).AsBool() {
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
				var condition82 tla.Value
				condition82, err = iface.Read(srvId23, nil)
				if err != nil {
					return err
				}
				var condition83 tla.Value
				condition83, err = iface.Read(state13, []tla.Value{condition82})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition83, Leader(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead0 tla.Value
				iRead0, err = iface.Read(srvId23, nil)
				if err != nil {
					return err
				}
				var i7 tla.Value = iRead0
				_ = i7
				var maxAgreeIndexRead tla.Value
				maxAgreeIndexRead, err = iface.Read(log18, []tla.Value{i7})
				if err != nil {
					return err
				}
				var maxAgreeIndexRead0 tla.Value
				maxAgreeIndexRead0, err = iface.Read(matchIndex3, []tla.Value{i7})
				if err != nil {
					return err
				}
				var maxAgreeIndex tla.Value = FindMaxAgreeIndex(iface, maxAgreeIndexRead, i7, maxAgreeIndexRead0)
				_ = maxAgreeIndex
				var nCommitIndexRead tla.Value
				nCommitIndexRead, err = iface.Read(log18, []tla.Value{i7})
				if err != nil {
					return err
				}
				var nCommitIndexRead0 tla.Value
				nCommitIndexRead0, err = iface.Read(currentTerm29, []tla.Value{i7})
				if err != nil {
					return err
				}
				var nCommitIndexRead1 tla.Value
				nCommitIndexRead1, err = iface.Read(commitIndex3, []tla.Value{i7})
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
				var condition84 tla.Value
				condition84, err = iface.Read(newCommitIndex, nil)
				if err != nil {
					return err
				}
				var condition85 tla.Value
				condition85, err = iface.Read(commitIndex3, []tla.Value{i7})
				if err != nil {
					return err
				}
				if !tla.ModuleGreaterThanOrEqualSymbol(condition84, condition85).AsBool() {
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
			commitIndex5, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			srvId26 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			newCommitIndex1 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			netEnabled6, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.netEnabled")
			if err != nil {
				return err
			}
			log20, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			sm1, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.sm")
			if err != nil {
				return err
			}
			smDomain1, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.smDomain")
			if err != nil {
				return err
			}
			net6, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.net")
			if err != nil {
				return err
			}
			var condition86 tla.Value
			condition86, err = iface.Read(srvId26, nil)
			if err != nil {
				return err
			}
			var condition87 tla.Value
			condition87, err = iface.Read(commitIndex5, []tla.Value{condition86})
			if err != nil {
				return err
			}
			var condition88 tla.Value
			condition88, err = iface.Read(newCommitIndex1, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition87, condition88).AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition89 tla.Value
					condition89, err = iface.Read(srvId26, nil)
					if err != nil {
						return err
					}
					var condition90 tla.Value
					condition90, err = iface.Read(netEnabled6, []tla.Value{condition89})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition90).AsBool() {
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
				exprRead48, err = iface.Read(srvId26, nil)
				if err != nil {
					return err
				}
				var exprRead49 tla.Value
				exprRead49, err = iface.Read(commitIndex5, []tla.Value{exprRead48})
				if err != nil {
					return err
				}
				var indexRead2 tla.Value
				indexRead2, err = iface.Read(srvId26, nil)
				if err != nil {
					return err
				}
				err = iface.Write(commitIndex5, []tla.Value{indexRead2}, tla.ModulePlusSymbol(exprRead49, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				var iRead1 tla.Value
				iRead1, err = iface.Read(srvId26, nil)
				if err != nil {
					return err
				}
				var i8 tla.Value = iRead1
				_ = i8
				var kRead tla.Value
				kRead, err = iface.Read(commitIndex5, []tla.Value{i8})
				if err != nil {
					return err
				}
				var k0 tla.Value = kRead
				_ = k0
				var entryRead2 tla.Value
				entryRead2, err = iface.Read(log20, []tla.Value{i8})
				if err != nil {
					return err
				}
				var entry0 tla.Value = entryRead2.ApplyFunction(k0)
				_ = entry0
				var cmd0 tla.Value = entry0.ApplyFunction(tla.MakeString("cmd"))
				_ = cmd0
				var respType0 tla.Value = func() tla.Value {
					if tla.ModuleEqualsSymbol(cmd0.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
						return ClientPutResponse(iface)
					} else {
						return ClientGetResponse(iface)
					}
				}()
				_ = respType0
				if tla.ModuleEqualsSymbol(cmd0.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
					var exprRead50 tla.Value
					exprRead50, err = iface.Read(sm1, []tla.Value{i8})
					if err != nil {
						return err
					}
					err = iface.Write(sm1, []tla.Value{i8}, tla.ModuleDoubleAtSignSymbol(tla.ModuleColonGreaterThanSymbol(cmd0.ApplyFunction(tla.MakeString("key")), cmd0.ApplyFunction(tla.MakeString("value"))), exprRead50))
					if err != nil {
						return err
					}
					var exprRead51 tla.Value
					exprRead51, err = iface.Read(smDomain1, []tla.Value{i8})
					if err != nil {
						return err
					}
					err = iface.Write(smDomain1, []tla.Value{i8}, tla.ModuleUnionSymbol(exprRead51, tla.MakeSet(cmd0.ApplyFunction(tla.MakeString("key")))))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var reqOkRead tla.Value
				reqOkRead, err = iface.Read(smDomain1, []tla.Value{i8})
				if err != nil {
					return err
				}
				var reqOk tla.Value = tla.ModuleInSymbol(cmd0.ApplyFunction(tla.MakeString("key")), reqOkRead)
				_ = reqOk
				var exprRead52 tla.Value
				exprRead52, err = iface.Read(sm1, []tla.Value{i8})
				if err != nil {
					return err
				}
				err = iface.Write(net6, []tla.Value{entry0.ApplyFunction(tla.MakeString("client"))}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("mtype"), respType0},
					{tla.MakeString("msuccess"), tla.ModuleTRUE},
					{tla.MakeString("mresponse"), tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("idx"), cmd0.ApplyFunction(tla.MakeString("idx"))},
						{tla.MakeString("key"), cmd0.ApplyFunction(tla.MakeString("key"))},
						{tla.MakeString("value"), func() tla.Value {
							if reqOk.AsBool() {
								return exprRead52.ApplyFunction(cmd0.ApplyFunction(tla.MakeString("key")))
							} else {
								return Nil(iface)
							}
						}()},
						{tla.MakeString("ok"), reqOk},
					})},
					{tla.MakeString("mleaderHint"), i8},
					{tla.MakeString("msource"), i8},
					{tla.MakeString("mdest"), entry0.ApplyFunction(tla.MakeString("client"))},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AServerAdvanceCommitIndex.applyLoop")
				// no statements
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
			srvId31 := iface.RequireArchetypeResource("AServerBecomeLeader.srvId")
			netEnabled7, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.netEnabled")
			if err != nil {
				return err
			}
			state14, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.state")
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
			log21, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.log")
			if err != nil {
				return err
			}
			matchIndex4, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.matchIndex")
			if err != nil {
				return err
			}
			leader6, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.leader")
			if err != nil {
				return err
			}
			appendEntriesCh1, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.appendEntriesCh")
			if err != nil {
				return err
			}
			currentTerm30, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.currentTerm")
			if err != nil {
				return err
			}
			var condition91 tla.Value
			condition91, err = iface.Read(srvId31, nil)
			if err != nil {
				return err
			}
			var condition92 tla.Value
			condition92, err = iface.Read(becomeLeaderCh0, []tla.Value{condition91})
			if err != nil {
				return err
			}
			if condition92.AsBool() {
				if iface.GetConstant("ExploreFail")().AsBool() {
					var condition93 tla.Value
					condition93, err = iface.Read(srvId31, nil)
					if err != nil {
						return err
					}
					var condition94 tla.Value
					condition94, err = iface.Read(netEnabled7, []tla.Value{condition93})
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition94).AsBool() {
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
				var condition95 tla.Value
				condition95, err = iface.Read(srvId31, nil)
				if err != nil {
					return err
				}
				var condition96 tla.Value
				condition96, err = iface.Read(state14, []tla.Value{condition95})
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition96, Candidate(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition97 tla.Value
				condition97, err = iface.Read(srvId31, nil)
				if err != nil {
					return err
				}
				var condition98 tla.Value
				condition98, err = iface.Read(votesGranted3, []tla.Value{condition97})
				if err != nil {
					return err
				}
				if !IsQuorum(iface, condition98).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead2 tla.Value
				iRead2, err = iface.Read(srvId31, nil)
				if err != nil {
					return err
				}
				var i9 tla.Value = iRead2
				_ = i9
				err = iface.Write(state14, []tla.Value{i9}, Leader(iface))
				if err != nil {
					return err
				}
				var exprRead53 tla.Value
				exprRead53, err = iface.Read(log21, []tla.Value{i9})
				if err != nil {
					return err
				}
				err = iface.Write(nextIndex6, []tla.Value{i9}, tla.MakeFunction([]tla.Value{ServerSet(iface)}, func(args []tla.Value) tla.Value {
					var j4 tla.Value = args[0]
					_ = j4
					return tla.ModulePlusSymbol(tla.ModuleLen(exprRead53), tla.MakeNumber(1))
				}))
				if err != nil {
					return err
				}
				err = iface.Write(matchIndex4, []tla.Value{i9}, tla.MakeFunction([]tla.Value{ServerSet(iface)}, func(args0 []tla.Value) tla.Value {
					var j5 tla.Value = args0[0]
					_ = j5
					return tla.MakeNumber(0)
				}))
				if err != nil {
					return err
				}
				err = iface.Write(leader6, []tla.Value{i9}, i9)
				if err != nil {
					return err
				}
				var indexRead3 tla.Value
				indexRead3, err = iface.Read(srvId31, nil)
				if err != nil {
					return err
				}
				err = iface.Write(appendEntriesCh1, []tla.Value{indexRead3}, tla.ModuleTRUE)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint1 tla.Value
					toPrint1, err = iface.Read(currentTerm30, []tla.Value{i9})
					if err != nil {
						return err
					}
					var toPrint2 tla.Value
					toPrint2, err = iface.Read(state14, []tla.Value{i9})
					if err != nil {
						return err
					}
					var toPrint3 tla.Value
					toPrint3, err = iface.Read(leader6, []tla.Value{i9})
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("BecomeLeader"), i9, toPrint1, toPrint2, toPrint3).PCalPrint()
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
				var exprRead54 tla.Value
				exprRead54, err = iface.Read(reqCh, nil)
				if err != nil {
					return err
				}
				err = iface.Write(req, nil, exprRead54)
				if err != nil {
					return err
				}
				var exprRead55 tla.Value
				exprRead55, err = iface.Read(reqIdx, nil)
				if err != nil {
					return err
				}
				err = iface.Write(reqIdx, nil, tla.ModulePlusSymbol(exprRead55, tla.MakeNumber(1)))
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
			leader8 := iface.RequireArchetypeResource("AClient.leader")
			reqIdx1 := iface.RequireArchetypeResource("AClient.reqIdx")
			req0 := iface.RequireArchetypeResource("AClient.req")
			net7, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			fd4, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			var condition99 tla.Value
			condition99, err = iface.Read(leader8, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition99, Nil(iface)).AsBool() {
				var srvRead = ServerSet(iface)
				if srvRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var srv tla.Value = srvRead.SelectElement(iface.NextFairnessCounter("AClient.sndReq.2", uint(srvRead.AsSet().Len())))
				_ = srv
				err = iface.Write(leader8, nil, srv)
				if err != nil {
					return err
				}
				// no statements
				// no statements
			} else {
				// no statements
			}
			if iface.GetConstant("Debug")().AsBool() {
				var toPrint4 tla.Value
				toPrint4, err = iface.Read(leader8, nil)
				if err != nil {
					return err
				}
				var toPrint5 tla.Value
				toPrint5, err = iface.Read(reqIdx1, nil)
				if err != nil {
					return err
				}
				var toPrint6 tla.Value
				toPrint6, err = iface.Read(req0, nil)
				if err != nil {
					return err
				}
				tla.MakeTuple(tla.MakeString("ClientSndReq"), iface.Self(), toPrint4, toPrint5, toPrint6).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			var condition100 tla.Value
			condition100, err = iface.Read(req0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition100.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() {
				switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
				case 0:
					var exprRead56 tla.Value
					exprRead56, err = iface.Read(reqIdx1, nil)
					if err != nil {
						return err
					}
					var exprRead57 tla.Value
					exprRead57, err = iface.Read(req0, nil)
					if err != nil {
						return err
					}
					var exprRead58 tla.Value
					exprRead58, err = iface.Read(req0, nil)
					if err != nil {
						return err
					}
					var exprRead59 tla.Value
					exprRead59, err = iface.Read(leader8, nil)
					if err != nil {
						return err
					}
					var indexRead4 tla.Value
					indexRead4, err = iface.Read(leader8, nil)
					if err != nil {
						return err
					}
					err = iface.Write(net7, []tla.Value{indexRead4}, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("mtype"), ClientPutRequest(iface)},
						{tla.MakeString("mcmd"), tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("idx"), exprRead56},
							{tla.MakeString("type"), Put(iface)},
							{tla.MakeString("key"), exprRead57.ApplyFunction(tla.MakeString("key"))},
							{tla.MakeString("value"), exprRead58.ApplyFunction(tla.MakeString("value"))},
						})},
						{tla.MakeString("msource"), iface.Self()},
						{tla.MakeString("mdest"), exprRead59},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AClient.rcvResp")
				case 1:
					var condition102 tla.Value
					condition102, err = iface.Read(leader8, nil)
					if err != nil {
						return err
					}
					var condition103 tla.Value
					condition103, err = iface.Read(fd4, []tla.Value{condition102})
					if err != nil {
						return err
					}
					if !condition103.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("AClient.rcvResp")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				var condition101 tla.Value
				condition101, err = iface.Read(req0, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition101.ApplyFunction(tla.MakeString("type")), Get(iface)).AsBool() {
					switch iface.NextFairnessCounter("AClient.sndReq.1", 2) {
					case 0:
						var exprRead60 tla.Value
						exprRead60, err = iface.Read(reqIdx1, nil)
						if err != nil {
							return err
						}
						var exprRead61 tla.Value
						exprRead61, err = iface.Read(req0, nil)
						if err != nil {
							return err
						}
						var exprRead62 tla.Value
						exprRead62, err = iface.Read(leader8, nil)
						if err != nil {
							return err
						}
						var indexRead5 tla.Value
						indexRead5, err = iface.Read(leader8, nil)
						if err != nil {
							return err
						}
						err = iface.Write(net7, []tla.Value{indexRead5}, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("mtype"), ClientGetRequest(iface)},
							{tla.MakeString("mcmd"), tla.MakeRecord([]tla.RecordField{
								{tla.MakeString("idx"), exprRead60},
								{tla.MakeString("type"), Get(iface)},
								{tla.MakeString("key"), exprRead61.ApplyFunction(tla.MakeString("key"))},
							})},
							{tla.MakeString("msource"), iface.Self()},
							{tla.MakeString("mdest"), exprRead62},
						}))
						if err != nil {
							return err
						}
						return iface.Goto("AClient.rcvResp")
					case 1:
						var condition104 tla.Value
						condition104, err = iface.Read(leader8, nil)
						if err != nil {
							return err
						}
						var condition105 tla.Value
						condition105, err = iface.Read(fd4, []tla.Value{condition104})
						if err != nil {
							return err
						}
						if !condition105.AsBool() {
							return distsys.ErrCriticalSectionAborted
						}
						return iface.Goto("AClient.rcvResp")
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					return iface.Goto("AClient.rcvResp")
				}
				// no statements
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.rcvResp",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			resp := iface.RequireArchetypeResource("AClient.resp")
			net9, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			leader17 := iface.RequireArchetypeResource("AClient.leader")
			reqIdx4 := iface.RequireArchetypeResource("AClient.reqIdx")
			req6 := iface.RequireArchetypeResource("AClient.req")
			respCh, err := iface.RequireArchetypeResourceRef("AClient.respCh")
			if err != nil {
				return err
			}
			fd6, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			netLen0, err := iface.RequireArchetypeResourceRef("AClient.netLen")
			if err != nil {
				return err
			}
			timeout, err := iface.RequireArchetypeResourceRef("AClient.timeout")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("AClient.rcvResp.0", 2) {
			case 0:
				var exprRead63 tla.Value
				exprRead63, err = iface.Read(net9, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(resp, nil, exprRead63)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint7 tla.Value
					toPrint7, err = iface.Read(leader17, nil)
					if err != nil {
						return err
					}
					var toPrint8 tla.Value
					toPrint8, err = iface.Read(reqIdx4, nil)
					if err != nil {
						return err
					}
					var toPrint9 tla.Value
					toPrint9, err = iface.Read(resp, nil)
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ClientRcvResp"), iface.Self(), toPrint7, toPrint8, toPrint9).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition106 tla.Value
				condition106, err = iface.Read(resp, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition106.ApplyFunction(tla.MakeString("mdest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).mdest) = (self)", distsys.ErrAssertionFailed)
				}
				var condition107 tla.Value
				condition107, err = iface.Read(resp, nil)
				if err != nil {
					return err
				}
				var condition108 tla.Value
				condition108, err = iface.Read(reqIdx4, nil)
				if err != nil {
					return err
				}
				if tla.ModuleNotEqualsSymbol(condition107.ApplyFunction(tla.MakeString("mresponse")).ApplyFunction(tla.MakeString("idx")), condition108).AsBool() {
					return iface.Goto("AClient.rcvResp")
				} else {
					var exprRead64 tla.Value
					exprRead64, err = iface.Read(resp, nil)
					if err != nil {
						return err
					}
					err = iface.Write(leader17, nil, exprRead64.ApplyFunction(tla.MakeString("mleaderHint")))
					if err != nil {
						return err
					}
					var condition109 tla.Value
					condition109, err = iface.Read(req6, nil)
					if err != nil {
						return err
					}
					var condition110 tla.Value
					condition110, err = iface.Read(resp, nil)
					if err != nil {
						return err
					}
					var condition111 tla.Value
					condition111, err = iface.Read(req6, nil)
					if err != nil {
						return err
					}
					var condition112 tla.Value
					condition112, err = iface.Read(resp, nil)
					if err != nil {
						return err
					}
					if !tla.MakeBool(tla.MakeBool(!tla.ModuleEqualsSymbol(condition109.ApplyFunction(tla.MakeString("type")), Get(iface)).AsBool() || tla.ModuleEqualsSymbol(condition110.ApplyFunction(tla.MakeString("mtype")), ClientGetResponse(iface)).AsBool()).AsBool() && tla.MakeBool(!tla.ModuleEqualsSymbol(condition111.ApplyFunction(tla.MakeString("type")), Put(iface)).AsBool() || tla.ModuleEqualsSymbol(condition112.ApplyFunction(tla.MakeString("mtype")), ClientPutResponse(iface)).AsBool()).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)))", distsys.ErrAssertionFailed)
					}
					var condition113 tla.Value
					condition113, err = iface.Read(resp, nil)
					if err != nil {
						return err
					}
					if tla.ModuleLogicalNotSymbol(condition113.ApplyFunction(tla.MakeString("msuccess"))).AsBool() {
						return iface.Goto("AClient.sndReq")
					} else {
						var condition114 tla.Value
						condition114, err = iface.Read(resp, nil)
						if err != nil {
							return err
						}
						var condition115 tla.Value
						condition115, err = iface.Read(reqIdx4, nil)
						if err != nil {
							return err
						}
						var condition116 tla.Value
						condition116, err = iface.Read(resp, nil)
						if err != nil {
							return err
						}
						var condition117 tla.Value
						condition117, err = iface.Read(req6, nil)
						if err != nil {
							return err
						}
						if !tla.MakeBool(tla.ModuleEqualsSymbol(condition114.ApplyFunction(tla.MakeString("mresponse")).ApplyFunction(tla.MakeString("idx")), condition115).AsBool() && tla.ModuleEqualsSymbol(condition116.ApplyFunction(tla.MakeString("mresponse")).ApplyFunction(tla.MakeString("key")), condition117.ApplyFunction(tla.MakeString("key"))).AsBool()).AsBool() {
							return fmt.Errorf("%w: ((((resp).mresponse).idx) = (reqIdx)) /\\ ((((resp).mresponse).key) = ((req).key))", distsys.ErrAssertionFailed)
						}
						var exprRead65 tla.Value
						exprRead65, err = iface.Read(resp, nil)
						if err != nil {
							return err
						}
						err = iface.Write(respCh, nil, exprRead65)
						if err != nil {
							return err
						}
						if iface.GetConstant("Debug")().AsBool() {
							var toPrint10 tla.Value
							toPrint10, err = iface.Read(leader17, nil)
							if err != nil {
								return err
							}
							var toPrint11 tla.Value
							toPrint11, err = iface.Read(reqIdx4, nil)
							if err != nil {
								return err
							}
							var toPrint12 tla.Value
							toPrint12, err = iface.Read(resp, nil)
							if err != nil {
								return err
							}
							tla.MakeTuple(tla.MakeString("ClientRcvChDone"), iface.Self(), toPrint10, toPrint11, toPrint12).PCalPrint()
							return iface.Goto("AClient.clientLoop")
						} else {
							return iface.Goto("AClient.clientLoop")
						}
						// no statements
					}
					// no statements
				}
				// no statements
			case 1:
				var condition118 tla.Value
				condition118, err = iface.Read(leader17, nil)
				if err != nil {
					return err
				}
				var condition119 tla.Value
				condition119, err = iface.Read(fd6, []tla.Value{condition118})
				if err != nil {
					return err
				}
				var condition120 tla.Value
				condition120, err = iface.Read(netLen0, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				var condition121 tla.Value
				condition121, err = iface.Read(timeout, nil)
				if err != nil {
					return err
				}
				if !tla.MakeBool(tla.MakeBool(condition119.AsBool() && tla.ModuleEqualsSymbol(condition120, tla.MakeNumber(0)).AsBool()).AsBool() || condition121.AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint13 tla.Value
					toPrint13, err = iface.Read(leader17, nil)
					if err != nil {
						return err
					}
					var toPrint14 tla.Value
					toPrint14, err = iface.Read(reqIdx4, nil)
					if err != nil {
						return err
					}
					tla.MakeTuple(tla.MakeString("ClientTimeout"), iface.Self(), toPrint13, toPrint14).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(leader17, nil, Nil(iface))
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
	distsys.MPCalCriticalSection{
		Name: "AServerCrasher.serverCrash",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			netEnabled8, err := iface.RequireArchetypeResourceRef("AServerCrasher.netEnabled")
			if err != nil {
				return err
			}
			srvId37 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead6 tla.Value
			indexRead6, err = iface.Read(srvId37, nil)
			if err != nil {
				return err
			}
			err = iface.Write(netEnabled8, []tla.Value{indexRead6}, tla.ModuleFALSE)
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
			fd7, err := iface.RequireArchetypeResourceRef("AServerCrasher.fd")
			if err != nil {
				return err
			}
			srvId38 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead7 tla.Value
			indexRead7, err = iface.Read(srvId38, nil)
			if err != nil {
				return err
			}
			err = iface.Write(fd7, []tla.Value{indexRead7}, tla.ModuleTRUE)
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
)

var AServer = distsys.MPCalArchetype{
	Name:              "AServer",
	Label:             "AServer.serverLoop",
	RequiredRefParams: []string{"AServer.net", "AServer.netLen", "AServer.netEnabled", "AServer.fd", "AServer.state", "AServer.currentTerm", "AServer.log", "AServer.plog", "AServer.commitIndex", "AServer.nextIndex", "AServer.matchIndex", "AServer.votedFor", "AServer.votesResponded", "AServer.votesGranted", "AServer.leader", "AServer.sm", "AServer.smDomain", "AServer.leaderTimeout", "AServer.appendEntriesCh", "AServer.becomeLeaderCh"},
	RequiredValParams: []string{"AServer.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.idx", tla.MakeNumber(1))
		iface.EnsureArchetypeResourceLocal("AServer.m", tla.Value{})
	},
}

var AServerRequestVote = distsys.MPCalArchetype{
	Name:              "AServerRequestVote",
	Label:             "AServerRequestVote.serverRequestVoteLoop",
	RequiredRefParams: []string{"AServerRequestVote.net", "AServerRequestVote.netLen", "AServerRequestVote.netEnabled", "AServerRequestVote.fd", "AServerRequestVote.state", "AServerRequestVote.currentTerm", "AServerRequestVote.log", "AServerRequestVote.plog", "AServerRequestVote.commitIndex", "AServerRequestVote.nextIndex", "AServerRequestVote.matchIndex", "AServerRequestVote.votedFor", "AServerRequestVote.votesResponded", "AServerRequestVote.votesGranted", "AServerRequestVote.leader", "AServerRequestVote.sm", "AServerRequestVote.smDomain", "AServerRequestVote.leaderTimeout", "AServerRequestVote.appendEntriesCh", "AServerRequestVote.becomeLeaderCh"},
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
	RequiredRefParams: []string{"AServerAppendEntries.net", "AServerAppendEntries.netLen", "AServerAppendEntries.netEnabled", "AServerAppendEntries.fd", "AServerAppendEntries.state", "AServerAppendEntries.currentTerm", "AServerAppendEntries.log", "AServerAppendEntries.plog", "AServerAppendEntries.commitIndex", "AServerAppendEntries.nextIndex", "AServerAppendEntries.matchIndex", "AServerAppendEntries.votedFor", "AServerAppendEntries.votesResponded", "AServerAppendEntries.votesGranted", "AServerAppendEntries.leader", "AServerAppendEntries.sm", "AServerAppendEntries.smDomain", "AServerAppendEntries.leaderTimeout", "AServerAppendEntries.appendEntriesCh", "AServerAppendEntries.becomeLeaderCh"},
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
	RequiredRefParams: []string{"AServerAdvanceCommitIndex.net", "AServerAdvanceCommitIndex.netLen", "AServerAdvanceCommitIndex.netEnabled", "AServerAdvanceCommitIndex.fd", "AServerAdvanceCommitIndex.state", "AServerAdvanceCommitIndex.currentTerm", "AServerAdvanceCommitIndex.log", "AServerAdvanceCommitIndex.plog", "AServerAdvanceCommitIndex.commitIndex", "AServerAdvanceCommitIndex.nextIndex", "AServerAdvanceCommitIndex.matchIndex", "AServerAdvanceCommitIndex.votedFor", "AServerAdvanceCommitIndex.votesResponded", "AServerAdvanceCommitIndex.votesGranted", "AServerAdvanceCommitIndex.leader", "AServerAdvanceCommitIndex.sm", "AServerAdvanceCommitIndex.smDomain", "AServerAdvanceCommitIndex.leaderTimeout", "AServerAdvanceCommitIndex.appendEntriesCh", "AServerAdvanceCommitIndex.becomeLeaderCh"},
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
	RequiredRefParams: []string{"AServerBecomeLeader.net", "AServerBecomeLeader.netLen", "AServerBecomeLeader.netEnabled", "AServerBecomeLeader.fd", "AServerBecomeLeader.state", "AServerBecomeLeader.currentTerm", "AServerBecomeLeader.log", "AServerBecomeLeader.plog", "AServerBecomeLeader.commitIndex", "AServerBecomeLeader.nextIndex", "AServerBecomeLeader.matchIndex", "AServerBecomeLeader.votedFor", "AServerBecomeLeader.votesResponded", "AServerBecomeLeader.votesGranted", "AServerBecomeLeader.leader", "AServerBecomeLeader.sm", "AServerBecomeLeader.smDomain", "AServerBecomeLeader.leaderTimeout", "AServerBecomeLeader.appendEntriesCh", "AServerBecomeLeader.becomeLeaderCh"},
	RequiredValParams: []string{"AServerBecomeLeader.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
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
		iface.EnsureArchetypeResourceLocal("AClient.leader", Nil(iface))
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AClient.reqIdx", tla.MakeNumber(0))
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
