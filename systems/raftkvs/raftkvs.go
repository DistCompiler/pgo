package raftkvs

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
func Put(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("put")
}
func Get(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("get")
}
func ApplyLogEntry(iface distsys.ArchetypeInterface, xentry tla.TLAValue, xsm tla.TLAValue, xsmDomain tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		var cmd tla.TLAValue = xentry.ApplyFunction(tla.MakeTLAString("cmd"))
		_ = cmd
		return func() tla.TLAValue {
			if tla.TLA_EqualsSymbol(cmd.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
				return tla.MakeTLATuple(tla.TLA_DoubleAtSignSymbol(xsm, tla.TLA_ColonGreaterThanSymbol(cmd.ApplyFunction(tla.MakeTLAString("key")), cmd.ApplyFunction(tla.MakeTLAString("value")))), tla.TLA_UnionSymbol(xsmDomain, tla.MakeTLASet(cmd.ApplyFunction(tla.MakeTLAString("key")))))
			} else {
				return tla.MakeTLATuple(xsm, xsmDomain)
			}
		}()
	}()
}
func ApplyLog(iface distsys.ArchetypeInterface, xlog tla.TLAValue, start tla.TLAValue, end tla.TLAValue, xsm0 tla.TLAValue, xsmDomain0 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_GreaterThanSymbol(start, end).AsBool() {
			return tla.MakeTLATuple(xsm0, xsmDomain0)
		} else {
			return func() tla.TLAValue {
				var result tla.TLAValue = ApplyLogEntry(iface, xlog.ApplyFunction(start), xsm0, xsmDomain0)
				_ = result
				return ApplyLog(iface, xlog, tla.TLA_PlusSymbol(start, tla.MakeTLANumber(1)), end, result.ApplyFunction(tla.MakeTLANumber(1)), result.ApplyFunction(tla.MakeTLANumber(2)))
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
func ClientPutRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("cpq")
}
func ClientPutResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("cpp")
}
func ClientGetRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("cgq")
}
func ClientGetResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("cgp")
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
func LastTerm(iface distsys.ArchetypeInterface, xlog0 tla.TLAValue) tla.TLAValue {
	return func() tla.TLAValue {
		if tla.TLA_EqualsSymbol(tla.TLA_Len(xlog0), tla.MakeTLANumber(0)).AsBool() {
			return tla.MakeTLANumber(0)
		} else {
			return xlog0.ApplyFunction(tla.TLA_Len(xlog0)).ApplyFunction(tla.MakeTLAString("term"))
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
func ServerHandlerSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()), tla.TLA_AsteriskSymbol(iface.GetConstant("NumHandlers")(), iface.GetConstant("NumServers")())))
}
func ServerCrasherSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return func() tla.TLAValue {
		if iface.GetConstant("ExploreFail")().AsBool() {
			return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()), tla.TLA_AsteriskSymbol(iface.GetConstant("NumHandlers")(), iface.GetConstant("NumServers")())), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()), tla.TLA_AsteriskSymbol(iface.GetConstant("NumHandlers")(), iface.GetConstant("NumServers")())), iface.GetConstant("MaxNodeFail")()))
		} else {
			return tla.MakeTLASet()
		}
	}()
}
func ServerOffset(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(5), iface.GetConstant("NumServers")()), tla.TLA_AsteriskSymbol(iface.GetConstant("NumHandlers")(), iface.GetConstant("NumServers")())), iface.GetConstant("MaxNodeFail")())
}
func ClientSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(ServerOffset(iface), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(ServerOffset(iface), iface.GetConstant("NumClients")()))
}
func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_UnionSymbol(ServerSet(iface), ClientSet(iface))
}
func KeySet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet()
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServerListener.listenerLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m := iface.RequireArchetypeResource("AServerListener.m")
			net, err := iface.RequireArchetypeResourceRef("AServerListener.net")
			if err != nil {
				return err
			}
			srvId := iface.RequireArchetypeResource("AServerListener.srvId")
			handlerCh, err := iface.RequireArchetypeResourceRef("AServerListener.handlerCh")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var exprRead tla.TLAValue
				exprRead, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(net, []tla.TLAValue{exprRead})
				if err != nil {
					return err
				}
				err = iface.Write(m, []tla.TLAValue{}, exprRead0)
				if err != nil {
					return err
				}
				var condition tla.TLAValue
				condition, err = iface.Read(m, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition0 tla.TLAValue
				condition0, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("mdest")), condition0).AsBool() {
					return fmt.Errorf("%w: ((m).mdest) = (srvId)", distsys.ErrAssertionFailed)
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(m, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead tla.TLAValue
				indexRead, err = iface.Read(srvId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(handlerCh, []tla.TLAValue{indexRead}, exprRead1)
				if err != nil {
					return err
				}
				return iface.Goto("AServerListener.listenerLoop")
			} else {
				return iface.Goto("AServerListener.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerListener.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerHandler.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m2 := iface.RequireArchetypeResource("AServerHandler.m")
			handlerCh0, err := iface.RequireArchetypeResourceRef("AServerHandler.handlerCh")
			if err != nil {
				return err
			}
			srvId2 := iface.RequireArchetypeResource("AServerHandler.srvId")
			if tla.TLA_TRUE.AsBool() {
				var exprRead2 tla.TLAValue
				exprRead2, err = iface.Read(srvId2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead3 tla.TLAValue
				exprRead3, err = iface.Read(handlerCh0, []tla.TLAValue{exprRead2})
				if err != nil {
					return err
				}
				err = iface.Write(m2, []tla.TLAValue{}, exprRead3)
				if err != nil {
					return err
				}
				return iface.Goto("AServerHandler.handleMsg")
			} else {
				return iface.Goto("AServerHandler.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerHandler.handleMsg",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			m3 := iface.RequireArchetypeResource("AServerHandler.m")
			currentTerm, err := iface.RequireArchetypeResourceRef("AServerHandler.currentTerm")
			if err != nil {
				return err
			}
			srvId3 := iface.RequireArchetypeResource("AServerHandler.srvId")
			state, err := iface.RequireArchetypeResourceRef("AServerHandler.state")
			if err != nil {
				return err
			}
			votedFor, err := iface.RequireArchetypeResourceRef("AServerHandler.votedFor")
			if err != nil {
				return err
			}
			leader, err := iface.RequireArchetypeResourceRef("AServerHandler.leader")
			if err != nil {
				return err
			}
			log, err := iface.RequireArchetypeResourceRef("AServerHandler.log")
			if err != nil {
				return err
			}
			net0, err := iface.RequireArchetypeResourceRef("AServerHandler.net")
			if err != nil {
				return err
			}
			fd, err := iface.RequireArchetypeResourceRef("AServerHandler.fd")
			if err != nil {
				return err
			}
			votesResponded, err := iface.RequireArchetypeResourceRef("AServerHandler.votesResponded")
			if err != nil {
				return err
			}
			votesGranted, err := iface.RequireArchetypeResourceRef("AServerHandler.votesGranted")
			if err != nil {
				return err
			}
			becomeLeaderCh, err := iface.RequireArchetypeResourceRef("AServerHandler.becomeLeaderCh")
			if err != nil {
				return err
			}
			leaderTimeout, err := iface.RequireArchetypeResourceRef("AServerHandler.leaderTimeout")
			if err != nil {
				return err
			}
			plog, err := iface.RequireArchetypeResourceRef("AServerHandler.plog")
			if err != nil {
				return err
			}
			commitIndex, err := iface.RequireArchetypeResourceRef("AServerHandler.commitIndex")
			if err != nil {
				return err
			}
			sm, err := iface.RequireArchetypeResourceRef("AServerHandler.sm")
			if err != nil {
				return err
			}
			smDomain, err := iface.RequireArchetypeResourceRef("AServerHandler.smDomain")
			if err != nil {
				return err
			}
			nextIndex, err := iface.RequireArchetypeResourceRef("AServerHandler.nextIndex")
			if err != nil {
				return err
			}
			matchIndex1, err := iface.RequireArchetypeResourceRef("AServerHandler.matchIndex")
			if err != nil {
				return err
			}
			var condition1 tla.TLAValue
			condition1, err = iface.Read(m3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition1.ApplyFunction(tla.MakeTLAString("mtype")), RequestVoteRequest(iface)).AsBool() {
				var condition2 tla.TLAValue
				condition2, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition3 tla.TLAValue
				condition3, err = iface.Read(srvId3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition4 tla.TLAValue
				condition4, err = iface.Read(currentTerm, []tla.TLAValue{condition3})
				if err != nil {
					return err
				}
				if tla.TLA_GreaterThanSymbol(condition2.ApplyFunction(tla.MakeTLAString("mterm")), condition4).AsBool() {
					var exprRead4 tla.TLAValue
					exprRead4, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead0 tla.TLAValue
					indexRead0, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(currentTerm, []tla.TLAValue{indexRead0}, exprRead4.ApplyFunction(tla.MakeTLAString("mterm")))
					if err != nil {
						return err
					}
					var indexRead1 tla.TLAValue
					indexRead1, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(state, []tla.TLAValue{indexRead1}, Follower(iface))
					if err != nil {
						return err
					}
					var indexRead2 tla.TLAValue
					indexRead2, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(votedFor, []tla.TLAValue{indexRead2}, Nil(iface))
					if err != nil {
						return err
					}
					var indexRead3 tla.TLAValue
					indexRead3, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(leader, []tla.TLAValue{indexRead3}, Nil(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var iRead tla.TLAValue
				iRead, err = iface.Read(srvId3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i1 tla.TLAValue = iRead
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
				grantRead0, err = iface.Read(currentTerm, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				var grantRead1 tla.TLAValue
				grantRead1, err = iface.Read(srvId3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var grantRead2 tla.TLAValue
				grantRead2, err = iface.Read(votedFor, []tla.TLAValue{grantRead1})
				if err != nil {
					return err
				}
				var grant tla.TLAValue = tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(grantRead.ApplyFunction(tla.MakeTLAString("mterm")), grantRead0).AsBool() && logOK.AsBool()).AsBool() && tla.TLA_InSymbol(grantRead2, tla.MakeTLASet(Nil(iface), j)).AsBool())
				_ = grant
				var condition5 tla.TLAValue
				condition5, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition6 tla.TLAValue
				condition6, err = iface.Read(currentTerm, []tla.TLAValue{i1})
				if err != nil {
					return err
				}
				if !tla.TLA_LessThanOrEqualSymbol(condition5.ApplyFunction(tla.MakeTLAString("mterm")), condition6).AsBool() {
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
				switch iface.NextFairnessCounter("AServerHandler.handleMsg.0", 2) {
				case 0:
					var exprRead31 tla.TLAValue
					exprRead31, err = iface.Read(currentTerm, []tla.TLAValue{i1})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.TLAValue{j}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("mtype"), RequestVoteResponse(iface)},
						{tla.MakeTLAString("mterm"), exprRead31},
						{tla.MakeTLAString("mvoteGranted"), grant},
						{tla.MakeTLAString("msource"), i1},
						{tla.MakeTLAString("mdest"), j},
					}))
					if err != nil {
						return err
					}
					// no statements
				case 1:
					var condition54 tla.TLAValue
					condition54, err = iface.Read(fd, []tla.TLAValue{j})
					if err != nil {
						return err
					}
					if !condition54.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					// no statements
				default:
					panic("current branch of either matches no code paths!")
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint tla.TLAValue
					toPrint, err = iface.Read(currentTerm, []tla.TLAValue{i1})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("HandleRequestVoteRequest"), i1, j, toPrint, grant).PCalPrint()
					return iface.Goto("AServerHandler.serverLoop")
				} else {
					return iface.Goto("AServerHandler.serverLoop")
				}
				// no statements
				// no statements
			} else {
				var condition7 tla.TLAValue
				condition7, err = iface.Read(m3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition7.ApplyFunction(tla.MakeTLAString("mtype")), RequestVoteResponse(iface)).AsBool() {
					var condition8 tla.TLAValue
					condition8, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition9 tla.TLAValue
					condition9, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition10 tla.TLAValue
					condition10, err = iface.Read(currentTerm, []tla.TLAValue{condition9})
					if err != nil {
						return err
					}
					if tla.TLA_GreaterThanSymbol(condition8.ApplyFunction(tla.MakeTLAString("mterm")), condition10).AsBool() {
						var exprRead5 tla.TLAValue
						exprRead5, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead4 tla.TLAValue
						indexRead4, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(currentTerm, []tla.TLAValue{indexRead4}, exprRead5.ApplyFunction(tla.MakeTLAString("mterm")))
						if err != nil {
							return err
						}
						var indexRead5 tla.TLAValue
						indexRead5, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(state, []tla.TLAValue{indexRead5}, Follower(iface))
						if err != nil {
							return err
						}
						var indexRead6 tla.TLAValue
						indexRead6, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(votedFor, []tla.TLAValue{indexRead6}, Nil(iface))
						if err != nil {
							return err
						}
						var indexRead7 tla.TLAValue
						indexRead7, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(leader, []tla.TLAValue{indexRead7}, Nil(iface))
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					var condition11 tla.TLAValue
					condition11, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition12 tla.TLAValue
					condition12, err = iface.Read(srvId3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition13 tla.TLAValue
					condition13, err = iface.Read(currentTerm, []tla.TLAValue{condition12})
					if err != nil {
						return err
					}
					if tla.TLA_LessThanSymbol(condition11.ApplyFunction(tla.MakeTLAString("mterm")), condition13).AsBool() {
						// skip
						return iface.Goto("AServerHandler.serverLoop")
					} else {
						var iRead0 tla.TLAValue
						iRead0, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var i2 tla.TLAValue = iRead0
						_ = i2
						var jRead0 tla.TLAValue
						jRead0, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var j0 tla.TLAValue = jRead0.ApplyFunction(tla.MakeTLAString("msource"))
						_ = j0
						var condition14 tla.TLAValue
						condition14, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition15 tla.TLAValue
						condition15, err = iface.Read(currentTerm, []tla.TLAValue{i2})
						if err != nil {
							return err
						}
						if !tla.TLA_EqualsSymbol(condition14.ApplyFunction(tla.MakeTLAString("mterm")), condition15).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
						var exprRead6 tla.TLAValue
						exprRead6, err = iface.Read(votesResponded, []tla.TLAValue{i2})
						if err != nil {
							return err
						}
						err = iface.Write(votesResponded, []tla.TLAValue{i2}, tla.TLA_UnionSymbol(exprRead6, tla.MakeTLASet(j0)))
						if err != nil {
							return err
						}
						var condition16 tla.TLAValue
						condition16, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if condition16.ApplyFunction(tla.MakeTLAString("mvoteGranted")).AsBool() {
							var exprRead7 tla.TLAValue
							exprRead7, err = iface.Read(votesGranted, []tla.TLAValue{i2})
							if err != nil {
								return err
							}
							err = iface.Write(votesGranted, []tla.TLAValue{i2}, tla.TLA_UnionSymbol(exprRead7, tla.MakeTLASet(j0)))
							if err != nil {
								return err
							}
							var condition17 tla.TLAValue
							condition17, err = iface.Read(state, []tla.TLAValue{i2})
							if err != nil {
								return err
							}
							var condition18 tla.TLAValue
							condition18, err = iface.Read(votesGranted, []tla.TLAValue{i2})
							if err != nil {
								return err
							}
							if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition17, Candidate(iface)).AsBool() && IsQuorum(iface, condition18).AsBool()).AsBool() {
								err = iface.Write(becomeLeaderCh, []tla.TLAValue{i2}, tla.TLA_TRUE)
								if err != nil {
									return err
								}
								return iface.Goto("AServerHandler.serverLoop")
							} else {
								return iface.Goto("AServerHandler.serverLoop")
							}
							// no statements
						} else {
							return iface.Goto("AServerHandler.serverLoop")
						}
						// no statements
						// no statements
					}
					// no statements
				} else {
					var condition19 tla.TLAValue
					condition19, err = iface.Read(m3, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_EqualsSymbol(condition19.ApplyFunction(tla.MakeTLAString("mtype")), AppendEntriesRequest(iface)).AsBool() {
						var condition20 tla.TLAValue
						condition20, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition21 tla.TLAValue
						condition21, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition22 tla.TLAValue
						condition22, err = iface.Read(currentTerm, []tla.TLAValue{condition21})
						if err != nil {
							return err
						}
						if tla.TLA_GreaterThanSymbol(condition20.ApplyFunction(tla.MakeTLAString("mterm")), condition22).AsBool() {
							var exprRead8 tla.TLAValue
							exprRead8, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var indexRead8 tla.TLAValue
							indexRead8, err = iface.Read(srvId3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(currentTerm, []tla.TLAValue{indexRead8}, exprRead8.ApplyFunction(tla.MakeTLAString("mterm")))
							if err != nil {
								return err
							}
							var indexRead9 tla.TLAValue
							indexRead9, err = iface.Read(srvId3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(state, []tla.TLAValue{indexRead9}, Follower(iface))
							if err != nil {
								return err
							}
							var indexRead10 tla.TLAValue
							indexRead10, err = iface.Read(srvId3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(votedFor, []tla.TLAValue{indexRead10}, Nil(iface))
							if err != nil {
								return err
							}
							var indexRead11 tla.TLAValue
							indexRead11, err = iface.Read(srvId3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(leader, []tla.TLAValue{indexRead11}, Nil(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var iRead1 tla.TLAValue
						iRead1, err = iface.Read(srvId3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var i3 tla.TLAValue = iRead1
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
						var condition23 tla.TLAValue
						condition23, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition24 tla.TLAValue
						condition24, err = iface.Read(currentTerm, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if !tla.TLA_LessThanOrEqualSymbol(condition23.ApplyFunction(tla.MakeTLAString("mterm")), condition24).AsBool() {
							return fmt.Errorf("%w: ((m).mterm) <= ((currentTerm)[i])", distsys.ErrAssertionFailed)
						}
						var condition25 tla.TLAValue
						condition25, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition26 tla.TLAValue
						condition26, err = iface.Read(currentTerm, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if tla.TLA_EqualsSymbol(condition25.ApplyFunction(tla.MakeTLAString("mterm")), condition26).AsBool() {
							var exprRead9 tla.TLAValue
							exprRead9, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(leader, []tla.TLAValue{i3}, exprRead9.ApplyFunction(tla.MakeTLAString("msource")))
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
						var condition27 tla.TLAValue
						condition27, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition28 tla.TLAValue
						condition28, err = iface.Read(currentTerm, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var condition29 tla.TLAValue
						condition29, err = iface.Read(state, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition27.ApplyFunction(tla.MakeTLAString("mterm")), condition28).AsBool() && tla.TLA_EqualsSymbol(condition29, Candidate(iface)).AsBool()).AsBool() {
							err = iface.Write(state, []tla.TLAValue{i3}, Follower(iface))
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var condition30 tla.TLAValue
						condition30, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition31 tla.TLAValue
						condition31, err = iface.Read(currentTerm, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var condition32 tla.TLAValue
						condition32, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition33 tla.TLAValue
						condition33, err = iface.Read(currentTerm, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						var condition34 tla.TLAValue
						condition34, err = iface.Read(state, []tla.TLAValue{i3})
						if err != nil {
							return err
						}
						if tla.MakeTLABool(tla.TLA_LessThanSymbol(condition30.ApplyFunction(tla.MakeTLAString("mterm")), condition31).AsBool() || tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition32.ApplyFunction(tla.MakeTLAString("mterm")), condition33).AsBool() && tla.TLA_EqualsSymbol(condition34, Follower(iface)).AsBool()).AsBool() && tla.TLA_LogicalNotSymbol(logOK0).AsBool()).AsBool()).AsBool() {
							switch iface.NextFairnessCounter("AServerHandler.handleMsg.1", 2) {
							case 0:
								var exprRead32 tla.TLAValue
								exprRead32, err = iface.Read(currentTerm, []tla.TLAValue{i3})
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.TLAValue{j1}, tla.MakeTLARecord([]tla.TLARecordField{
									{tla.MakeTLAString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeTLAString("mterm"), exprRead32},
									{tla.MakeTLAString("msuccess"), tla.TLA_FALSE},
									{tla.MakeTLAString("mmatchIndex"), tla.MakeTLANumber(0)},
									{tla.MakeTLAString("msource"), i3},
									{tla.MakeTLAString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServerHandler.serverLoop")
							case 1:
								var condition55 tla.TLAValue
								condition55, err = iface.Read(fd, []tla.TLAValue{j1})
								if err != nil {
									return err
								}
								if !condition55.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServerHandler.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
						} else {
							var condition35 tla.TLAValue
							condition35, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition36 tla.TLAValue
							condition36, err = iface.Read(currentTerm, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var condition37 tla.TLAValue
							condition37, err = iface.Read(state, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							if !tla.MakeTLABool(tla.MakeTLABool(tla.TLA_EqualsSymbol(condition35.ApplyFunction(tla.MakeTLAString("mterm")), condition36).AsBool() && tla.TLA_EqualsSymbol(condition37, Follower(iface)).AsBool()).AsBool() && logOK0.AsBool()).AsBool() {
								return fmt.Errorf("%w: ((((m).mterm) = ((currentTerm)[i])) /\\ (((state)[i]) = (Follower))) /\\ (logOK)", distsys.ErrAssertionFailed)
							}
							var indexRead12 tla.TLAValue
							indexRead12, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var index0 tla.TLAValue = tla.TLA_PlusSymbol(indexRead12.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.MakeTLANumber(1))
							_ = index0
							var exprRead10 tla.TLAValue
							exprRead10, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var exprRead11 tla.TLAValue
							exprRead11, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(plog, []tla.TLAValue{i3}, tla.MakeTLARecord([]tla.TLARecordField{
								{tla.MakeTLAString("cmd"), iface.GetConstant("LogPop")()},
								{tla.MakeTLAString("cnt"), tla.TLA_MinusSymbol(tla.TLA_Len(exprRead10), exprRead11.ApplyFunction(tla.MakeTLAString("mprevLogIndex")))},
							}))
							if err != nil {
								return err
							}
							var exprRead12 tla.TLAValue
							exprRead12, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var exprRead13 tla.TLAValue
							exprRead13, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(log, []tla.TLAValue{i3}, tla.TLA_SubSeq(exprRead12, tla.MakeTLANumber(1), exprRead13.ApplyFunction(tla.MakeTLAString("mprevLogIndex"))))
							if err != nil {
								return err
							}
							var exprRead14 tla.TLAValue
							exprRead14, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(plog, []tla.TLAValue{i3}, tla.MakeTLARecord([]tla.TLARecordField{
								{tla.MakeTLAString("cmd"), iface.GetConstant("LogConcat")()},
								{tla.MakeTLAString("entries"), exprRead14.ApplyFunction(tla.MakeTLAString("mentries"))},
							}))
							if err != nil {
								return err
							}
							var exprRead15 tla.TLAValue
							exprRead15, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var exprRead16 tla.TLAValue
							exprRead16, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(log, []tla.TLAValue{i3}, tla.TLA_OSymbol(exprRead15, exprRead16.ApplyFunction(tla.MakeTLAString("mentries"))))
							if err != nil {
								return err
							}
							var condition38 tla.TLAValue
							condition38, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition39 tla.TLAValue
							condition39, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							if !tla.TLA_LessThanOrEqualSymbol(condition38.ApplyFunction(tla.MakeTLAString("mcommitIndex")), tla.TLA_Len(condition39)).AsBool() {
								return fmt.Errorf("%w: ((m).mcommitIndex) <= (Len((log)[i]))", distsys.ErrAssertionFailed)
							}
							var resultRead tla.TLAValue
							resultRead, err = iface.Read(log, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var resultRead0 tla.TLAValue
							resultRead0, err = iface.Read(commitIndex, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var resultRead1 tla.TLAValue
							resultRead1, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var resultRead2 tla.TLAValue
							resultRead2, err = iface.Read(sm, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var resultRead3 tla.TLAValue
							resultRead3, err = iface.Read(smDomain, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var result0 tla.TLAValue = ApplyLog(iface, resultRead, tla.TLA_PlusSymbol(resultRead0, tla.MakeTLANumber(1)), resultRead1.ApplyFunction(tla.MakeTLAString("mcommitIndex")), resultRead2, resultRead3)
							_ = result0
							err = iface.Write(sm, []tla.TLAValue{i3}, result0.ApplyFunction(tla.MakeTLANumber(1)))
							if err != nil {
								return err
							}
							err = iface.Write(smDomain, []tla.TLAValue{i3}, result0.ApplyFunction(tla.MakeTLANumber(2)))
							if err != nil {
								return err
							}
							// no statements
							var exprRead17 tla.TLAValue
							exprRead17, err = iface.Read(commitIndex, []tla.TLAValue{i3})
							if err != nil {
								return err
							}
							var exprRead18 tla.TLAValue
							exprRead18, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(commitIndex, []tla.TLAValue{i3}, Max(iface, tla.MakeTLASet(exprRead17, exprRead18.ApplyFunction(tla.MakeTLAString("mcommitIndex")))))
							if err != nil {
								return err
							}
							switch iface.NextFairnessCounter("AServerHandler.handleMsg.2", 2) {
							case 0:
								var exprRead33 tla.TLAValue
								exprRead33, err = iface.Read(currentTerm, []tla.TLAValue{i3})
								if err != nil {
									return err
								}
								var exprRead34 tla.TLAValue
								exprRead34, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var exprRead35 tla.TLAValue
								exprRead35, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(net0, []tla.TLAValue{j1}, tla.MakeTLARecord([]tla.TLARecordField{
									{tla.MakeTLAString("mtype"), AppendEntriesResponse(iface)},
									{tla.MakeTLAString("mterm"), exprRead33},
									{tla.MakeTLAString("msuccess"), tla.TLA_TRUE},
									{tla.MakeTLAString("mmatchIndex"), tla.TLA_PlusSymbol(exprRead34.ApplyFunction(tla.MakeTLAString("mprevLogIndex")), tla.TLA_Len(exprRead35.ApplyFunction(tla.MakeTLAString("mentries"))))},
									{tla.MakeTLAString("msource"), i3},
									{tla.MakeTLAString("mdest"), j1},
								}))
								if err != nil {
									return err
								}
								return iface.Goto("AServerHandler.serverLoop")
							case 1:
								var condition56 tla.TLAValue
								condition56, err = iface.Read(fd, []tla.TLAValue{j1})
								if err != nil {
									return err
								}
								if !condition56.AsBool() {
									return distsys.ErrCriticalSectionAborted
								}
								return iface.Goto("AServerHandler.serverLoop")
							default:
								panic("current branch of either matches no code paths!")
							}
							// no statements
							// no statements
						}
						// no statements
						// no statements
					} else {
						var condition40 tla.TLAValue
						condition40, err = iface.Read(m3, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if tla.TLA_EqualsSymbol(condition40.ApplyFunction(tla.MakeTLAString("mtype")), AppendEntriesResponse(iface)).AsBool() {
							var condition41 tla.TLAValue
							condition41, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition42 tla.TLAValue
							condition42, err = iface.Read(srvId3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition43 tla.TLAValue
							condition43, err = iface.Read(currentTerm, []tla.TLAValue{condition42})
							if err != nil {
								return err
							}
							if tla.TLA_GreaterThanSymbol(condition41.ApplyFunction(tla.MakeTLAString("mterm")), condition43).AsBool() {
								var exprRead19 tla.TLAValue
								exprRead19, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var indexRead13 tla.TLAValue
								indexRead13, err = iface.Read(srvId3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(currentTerm, []tla.TLAValue{indexRead13}, exprRead19.ApplyFunction(tla.MakeTLAString("mterm")))
								if err != nil {
									return err
								}
								var indexRead14 tla.TLAValue
								indexRead14, err = iface.Read(srvId3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(state, []tla.TLAValue{indexRead14}, Follower(iface))
								if err != nil {
									return err
								}
								var indexRead15 tla.TLAValue
								indexRead15, err = iface.Read(srvId3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(votedFor, []tla.TLAValue{indexRead15}, Nil(iface))
								if err != nil {
									return err
								}
								var indexRead16 tla.TLAValue
								indexRead16, err = iface.Read(srvId3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								err = iface.Write(leader, []tla.TLAValue{indexRead16}, Nil(iface))
								if err != nil {
									return err
								}
								// no statements
							} else {
								// no statements
							}
							var condition44 tla.TLAValue
							condition44, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition45 tla.TLAValue
							condition45, err = iface.Read(srvId3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition46 tla.TLAValue
							condition46, err = iface.Read(currentTerm, []tla.TLAValue{condition45})
							if err != nil {
								return err
							}
							if tla.TLA_LessThanSymbol(condition44.ApplyFunction(tla.MakeTLAString("mterm")), condition46).AsBool() {
								// skip
								return iface.Goto("AServerHandler.serverLoop")
							} else {
								var iRead2 tla.TLAValue
								iRead2, err = iface.Read(srvId3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var i4 tla.TLAValue = iRead2
								_ = i4
								var jRead2 tla.TLAValue
								jRead2, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var j2 tla.TLAValue = jRead2.ApplyFunction(tla.MakeTLAString("msource"))
								_ = j2
								var condition47 tla.TLAValue
								condition47, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var condition48 tla.TLAValue
								condition48, err = iface.Read(currentTerm, []tla.TLAValue{i4})
								if err != nil {
									return err
								}
								if !tla.TLA_EqualsSymbol(condition47.ApplyFunction(tla.MakeTLAString("mterm")), condition48).AsBool() {
									return fmt.Errorf("%w: ((m).mterm) = ((currentTerm)[i])", distsys.ErrAssertionFailed)
								}
								var condition49 tla.TLAValue
								condition49, err = iface.Read(m3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								if condition49.ApplyFunction(tla.MakeTLAString("msuccess")).AsBool() {
									var exprRead20 tla.TLAValue
									exprRead20, err = iface.Read(nextIndex, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									var exprRead21 tla.TLAValue
									exprRead21, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.TLAValue{i4}, tla.TLAFunctionSubstitution(exprRead20, []tla.TLAFunctionSubstitutionRecord{
										{[]tla.TLAValue{j2}, func(anchor tla.TLAValue) tla.TLAValue {
											return tla.TLA_PlusSymbol(exprRead21.ApplyFunction(tla.MakeTLAString("mmatchIndex")), tla.MakeTLANumber(1))
										}},
									}))
									if err != nil {
										return err
									}
									var exprRead22 tla.TLAValue
									exprRead22, err = iface.Read(matchIndex1, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									var exprRead23 tla.TLAValue
									exprRead23, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(matchIndex1, []tla.TLAValue{i4}, tla.TLAFunctionSubstitution(exprRead22, []tla.TLAFunctionSubstitutionRecord{
										{[]tla.TLAValue{j2}, func(anchor0 tla.TLAValue) tla.TLAValue {
											return exprRead23.ApplyFunction(tla.MakeTLAString("mmatchIndex"))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServerHandler.serverLoop")
								} else {
									var exprRead24 tla.TLAValue
									exprRead24, err = iface.Read(nextIndex, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									var exprRead25 tla.TLAValue
									exprRead25, err = iface.Read(nextIndex, []tla.TLAValue{i4})
									if err != nil {
										return err
									}
									err = iface.Write(nextIndex, []tla.TLAValue{i4}, tla.TLAFunctionSubstitution(exprRead24, []tla.TLAFunctionSubstitutionRecord{
										{[]tla.TLAValue{j2}, func(anchor1 tla.TLAValue) tla.TLAValue {
											return Max(iface, tla.MakeTLASet(tla.TLA_MinusSymbol(exprRead25.ApplyFunction(j2), tla.MakeTLANumber(1)), tla.MakeTLANumber(1)))
										}},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServerHandler.serverLoop")
								}
								// no statements
								// no statements
							}
							// no statements
						} else {
							var condition50 tla.TLAValue
							condition50, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var condition51 tla.TLAValue
							condition51, err = iface.Read(m3, []tla.TLAValue{})
							if err != nil {
								return err
							}
							if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition50.ApplyFunction(tla.MakeTLAString("mtype")), ClientPutRequest(iface)).AsBool() || tla.TLA_EqualsSymbol(condition51.ApplyFunction(tla.MakeTLAString("mtype")), ClientGetRequest(iface)).AsBool()).AsBool() {
								if iface.GetConstant("Debug")().AsBool() {
									var toPrint0 tla.TLAValue
									toPrint0, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var toPrint1 tla.TLAValue
									toPrint1, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var toPrint2 tla.TLAValue
									toPrint2, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var toPrint3 tla.TLAValue
									toPrint3, err = iface.Read(currentTerm, []tla.TLAValue{toPrint2})
									if err != nil {
										return err
									}
									var toPrint4 tla.TLAValue
									toPrint4, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var toPrint5 tla.TLAValue
									toPrint5, err = iface.Read(state, []tla.TLAValue{toPrint4})
									if err != nil {
										return err
									}
									tla.MakeTLATuple(tla.MakeTLAString("HandleClientRequest"), toPrint0, toPrint1.ApplyFunction(tla.MakeTLAString("msource")), toPrint3, toPrint5).PCalPrint()
									// no statements
								} else {
									// no statements
								}
								var condition52 tla.TLAValue
								condition52, err = iface.Read(srvId3, []tla.TLAValue{})
								if err != nil {
									return err
								}
								var condition53 tla.TLAValue
								condition53, err = iface.Read(state, []tla.TLAValue{condition52})
								if err != nil {
									return err
								}
								if tla.TLA_EqualsSymbol(condition53, Leader(iface)).AsBool() {
									var entryRead tla.TLAValue
									entryRead, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entryRead0 tla.TLAValue
									entryRead0, err = iface.Read(currentTerm, []tla.TLAValue{entryRead})
									if err != nil {
										return err
									}
									var entryRead1 tla.TLAValue
									entryRead1, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entryRead2 tla.TLAValue
									entryRead2, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var entry tla.TLAValue = tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("term"), entryRead0},
										{tla.MakeTLAString("cmd"), entryRead1.ApplyFunction(tla.MakeTLAString("mcmd"))},
										{tla.MakeTLAString("client"), entryRead2.ApplyFunction(tla.MakeTLAString("msource"))},
									})
									_ = entry
									var exprRead26 tla.TLAValue
									exprRead26, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var exprRead27 tla.TLAValue
									exprRead27, err = iface.Read(log, []tla.TLAValue{exprRead26})
									if err != nil {
										return err
									}
									var indexRead17 tla.TLAValue
									indexRead17, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(log, []tla.TLAValue{indexRead17}, tla.TLA_Append(exprRead27, entry))
									if err != nil {
										return err
									}
									var indexRead18 tla.TLAValue
									indexRead18, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									err = iface.Write(plog, []tla.TLAValue{indexRead18}, tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("cmd"), iface.GetConstant("LogConcat")()},
										{tla.MakeTLAString("entries"), tla.MakeTLATuple(entry)},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServerHandler.serverLoop")
									// no statements
								} else {
									var iRead3 tla.TLAValue
									iRead3, err = iface.Read(srvId3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var i5 tla.TLAValue = iRead3
									_ = i5
									var jRead3 tla.TLAValue
									jRead3, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var j3 tla.TLAValue = jRead3.ApplyFunction(tla.MakeTLAString("msource"))
									_ = j3
									var respTypeRead tla.TLAValue
									respTypeRead, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var respType tla.TLAValue = func() tla.TLAValue {
										if tla.TLA_EqualsSymbol(respTypeRead.ApplyFunction(tla.MakeTLAString("mcmd")).ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
											return ClientPutResponse(iface)
										} else {
											return ClientGetResponse(iface)
										}
									}()
									_ = respType
									var exprRead28 tla.TLAValue
									exprRead28, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var exprRead29 tla.TLAValue
									exprRead29, err = iface.Read(m3, []tla.TLAValue{})
									if err != nil {
										return err
									}
									var exprRead30 tla.TLAValue
									exprRead30, err = iface.Read(leader, []tla.TLAValue{i5})
									if err != nil {
										return err
									}
									err = iface.Write(net0, []tla.TLAValue{j3}, tla.MakeTLARecord([]tla.TLARecordField{
										{tla.MakeTLAString("mtype"), respType},
										{tla.MakeTLAString("msuccess"), tla.TLA_FALSE},
										{tla.MakeTLAString("mresponse"), tla.MakeTLARecord([]tla.TLARecordField{
											{tla.MakeTLAString("idx"), exprRead28.ApplyFunction(tla.MakeTLAString("mcmd")).ApplyFunction(tla.MakeTLAString("idx"))},
											{tla.MakeTLAString("key"), exprRead29.ApplyFunction(tla.MakeTLAString("mcmd")).ApplyFunction(tla.MakeTLAString("key"))},
										})},
										{tla.MakeTLAString("mleaderHint"), exprRead30},
										{tla.MakeTLAString("msource"), i5},
										{tla.MakeTLAString("mdest"), j3},
									}))
									if err != nil {
										return err
									}
									return iface.Goto("AServerHandler.serverLoop")
									// no statements
								}
								// no statements
							} else {
								return iface.Goto("AServerHandler.serverLoop")
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
		Name: "AServerHandler.Done",
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
			srvId39 := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			state10, err := iface.RequireArchetypeResourceRef("AServerRequestVote.state")
			if err != nil {
				return err
			}
			currentTerm25, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
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
			if tla.TLA_TRUE.AsBool() {
				var condition57 tla.TLAValue
				condition57, err = iface.Read(leaderTimeout0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !condition57.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition58 tla.TLAValue
				condition58, err = iface.Read(srvId39, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition59 tla.TLAValue
				condition59, err = iface.Read(netLen, []tla.TLAValue{condition58})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition59, tla.MakeTLANumber(0)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition60 tla.TLAValue
				condition60, err = iface.Read(srvId39, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition61 tla.TLAValue
				condition61, err = iface.Read(state10, []tla.TLAValue{condition60})
				if err != nil {
					return err
				}
				if !tla.TLA_InSymbol(condition61, tla.MakeTLASet(Follower(iface), Candidate(iface))).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead4 tla.TLAValue
				iRead4, err = iface.Read(srvId39, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i6 tla.TLAValue = iRead4
				_ = i6
				err = iface.Write(state10, []tla.TLAValue{i6}, Candidate(iface))
				if err != nil {
					return err
				}
				var exprRead36 tla.TLAValue
				exprRead36, err = iface.Read(currentTerm25, []tla.TLAValue{i6})
				if err != nil {
					return err
				}
				err = iface.Write(currentTerm25, []tla.TLAValue{i6}, tla.TLA_PlusSymbol(exprRead36, tla.MakeTLANumber(1)))
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
				err = iface.Write(leader5, []tla.TLAValue{i6}, Nil(iface))
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint6 tla.TLAValue
					toPrint6, err = iface.Read(currentTerm25, []tla.TLAValue{i6})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ServerTimeout"), i6, toPrint6).PCalPrint()
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
			srvId42 := iface.RequireArchetypeResource("AServerRequestVote.srvId")
			net4, err := iface.RequireArchetypeResourceRef("AServerRequestVote.net")
			if err != nil {
				return err
			}
			currentTerm28, err := iface.RequireArchetypeResourceRef("AServerRequestVote.currentTerm")
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
			var condition62 tla.TLAValue
			condition62, err = iface.Read(idx0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition62, iface.GetConstant("NumServers")()).AsBool() {
				var condition63 tla.TLAValue
				condition63, err = iface.Read(idx0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition64 tla.TLAValue
				condition64, err = iface.Read(srvId42, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition63, condition64).AsBool() {
					switch iface.NextFairnessCounter("AServerRequestVote.requestVoteLoop.0", 2) {
					case 0:
						var exprRead38 tla.TLAValue
						exprRead38, err = iface.Read(srvId42, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead39 tla.TLAValue
						exprRead39, err = iface.Read(currentTerm28, []tla.TLAValue{exprRead38})
						if err != nil {
							return err
						}
						var exprRead40 tla.TLAValue
						exprRead40, err = iface.Read(srvId42, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead41 tla.TLAValue
						exprRead41, err = iface.Read(log13, []tla.TLAValue{exprRead40})
						if err != nil {
							return err
						}
						var exprRead42 tla.TLAValue
						exprRead42, err = iface.Read(srvId42, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead43 tla.TLAValue
						exprRead43, err = iface.Read(log13, []tla.TLAValue{exprRead42})
						if err != nil {
							return err
						}
						var exprRead44 tla.TLAValue
						exprRead44, err = iface.Read(srvId42, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead45 tla.TLAValue
						exprRead45, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead19 tla.TLAValue
						indexRead19, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net4, []tla.TLAValue{indexRead19}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), RequestVoteRequest(iface)},
							{tla.MakeTLAString("mterm"), exprRead39},
							{tla.MakeTLAString("mlastLogTerm"), LastTerm(iface, exprRead41)},
							{tla.MakeTLAString("mlastLogIndex"), tla.TLA_Len(exprRead43)},
							{tla.MakeTLAString("msource"), exprRead44},
							{tla.MakeTLAString("mdest"), exprRead45},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition65 tla.TLAValue
						condition65, err = iface.Read(idx0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition66 tla.TLAValue
						condition66, err = iface.Read(fd2, []tla.TLAValue{condition65})
						if err != nil {
							return err
						}
						if !condition66.AsBool() {
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
				var exprRead37 tla.TLAValue
				exprRead37, err = iface.Read(idx0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead37, tla.MakeTLANumber(1)))
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
			state12, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			srvId47 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			idx7 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
			var condition67 tla.TLAValue
			condition67, err = iface.Read(appendEntriesCh, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if condition67.AsBool() {
				var condition68 tla.TLAValue
				condition68, err = iface.Read(srvId47, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition69 tla.TLAValue
				condition69, err = iface.Read(state12, []tla.TLAValue{condition68})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition69, Leader(iface)).AsBool() {
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
			state13, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.state")
			if err != nil {
				return err
			}
			srvId48 := iface.RequireArchetypeResource("AServerAppendEntries.srvId")
			idx8 := iface.RequireArchetypeResource("AServerAppendEntries.idx")
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
			currentTerm29, err := iface.RequireArchetypeResourceRef("AServerAppendEntries.currentTerm")
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
			var condition70 tla.TLAValue
			condition70, err = iface.Read(srvId48, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition71 tla.TLAValue
			condition71, err = iface.Read(state13, []tla.TLAValue{condition70})
			if err != nil {
				return err
			}
			var condition72 tla.TLAValue
			condition72, err = iface.Read(idx8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition71, Leader(iface)).AsBool() && tla.TLA_LessThanOrEqualSymbol(condition72, iface.GetConstant("NumServers")()).AsBool()).AsBool() {
				var condition73 tla.TLAValue
				condition73, err = iface.Read(idx8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition74 tla.TLAValue
				condition74, err = iface.Read(srvId48, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition73, condition74).AsBool() {
					var prevLogIndexRead tla.TLAValue
					prevLogIndexRead, err = iface.Read(srvId48, []tla.TLAValue{})
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
					prevLogTermRead, err = iface.Read(srvId48, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var prevLogTermRead0 tla.TLAValue
					prevLogTermRead0, err = iface.Read(log15, []tla.TLAValue{prevLogTermRead})
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
					var entriesRead tla.TLAValue
					entriesRead, err = iface.Read(srvId48, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entriesRead0 tla.TLAValue
					entriesRead0, err = iface.Read(log15, []tla.TLAValue{entriesRead})
					if err != nil {
						return err
					}
					var entriesRead1 tla.TLAValue
					entriesRead1, err = iface.Read(srvId48, []tla.TLAValue{})
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
					var entriesRead4 tla.TLAValue
					entriesRead4, err = iface.Read(srvId48, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var entriesRead5 tla.TLAValue
					entriesRead5, err = iface.Read(log15, []tla.TLAValue{entriesRead4})
					if err != nil {
						return err
					}
					var entries tla.TLAValue = tla.TLA_SubSeq(entriesRead0, entriesRead2.ApplyFunction(entriesRead3), tla.TLA_Len(entriesRead5))
					_ = entries
					switch iface.NextFairnessCounter("AServerAppendEntries.appendEntriesLoop.0", 2) {
					case 0:
						var exprRead47 tla.TLAValue
						exprRead47, err = iface.Read(srvId48, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead48 tla.TLAValue
						exprRead48, err = iface.Read(currentTerm29, []tla.TLAValue{exprRead47})
						if err != nil {
							return err
						}
						var exprRead49 tla.TLAValue
						exprRead49, err = iface.Read(srvId48, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead50 tla.TLAValue
						exprRead50, err = iface.Read(commitIndex2, []tla.TLAValue{exprRead49})
						if err != nil {
							return err
						}
						var exprRead51 tla.TLAValue
						exprRead51, err = iface.Read(srvId48, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead52 tla.TLAValue
						exprRead52, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead20 tla.TLAValue
						indexRead20, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net5, []tla.TLAValue{indexRead20}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), AppendEntriesRequest(iface)},
							{tla.MakeTLAString("mterm"), exprRead48},
							{tla.MakeTLAString("mprevLogIndex"), prevLogIndex},
							{tla.MakeTLAString("mprevLogTerm"), prevLogTerm},
							{tla.MakeTLAString("mentries"), entries},
							{tla.MakeTLAString("mcommitIndex"), exprRead50},
							{tla.MakeTLAString("msource"), exprRead51},
							{tla.MakeTLAString("mdest"), exprRead52},
						}))
						if err != nil {
							return err
						}
						// no statements
					case 1:
						var condition75 tla.TLAValue
						condition75, err = iface.Read(idx8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition76 tla.TLAValue
						condition76, err = iface.Read(fd3, []tla.TLAValue{condition75})
						if err != nil {
							return err
						}
						if !condition76.AsBool() {
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
				var exprRead46 tla.TLAValue
				exprRead46, err = iface.Read(idx8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(idx8, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead46, tla.MakeTLANumber(1)))
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
			state14, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.state")
			if err != nil {
				return err
			}
			srvId58 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			log18, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.log")
			if err != nil {
				return err
			}
			matchIndex3, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.matchIndex")
			if err != nil {
				return err
			}
			currentTerm30, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.currentTerm")
			if err != nil {
				return err
			}
			commitIndex3, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			newCommitIndex := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
			if tla.TLA_TRUE.AsBool() {
				var condition77 tla.TLAValue
				condition77, err = iface.Read(srvId58, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition78 tla.TLAValue
				condition78, err = iface.Read(state14, []tla.TLAValue{condition77})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition78, Leader(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead5 tla.TLAValue
				iRead5, err = iface.Read(srvId58, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i7 tla.TLAValue = iRead5
				_ = i7
				var maxAgreeIndexRead tla.TLAValue
				maxAgreeIndexRead, err = iface.Read(log18, []tla.TLAValue{i7})
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
				nCommitIndexRead, err = iface.Read(log18, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var nCommitIndexRead0 tla.TLAValue
				nCommitIndexRead0, err = iface.Read(currentTerm30, []tla.TLAValue{i7})
				if err != nil {
					return err
				}
				var nCommitIndexRead1 tla.TLAValue
				nCommitIndexRead1, err = iface.Read(commitIndex3, []tla.TLAValue{i7})
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
			commitIndex4, err := iface.RequireArchetypeResourceRef("AServerAdvanceCommitIndex.commitIndex")
			if err != nil {
				return err
			}
			srvId60 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.srvId")
			newCommitIndex0 := iface.RequireArchetypeResource("AServerAdvanceCommitIndex.newCommitIndex")
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
			var condition79 tla.TLAValue
			condition79, err = iface.Read(srvId60, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition80 tla.TLAValue
			condition80, err = iface.Read(commitIndex4, []tla.TLAValue{condition79})
			if err != nil {
				return err
			}
			var condition81 tla.TLAValue
			condition81, err = iface.Read(newCommitIndex0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition80, condition81).AsBool() {
				var exprRead53 tla.TLAValue
				exprRead53, err = iface.Read(srvId60, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead54 tla.TLAValue
				exprRead54, err = iface.Read(commitIndex4, []tla.TLAValue{exprRead53})
				if err != nil {
					return err
				}
				var indexRead21 tla.TLAValue
				indexRead21, err = iface.Read(srvId60, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(commitIndex4, []tla.TLAValue{indexRead21}, tla.TLA_PlusSymbol(exprRead54, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				var iRead6 tla.TLAValue
				iRead6, err = iface.Read(srvId60, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i8 tla.TLAValue = iRead6
				_ = i8
				var kRead tla.TLAValue
				kRead, err = iface.Read(commitIndex4, []tla.TLAValue{i8})
				if err != nil {
					return err
				}
				var k0 tla.TLAValue = kRead
				_ = k0
				var entryRead3 tla.TLAValue
				entryRead3, err = iface.Read(log20, []tla.TLAValue{i8})
				if err != nil {
					return err
				}
				var entry0 tla.TLAValue = entryRead3.ApplyFunction(k0)
				_ = entry0
				var cmd0 tla.TLAValue = entry0.ApplyFunction(tla.MakeTLAString("cmd"))
				_ = cmd0
				var respType0 tla.TLAValue = func() tla.TLAValue {
					if tla.TLA_EqualsSymbol(cmd0.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
						return ClientPutResponse(iface)
					} else {
						return ClientGetResponse(iface)
					}
				}()
				_ = respType0
				if tla.TLA_EqualsSymbol(cmd0.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
					var exprRead55 tla.TLAValue
					exprRead55, err = iface.Read(sm1, []tla.TLAValue{i8})
					if err != nil {
						return err
					}
					err = iface.Write(sm1, []tla.TLAValue{i8}, tla.TLA_DoubleAtSignSymbol(exprRead55, tla.TLA_ColonGreaterThanSymbol(cmd0.ApplyFunction(tla.MakeTLAString("key")), cmd0.ApplyFunction(tla.MakeTLAString("value")))))
					if err != nil {
						return err
					}
					var exprRead56 tla.TLAValue
					exprRead56, err = iface.Read(smDomain1, []tla.TLAValue{i8})
					if err != nil {
						return err
					}
					err = iface.Write(smDomain1, []tla.TLAValue{i8}, tla.TLA_UnionSymbol(exprRead56, tla.MakeTLASet(cmd0.ApplyFunction(tla.MakeTLAString("key")))))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var reqOkRead tla.TLAValue
				reqOkRead, err = iface.Read(smDomain1, []tla.TLAValue{i8})
				if err != nil {
					return err
				}
				var reqOk tla.TLAValue = tla.TLA_InSymbol(cmd0.ApplyFunction(tla.MakeTLAString("key")), reqOkRead)
				_ = reqOk
				var exprRead57 tla.TLAValue
				exprRead57, err = iface.Read(sm1, []tla.TLAValue{i8})
				if err != nil {
					return err
				}
				err = iface.Write(net6, []tla.TLAValue{entry0.ApplyFunction(tla.MakeTLAString("client"))}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("mtype"), respType0},
					{tla.MakeTLAString("msuccess"), tla.TLA_TRUE},
					{tla.MakeTLAString("mresponse"), tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("idx"), cmd0.ApplyFunction(tla.MakeTLAString("idx"))},
						{tla.MakeTLAString("key"), cmd0.ApplyFunction(tla.MakeTLAString("key"))},
						{tla.MakeTLAString("value"), func() tla.TLAValue {
							if reqOk.AsBool() {
								return exprRead57.ApplyFunction(cmd0.ApplyFunction(tla.MakeTLAString("key")))
							} else {
								return Nil(iface)
							}
						}()},
						{tla.MakeTLAString("ok"), reqOk},
					})},
					{tla.MakeTLAString("mleaderHint"), i8},
					{tla.MakeTLAString("msource"), i8},
					{tla.MakeTLAString("mdest"), entry0.ApplyFunction(tla.MakeTLAString("client"))},
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
			srvId64 := iface.RequireArchetypeResource("AServerBecomeLeader.srvId")
			state15, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.state")
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
			appendEntriesCh0, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.appendEntriesCh")
			if err != nil {
				return err
			}
			currentTerm31, err := iface.RequireArchetypeResourceRef("AServerBecomeLeader.currentTerm")
			if err != nil {
				return err
			}
			var condition82 tla.TLAValue
			condition82, err = iface.Read(srvId64, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition83 tla.TLAValue
			condition83, err = iface.Read(becomeLeaderCh0, []tla.TLAValue{condition82})
			if err != nil {
				return err
			}
			if condition83.AsBool() {
				var condition84 tla.TLAValue
				condition84, err = iface.Read(srvId64, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition85 tla.TLAValue
				condition85, err = iface.Read(state15, []tla.TLAValue{condition84})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition85, Candidate(iface)).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var condition86 tla.TLAValue
				condition86, err = iface.Read(srvId64, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition87 tla.TLAValue
				condition87, err = iface.Read(votesGranted3, []tla.TLAValue{condition86})
				if err != nil {
					return err
				}
				if !IsQuorum(iface, condition87).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var iRead7 tla.TLAValue
				iRead7, err = iface.Read(srvId64, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var i9 tla.TLAValue = iRead7
				_ = i9
				err = iface.Write(state15, []tla.TLAValue{i9}, Leader(iface))
				if err != nil {
					return err
				}
				var exprRead58 tla.TLAValue
				exprRead58, err = iface.Read(log21, []tla.TLAValue{i9})
				if err != nil {
					return err
				}
				err = iface.Write(nextIndex6, []tla.TLAValue{i9}, tla.MakeTLAFunction([]tla.TLAValue{ServerSet(iface)}, func(args []tla.TLAValue) tla.TLAValue {
					var j4 tla.TLAValue = args[0]
					_ = j4
					return tla.TLA_PlusSymbol(tla.TLA_Len(exprRead58), tla.MakeTLANumber(1))
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
				err = iface.Write(leader6, []tla.TLAValue{i9}, i9)
				if err != nil {
					return err
				}
				err = iface.Write(appendEntriesCh0, []tla.TLAValue{}, tla.TLA_TRUE)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint7 tla.TLAValue
					toPrint7, err = iface.Read(currentTerm31, []tla.TLAValue{i9})
					if err != nil {
						return err
					}
					var toPrint8 tla.TLAValue
					toPrint8, err = iface.Read(state15, []tla.TLAValue{i9})
					if err != nil {
						return err
					}
					var toPrint9 tla.TLAValue
					toPrint9, err = iface.Read(leader6, []tla.TLAValue{i9})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("BecomeLeader"), i9, toPrint7, toPrint8, toPrint9).PCalPrint()
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
			if tla.TLA_TRUE.AsBool() {
				var exprRead59 tla.TLAValue
				exprRead59, err = iface.Read(reqCh, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.TLAValue{}, exprRead59)
				if err != nil {
					return err
				}
				var exprRead60 tla.TLAValue
				exprRead60, err = iface.Read(reqIdx, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(reqIdx, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead60, tla.MakeTLANumber(1)))
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
			var condition88 tla.TLAValue
			condition88, err = iface.Read(leader8, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition88, Nil(iface)).AsBool() {
				var srvRead = ServerSet(iface)
				if srvRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var srv tla.TLAValue = srvRead.SelectElement(iface.NextFairnessCounter("AClient.sndReq.2", uint(srvRead.AsSet().Len())))
				_ = srv
				err = iface.Write(leader8, []tla.TLAValue{}, srv)
				if err != nil {
					return err
				}
				// no statements
				// no statements
			} else {
				// no statements
			}
			if iface.GetConstant("Debug")().AsBool() {
				var toPrint10 tla.TLAValue
				toPrint10, err = iface.Read(leader8, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var toPrint11 tla.TLAValue
				toPrint11, err = iface.Read(reqIdx1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var toPrint12 tla.TLAValue
				toPrint12, err = iface.Read(req0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				tla.MakeTLATuple(tla.MakeTLAString("ClientSndReq"), iface.Self(), toPrint10, toPrint11, toPrint12).PCalPrint()
				// no statements
			} else {
				// no statements
			}
			var condition89 tla.TLAValue
			condition89, err = iface.Read(req0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition89.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
				switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
				case 0:
					var exprRead61 tla.TLAValue
					exprRead61, err = iface.Read(reqIdx1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					// TODO: Why is multiple variables generated for the same resource??
					var exprRead62 tla.TLAValue
					exprRead62, err = iface.Read(req0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead63 tla.TLAValue
					exprRead63, err = iface.Read(req0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead64 tla.TLAValue
					exprRead64, err = iface.Read(leader8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead22 tla.TLAValue
					indexRead22, err = iface.Read(leader8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net7, []tla.TLAValue{indexRead22}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("mtype"), ClientPutRequest(iface)},
						{tla.MakeTLAString("mcmd"), tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("idx"), exprRead61},
							{tla.MakeTLAString("type"), Put(iface)},
							{tla.MakeTLAString("key"), exprRead62.ApplyFunction(tla.MakeTLAString("key"))},
							{tla.MakeTLAString("value"), exprRead63.ApplyFunction(tla.MakeTLAString("value"))},
						})},
						{tla.MakeTLAString("msource"), iface.Self()},
						{tla.MakeTLAString("mdest"), exprRead64},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AClient.rcvResp")
				case 1:
					var condition91 tla.TLAValue
					condition91, err = iface.Read(leader8, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition92 tla.TLAValue
					condition92, err = iface.Read(fd4, []tla.TLAValue{condition91})
					if err != nil {
						return err
					}
					if !condition92.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("AClient.rcvResp")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				var condition90 tla.TLAValue
				condition90, err = iface.Read(req0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition90.ApplyFunction(tla.MakeTLAString("type")), Get(iface)).AsBool() {
					// TODO: What does the NextFiarnessCounter do?
					switch iface.NextFairnessCounter("AClient.sndReq.1", 2) {
					case 0:
						var exprRead65 tla.TLAValue
						exprRead65, err = iface.Read(reqIdx1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead66 tla.TLAValue
						exprRead66, err = iface.Read(req0, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead67 tla.TLAValue
						exprRead67, err = iface.Read(leader8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead23 tla.TLAValue
						indexRead23, err = iface.Read(leader8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net7, []tla.TLAValue{indexRead23}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("mtype"), ClientGetRequest(iface)},
							{tla.MakeTLAString("mcmd"), tla.MakeTLARecord([]tla.TLARecordField{
								{tla.MakeTLAString("idx"), exprRead65},
								{tla.MakeTLAString("type"), Get(iface)},
								{tla.MakeTLAString("key"), exprRead66.ApplyFunction(tla.MakeTLAString("key"))},
							})},
							{tla.MakeTLAString("msource"), iface.Self()},
							{tla.MakeTLAString("mdest"), exprRead67},
						}))
						if err != nil {
							return err
						}
						return iface.Goto("AClient.rcvResp")
					case 1:
						var condition93 tla.TLAValue
						condition93, err = iface.Read(leader8, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition94 tla.TLAValue
						condition94, err = iface.Read(fd4, []tla.TLAValue{condition93})
						if err != nil {
							return err
						}
						if !condition94.AsBool() {
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
			// TODO: Why do we need to regenerate the ResourceRef in the same archetype?
			resp := iface.RequireArchetypeResource("AClient.resp")
			// TODO: How do we prevent conflicts? 2PC?
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
				var exprRead68 tla.TLAValue
				exprRead68, err = iface.Read(net9, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(resp, []tla.TLAValue{}, exprRead68)
				if err != nil {
					return err
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint13 tla.TLAValue
					toPrint13, err = iface.Read(leader17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint14 tla.TLAValue
					toPrint14, err = iface.Read(reqIdx4, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint15 tla.TLAValue
					toPrint15, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ClientRcvResp"), iface.Self(), toPrint13, toPrint14, toPrint15).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				var condition95 tla.TLAValue
				condition95, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition95.ApplyFunction(tla.MakeTLAString("mdest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((resp).mdest) = (self)", distsys.ErrAssertionFailed)
				}
				var condition96 tla.TLAValue
				// TODO: Again, why do we re-read the same resource?
				condition96, err = iface.Read(resp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition97 tla.TLAValue
				condition97, err = iface.Read(reqIdx4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_NotEqualsSymbol(condition96.ApplyFunction(tla.MakeTLAString("mresponse")).ApplyFunction(tla.MakeTLAString("idx")), condition97).AsBool() {
					return iface.Goto("AClient.rcvResp")
				} else {
					var exprRead69 tla.TLAValue
					exprRead69, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(leader17, []tla.TLAValue{}, exprRead69.ApplyFunction(tla.MakeTLAString("mleaderHint")))
					if err != nil {
						return err
					}
					var condition98 tla.TLAValue
					condition98, err = iface.Read(req6, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition99 tla.TLAValue
					condition99, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition100 tla.TLAValue
					condition100, err = iface.Read(req6, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition101 tla.TLAValue
					condition101, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.MakeTLABool(tla.MakeTLABool(!tla.TLA_EqualsSymbol(condition98.ApplyFunction(tla.MakeTLAString("type")), Get(iface)).AsBool() || tla.TLA_EqualsSymbol(condition99.ApplyFunction(tla.MakeTLAString("mtype")), ClientGetResponse(iface)).AsBool()).AsBool() && tla.MakeTLABool(!tla.TLA_EqualsSymbol(condition100.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() || tla.TLA_EqualsSymbol(condition101.ApplyFunction(tla.MakeTLAString("mtype")), ClientPutResponse(iface)).AsBool()).AsBool()).AsBool() {
						return fmt.Errorf("%w: ((((req).type) = (Get)) => (((resp).mtype) = (ClientGetResponse))) /\\ ((((req).type) = (Put)) => (((resp).mtype) = (ClientPutResponse)))", distsys.ErrAssertionFailed)
					}
					var condition102 tla.TLAValue
					condition102, err = iface.Read(resp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_LogicalNotSymbol(condition102.ApplyFunction(tla.MakeTLAString("msuccess"))).AsBool() {
						return iface.Goto("AClient.sndReq")
					} else {
						var condition103 tla.TLAValue
						condition103, err = iface.Read(resp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition104 tla.TLAValue
						condition104, err = iface.Read(reqIdx4, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition105 tla.TLAValue
						condition105, err = iface.Read(resp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition106 tla.TLAValue
						condition106, err = iface.Read(req6, []tla.TLAValue{})
						if err != nil {
							return err
						}
						if !tla.MakeTLABool(tla.TLA_EqualsSymbol(condition103.ApplyFunction(tla.MakeTLAString("mresponse")).ApplyFunction(tla.MakeTLAString("idx")), condition104).AsBool() && tla.TLA_EqualsSymbol(condition105.ApplyFunction(tla.MakeTLAString("mresponse")).ApplyFunction(tla.MakeTLAString("key")), condition106.ApplyFunction(tla.MakeTLAString("key"))).AsBool()).AsBool() {
							return fmt.Errorf("%w: ((((resp).mresponse).idx) = (reqIdx)) /\\ ((((resp).mresponse).key) = ((req).key))", distsys.ErrAssertionFailed)
						}
						var exprRead70 tla.TLAValue
						exprRead70, err = iface.Read(resp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(respCh, []tla.TLAValue{}, exprRead70)
						if err != nil {
							return err
						}
						if iface.GetConstant("Debug")().AsBool() {
							var toPrint16 tla.TLAValue
							toPrint16, err = iface.Read(leader17, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var toPrint17 tla.TLAValue
							toPrint17, err = iface.Read(reqIdx4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var toPrint18 tla.TLAValue
							toPrint18, err = iface.Read(resp, []tla.TLAValue{})
							if err != nil {
								return err
							}
							tla.MakeTLATuple(tla.MakeTLAString("ClientRcvChDone"), iface.Self(), toPrint16, toPrint17, toPrint18).PCalPrint()
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
				var condition107 tla.TLAValue
				condition107, err = iface.Read(leader17, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition108 tla.TLAValue
				condition108, err = iface.Read(fd6, []tla.TLAValue{condition107})
				if err != nil {
					return err
				}
				var condition109 tla.TLAValue
				condition109, err = iface.Read(netLen0, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				var condition110 tla.TLAValue
				condition110, err = iface.Read(timeout, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(tla.MakeTLABool(condition108.AsBool() && tla.TLA_EqualsSymbol(condition109, tla.MakeTLANumber(0)).AsBool()).AsBool() || condition110.AsBool()).AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				if iface.GetConstant("Debug")().AsBool() {
					var toPrint19 tla.TLAValue
					toPrint19, err = iface.Read(leader17, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var toPrint20 tla.TLAValue
					toPrint20, err = iface.Read(reqIdx4, []tla.TLAValue{})
					if err != nil {
						return err
					}
					tla.MakeTLATuple(tla.MakeTLAString("ClientTimeout"), iface.Self(), toPrint19, toPrint20).PCalPrint()
					// no statements
				} else {
					// no statements
				}
				err = iface.Write(leader17, []tla.TLAValue{}, Nil(iface))
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
			netEnabled, err := iface.RequireArchetypeResourceRef("AServerCrasher.netEnabled")
			if err != nil {
				return err
			}
			srvId68 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead24 tla.TLAValue
			indexRead24, err = iface.Read(srvId68, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(netEnabled, []tla.TLAValue{indexRead24}, tla.TLA_FALSE)
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
			srvId69 := iface.RequireArchetypeResource("AServerCrasher.srvId")
			var indexRead25 tla.TLAValue
			indexRead25, err = iface.Read(srvId69, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(fd7, []tla.TLAValue{indexRead25}, tla.TLA_TRUE)
			if err != nil {
				return err
			}
			return iface.Goto("AServerCrasher.block")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServerCrasher.block",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if !tla.TLA_FALSE.AsBool() {
				return distsys.ErrCriticalSectionAborted
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

var AServerListener = distsys.MPCalArchetype{
	Name:              "AServerListener",
	Label:             "AServerListener.listenerLoop",
	RequiredRefParams: []string{"AServerListener.net", "AServerListener.netLen", "AServerListener.netEnabled", "AServerListener.fd", "AServerListener.state", "AServerListener.currentTerm", "AServerListener.log", "AServerListener.plog", "AServerListener.commitIndex", "AServerListener.nextIndex", "AServerListener.matchIndex", "AServerListener.votedFor", "AServerListener.votesResponded", "AServerListener.votesGranted", "AServerListener.leader", "AServerListener.sm", "AServerListener.smDomain", "AServerListener.leaderTimeout", "AServerListener.appendEntriesCh", "AServerListener.becomeLeaderCh", "AServerListener.handlerCh"},
	RequiredValParams: []string{"AServerListener.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerListener.m", tla.TLAValue{})
	},
}

var AServerHandler = distsys.MPCalArchetype{
	Name:              "AServerHandler",
	Label:             "AServerHandler.serverLoop",
	RequiredRefParams: []string{"AServerHandler.net", "AServerHandler.netLen", "AServerHandler.netEnabled", "AServerHandler.fd", "AServerHandler.state", "AServerHandler.currentTerm", "AServerHandler.log", "AServerHandler.plog", "AServerHandler.commitIndex", "AServerHandler.nextIndex", "AServerHandler.matchIndex", "AServerHandler.votedFor", "AServerHandler.votesResponded", "AServerHandler.votesGranted", "AServerHandler.leader", "AServerHandler.sm", "AServerHandler.smDomain", "AServerHandler.leaderTimeout", "AServerHandler.appendEntriesCh", "AServerHandler.becomeLeaderCh", "AServerHandler.handlerCh"},
	RequiredValParams: []string{"AServerHandler.srvId"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServerHandler.idx", tla.MakeTLANumber(1))
		iface.EnsureArchetypeResourceLocal("AServerHandler.m", tla.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("AServerRequestVote.idx", tla.MakeTLANumber(1))
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
		iface.EnsureArchetypeResourceLocal("AServerAppendEntries.idx", tla.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("AServerAdvanceCommitIndex.newCommitIndex", tla.MakeTLANumber(0))
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
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.reqIdx", tla.MakeTLANumber(0))
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
