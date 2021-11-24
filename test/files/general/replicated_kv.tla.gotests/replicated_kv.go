package replicatedkv

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func KeySpace(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(iface.GetConstant("GET_KEY")(), iface.GetConstant("PUT_KEY")())
}
func GET_ORDER(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
}
func PUT_ORDER(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func DISCONNECT_ORDER(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func NULL_ORDER(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func GetSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_MinusSymbol(iface.GetConstant("NUM_CLIENTS")(), tla.MakeTLANumber(1))))
}
func PutSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")()), tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_MinusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(2), iface.GetConstant("NUM_CLIENTS")()), tla.MakeTLANumber(1))))
}
func DisconnectSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(2), iface.GetConstant("NUM_CLIENTS")())), tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_MinusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(3), iface.GetConstant("NUM_CLIENTS")()), tla.MakeTLANumber(1))))
}
func NullSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_AsteriskSymbol(tla.MakeTLANumber(3), iface.GetConstant("NUM_CLIENTS")())), tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_MinusSymbol(tla.TLA_AsteriskSymbol(tla.MakeTLANumber(4), iface.GetConstant("NUM_CLIENTS")()), tla.MakeTLANumber(1))))
}
func NUM_NODES(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
}
func ReplicaSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(0), tla.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeTLANumber(1)))
}
func ClientSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.TLA_MinusSymbol(NUM_NODES(iface), tla.MakeTLANumber(1)))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			stableMessages := iface.RequireArchetypeResource("AReplica.stableMessages")
			continue0 := iface.RequireArchetypeResource("AReplica.continue")
			if tla.TLA_TRUE.AsBool() {
				err = iface.Write(stableMessages, []tla.TLAValue{}, tla.MakeTLATuple())
				if err != nil {
					return err
				}
				err = iface.Write(continue0, []tla.TLAValue{}, tla.TLA_TRUE)
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.receiveClientRequest")
			} else {
				return iface.Goto("AReplica.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.receiveClientRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AReplica.msg")
			replicas, err := iface.RequireArchetypeResourceRef("AReplica.replicas")
			if err != nil {
				return err
			}
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(replicas, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []tla.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("AReplica.clientDisconnected")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.clientDisconnected",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg0 := iface.RequireArchetypeResource("AReplica.msg")
			liveClients := iface.RequireArchetypeResource("AReplica.liveClients")
			var condition tla.TLAValue
			condition, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("DISCONNECT_MSG")()).AsBool() {
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(liveClients, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(msg0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(liveClients, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead0, tla.MakeTLASet(exprRead1.ApplyFunction(tla.MakeTLAString("client")))))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.replicaGetRequest")
			} else {
				return iface.Goto("AReplica.replicaGetRequest")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaGetRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg2 := iface.RequireArchetypeResource("AReplica.msg")
			liveClients1 := iface.RequireArchetypeResource("AReplica.liveClients")
			currentClocks := iface.RequireArchetypeResource("AReplica.currentClocks")
			pendingRequests := iface.RequireArchetypeResource("AReplica.pendingRequests")
			var condition0 tla.TLAValue
			condition0, err = iface.Read(msg2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition0.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("GET_MSG")()).AsBool() {
				var condition1 tla.TLAValue
				condition1, err = iface.Read(msg2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition2 tla.TLAValue
				condition2, err = iface.Read(liveClients1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_InSymbol(condition1.ApplyFunction(tla.MakeTLAString("client")), condition2).AsBool() {
					return fmt.Errorf("%w: ((msg).client) \\in (liveClients)", distsys.ErrAssertionFailed)
				}
				var exprRead2 tla.TLAValue
				exprRead2, err = iface.Read(msg2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead tla.TLAValue
				indexRead, err = iface.Read(msg2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks, []tla.TLAValue{indexRead.ApplyFunction(tla.MakeTLAString("client"))}, exprRead2.ApplyFunction(tla.MakeTLAString("timestamp")))
				if err != nil {
					return err
				}
				var exprRead3 tla.TLAValue
				exprRead3, err = iface.Read(pendingRequests, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead4 tla.TLAValue
				exprRead4, err = iface.Read(msg2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead5 tla.TLAValue
				exprRead5, err = iface.Read(msg2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead0 tla.TLAValue
				indexRead0, err = iface.Read(msg2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests, []tla.TLAValue{indexRead0.ApplyFunction(tla.MakeTLAString("client"))}, tla.TLA_Append(exprRead3.ApplyFunction(exprRead4.ApplyFunction(tla.MakeTLAString("client"))), exprRead5))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.replicaPutRequest")
			} else {
				return iface.Goto("AReplica.replicaPutRequest")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaPutRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg9 := iface.RequireArchetypeResource("AReplica.msg")
			currentClocks0 := iface.RequireArchetypeResource("AReplica.currentClocks")
			pendingRequests1 := iface.RequireArchetypeResource("AReplica.pendingRequests")
			var condition3 tla.TLAValue
			condition3, err = iface.Read(msg9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition3.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("PUT_MSG")()).AsBool() {
				var exprRead6 tla.TLAValue
				exprRead6, err = iface.Read(msg9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead1 tla.TLAValue
				indexRead1, err = iface.Read(msg9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks0, []tla.TLAValue{indexRead1.ApplyFunction(tla.MakeTLAString("client"))}, exprRead6.ApplyFunction(tla.MakeTLAString("timestamp")))
				if err != nil {
					return err
				}
				var exprRead7 tla.TLAValue
				exprRead7, err = iface.Read(pendingRequests1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead8 tla.TLAValue
				exprRead8, err = iface.Read(msg9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead9 tla.TLAValue
				exprRead9, err = iface.Read(msg9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead2 tla.TLAValue
				indexRead2, err = iface.Read(msg9, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests1, []tla.TLAValue{indexRead2.ApplyFunction(tla.MakeTLAString("client"))}, tla.TLA_Append(exprRead7.ApplyFunction(exprRead8.ApplyFunction(tla.MakeTLAString("client"))), exprRead9))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.replicaNullRequest")
			} else {
				return iface.Goto("AReplica.replicaNullRequest")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.replicaNullRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg15 := iface.RequireArchetypeResource("AReplica.msg")
			currentClocks1 := iface.RequireArchetypeResource("AReplica.currentClocks")
			var condition4 tla.TLAValue
			condition4, err = iface.Read(msg15, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition4.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("NULL_MSG")()).AsBool() {
				var exprRead10 tla.TLAValue
				exprRead10, err = iface.Read(msg15, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead3 tla.TLAValue
				indexRead3, err = iface.Read(msg15, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks1, []tla.TLAValue{indexRead3.ApplyFunction(tla.MakeTLAString("client"))}, exprRead10.ApplyFunction(tla.MakeTLAString("timestamp")))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findStableRequestsLoop")
			} else {
				return iface.Goto("AReplica.findStableRequestsLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.findStableRequestsLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			continue1 := iface.RequireArchetypeResource("AReplica.continue")
			pendingClients := iface.RequireArchetypeResource("AReplica.pendingClients")
			liveClients2 := iface.RequireArchetypeResource("AReplica.liveClients")
			pendingRequests3 := iface.RequireArchetypeResource("AReplica.pendingRequests")
			nextClient := iface.RequireArchetypeResource("AReplica.nextClient")
			clientsIter := iface.RequireArchetypeResource("AReplica.clientsIter")
			i := iface.RequireArchetypeResource("AReplica.i")
			minClock := iface.RequireArchetypeResource("AReplica.minClock")
			var condition5 tla.TLAValue
			condition5, err = iface.Read(continue1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if condition5.AsBool() {
				var exprRead11 tla.TLAValue
				exprRead11, err = iface.Read(liveClients2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead12 tla.TLAValue
				exprRead12, err = iface.Read(pendingRequests3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingClients, []tla.TLAValue{}, tla.TLASetRefinement(exprRead11, func(elem tla.TLAValue) bool {
					var c tla.TLAValue = elem
					_ = c
					return tla.TLA_GreaterThanSymbol(tla.TLA_Len(exprRead12.ApplyFunction(c)), tla.MakeTLANumber(0)).AsBool()
				}))
				if err != nil {
					return err
				}
				err = iface.Write(nextClient, []tla.TLAValue{}, tla.TLA_PlusSymbol(NUM_NODES(iface), tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				var exprRead13 tla.TLAValue
				exprRead13, err = iface.Read(liveClients2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clientsIter, []tla.TLAValue{}, exprRead13)
				if err != nil {
					return err
				}
				err = iface.Write(i, []tla.TLAValue{}, tla.MakeTLANumber(0))
				if err != nil {
					return err
				}
				err = iface.Write(minClock, []tla.TLAValue{}, tla.MakeTLANumber(0))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClock")
			} else {
				err = iface.Write(i, []tla.TLAValue{}, tla.MakeTLANumber(1))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.respondPendingRequestsLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.findMinClock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i1 := iface.RequireArchetypeResource("AReplica.i")
			clientsIter0 := iface.RequireArchetypeResource("AReplica.clientsIter")
			minClock0 := iface.RequireArchetypeResource("AReplica.minClock")
			currentClocks2 := iface.RequireArchetypeResource("AReplica.currentClocks")
			lowestPending := iface.RequireArchetypeResource("AReplica.lowestPending")
			var condition6 tla.TLAValue
			condition6, err = iface.Read(i1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition7 tla.TLAValue
			condition7, err = iface.Read(clientsIter0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition6, tla.TLA_Cardinality(condition7)).AsBool() {
				var clientRead tla.TLAValue
				clientRead, err = iface.Read(clientsIter0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var clientRead0 = clientRead
				if clientRead0.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var client tla.TLAValue = clientRead0.SelectElement(iface.NextFairnessCounter("AReplica.findMinClock.0", uint(clientRead0.AsSet().Len())))
				_ = client
				var condition8 tla.TLAValue
				condition8, err = iface.Read(minClock0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition9 tla.TLAValue
				condition9, err = iface.Read(currentClocks2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition10 tla.TLAValue
				condition10, err = iface.Read(minClock0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.MakeTLABool(tla.TLA_EqualsSymbol(condition8, tla.MakeTLANumber(0)).AsBool() || tla.TLA_LessThanSymbol(condition9.ApplyFunction(client), condition10).AsBool()).AsBool() {
					var exprRead14 tla.TLAValue
					exprRead14, err = iface.Read(currentClocks2, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(minClock0, []tla.TLAValue{}, exprRead14.ApplyFunction(client))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead15 tla.TLAValue
				exprRead15, err = iface.Read(clientsIter0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clientsIter0, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead15, tla.MakeTLASet(client)))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClock")
				// no statements
			} else {
				var exprRead16 tla.TLAValue
				exprRead16, err = iface.Read(minClock0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(lowestPending, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead16, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(i1, []tla.TLAValue{}, tla.MakeTLANumber(0))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClient")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.findMinClient",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i3 := iface.RequireArchetypeResource("AReplica.i")
			pendingClients0 := iface.RequireArchetypeResource("AReplica.pendingClients")
			firstPending := iface.RequireArchetypeResource("AReplica.firstPending")
			pendingRequests4 := iface.RequireArchetypeResource("AReplica.pendingRequests")
			timestamp := iface.RequireArchetypeResource("AReplica.timestamp")
			minClock4 := iface.RequireArchetypeResource("AReplica.minClock")
			chooseMessage := iface.RequireArchetypeResource("AReplica.chooseMessage")
			lowestPending0 := iface.RequireArchetypeResource("AReplica.lowestPending")
			nextClient0 := iface.RequireArchetypeResource("AReplica.nextClient")
			var condition11 tla.TLAValue
			condition11, err = iface.Read(i3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition12 tla.TLAValue
			condition12, err = iface.Read(pendingClients0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition11, tla.TLA_Cardinality(condition12)).AsBool() {
				var clientRead1 tla.TLAValue
				clientRead1, err = iface.Read(pendingClients0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var clientRead2 = clientRead1
				if clientRead2.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var client0 tla.TLAValue = clientRead2.SelectElement(iface.NextFairnessCounter("AReplica.findMinClient.0", uint(clientRead2.AsSet().Len())))
				_ = client0
				var exprRead17 tla.TLAValue
				exprRead17, err = iface.Read(pendingRequests4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(firstPending, []tla.TLAValue{}, tla.TLA_Head(exprRead17.ApplyFunction(client0)))
				if err != nil {
					return err
				}
				var condition13 tla.TLAValue
				condition13, err = iface.Read(firstPending, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition14 tla.TLAValue
				condition14, err = iface.Read(firstPending, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.MakeTLABool(tla.TLA_EqualsSymbol(condition13.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("GET_MSG")()).AsBool() || tla.TLA_EqualsSymbol(condition14.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("PUT_MSG")()).AsBool()).AsBool() {
					return fmt.Errorf("%w: (((firstPending).op) = (GET_MSG)) \\/ (((firstPending).op) = (PUT_MSG))", distsys.ErrAssertionFailed)
				}
				var exprRead18 tla.TLAValue
				exprRead18, err = iface.Read(firstPending, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(timestamp, []tla.TLAValue{}, exprRead18.ApplyFunction(tla.MakeTLAString("timestamp")))
				if err != nil {
					return err
				}
				var condition15 tla.TLAValue
				condition15, err = iface.Read(timestamp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition16 tla.TLAValue
				condition16, err = iface.Read(minClock4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_LessThanSymbol(condition15, condition16).AsBool() {
					var exprRead19 tla.TLAValue
					exprRead19, err = iface.Read(timestamp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead20 tla.TLAValue
					exprRead20, err = iface.Read(lowestPending0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead21 tla.TLAValue
					exprRead21, err = iface.Read(timestamp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead22 tla.TLAValue
					exprRead22, err = iface.Read(lowestPending0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead23 tla.TLAValue
					exprRead23, err = iface.Read(nextClient0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(chooseMessage, []tla.TLAValue{}, tla.MakeTLABool(tla.TLA_LessThanSymbol(exprRead19, exprRead20).AsBool() || tla.MakeTLABool(tla.TLA_EqualsSymbol(exprRead21, exprRead22).AsBool() && tla.TLA_LessThanSymbol(client0, exprRead23).AsBool()).AsBool()))
					if err != nil {
						return err
					}
					var condition17 tla.TLAValue
					condition17, err = iface.Read(chooseMessage, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if condition17.AsBool() {
						err = iface.Write(nextClient0, []tla.TLAValue{}, client0)
						if err != nil {
							return err
						}
						var exprRead24 tla.TLAValue
						exprRead24, err = iface.Read(timestamp, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(lowestPending0, []tla.TLAValue{}, exprRead24)
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead25 tla.TLAValue
				exprRead25, err = iface.Read(pendingClients0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingClients0, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead25, tla.MakeTLASet(client0)))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClient")
				// no statements
			} else {
				return iface.Goto("AReplica.addStableMessage")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.addStableMessage",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			lowestPending3 := iface.RequireArchetypeResource("AReplica.lowestPending")
			minClock5 := iface.RequireArchetypeResource("AReplica.minClock")
			msg18 := iface.RequireArchetypeResource("AReplica.msg")
			pendingRequests5 := iface.RequireArchetypeResource("AReplica.pendingRequests")
			nextClient2 := iface.RequireArchetypeResource("AReplica.nextClient")
			stableMessages0 := iface.RequireArchetypeResource("AReplica.stableMessages")
			continue2 := iface.RequireArchetypeResource("AReplica.continue")
			var condition18 tla.TLAValue
			condition18, err = iface.Read(lowestPending3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition19 tla.TLAValue
			condition19, err = iface.Read(minClock5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition18, condition19).AsBool() {
				var exprRead26 tla.TLAValue
				exprRead26, err = iface.Read(pendingRequests5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead27 tla.TLAValue
				exprRead27, err = iface.Read(nextClient2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(msg18, []tla.TLAValue{}, tla.TLA_Head(exprRead26.ApplyFunction(exprRead27)))
				if err != nil {
					return err
				}
				var exprRead28 tla.TLAValue
				exprRead28, err = iface.Read(pendingRequests5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead29 tla.TLAValue
				exprRead29, err = iface.Read(nextClient2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead4 tla.TLAValue
				indexRead4, err = iface.Read(nextClient2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests5, []tla.TLAValue{indexRead4}, tla.TLA_Tail(exprRead28.ApplyFunction(exprRead29)))
				if err != nil {
					return err
				}
				var exprRead30 tla.TLAValue
				exprRead30, err = iface.Read(stableMessages0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead31 tla.TLAValue
				exprRead31, err = iface.Read(msg18, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(stableMessages0, []tla.TLAValue{}, tla.TLA_Append(exprRead30, exprRead31))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findStableRequestsLoop")
			} else {
				err = iface.Write(continue2, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findStableRequestsLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.respondPendingRequestsLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i4 := iface.RequireArchetypeResource("AReplica.i")
			stableMessages2 := iface.RequireArchetypeResource("AReplica.stableMessages")
			msg20 := iface.RequireArchetypeResource("AReplica.msg")
			var condition20 tla.TLAValue
			condition20, err = iface.Read(i4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition21 tla.TLAValue
			condition21, err = iface.Read(stableMessages2, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition20, tla.TLA_Len(condition21)).AsBool() {
				var exprRead32 tla.TLAValue
				exprRead32, err = iface.Read(stableMessages2, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead33 tla.TLAValue
				exprRead33, err = iface.Read(i4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(msg20, []tla.TLAValue{}, exprRead32.ApplyFunction(exprRead33))
				if err != nil {
					return err
				}
				var exprRead34 tla.TLAValue
				exprRead34, err = iface.Read(i4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(i4, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead34, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.respondStableGet")
			} else {
				return iface.Goto("AReplica.replicaLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.respondStableGet",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg21 := iface.RequireArchetypeResource("AReplica.msg")
			key := iface.RequireArchetypeResource("AReplica.key")
			val := iface.RequireArchetypeResource("AReplica.val")
			kv, err := iface.RequireArchetypeResourceRef("AReplica.kv")
			if err != nil {
				return err
			}
			clients, err := iface.RequireArchetypeResourceRef("AReplica.clients")
			if err != nil {
				return err
			}
			var condition22 tla.TLAValue
			condition22, err = iface.Read(msg21, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition22.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("GET_MSG")()).AsBool() {
				var exprRead35 tla.TLAValue
				exprRead35, err = iface.Read(msg21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(key, []tla.TLAValue{}, exprRead35.ApplyFunction(tla.MakeTLAString("key")))
				if err != nil {
					return err
				}
				var exprRead36 tla.TLAValue
				exprRead36, err = iface.Read(key, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead37 tla.TLAValue
				exprRead37, err = iface.Read(kv, []tla.TLAValue{exprRead36})
				if err != nil {
					return err
				}
				err = iface.Write(val, []tla.TLAValue{}, exprRead37)
				if err != nil {
					return err
				}
				var exprRead38 tla.TLAValue
				exprRead38, err = iface.Read(val, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead5 tla.TLAValue
				indexRead5, err = iface.Read(msg21, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clients, []tla.TLAValue{indexRead5.ApplyFunction(tla.MakeTLAString("reply_to"))}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("type"), iface.GetConstant("GET_RESPONSE")()},
					{tla.MakeTLAString("result"), exprRead38},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.respondStablePut")
			} else {
				return iface.Goto("AReplica.respondStablePut")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.respondStablePut",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg24 := iface.RequireArchetypeResource("AReplica.msg")
			key1 := iface.RequireArchetypeResource("AReplica.key")
			val1 := iface.RequireArchetypeResource("AReplica.val")
			kv0, err := iface.RequireArchetypeResourceRef("AReplica.kv")
			if err != nil {
				return err
			}
			clients0, err := iface.RequireArchetypeResourceRef("AReplica.clients")
			if err != nil {
				return err
			}
			ok := iface.RequireArchetypeResource("AReplica.ok")
			var condition23 tla.TLAValue
			condition23, err = iface.Read(msg24, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition23.ApplyFunction(tla.MakeTLAString("op")), iface.GetConstant("PUT_MSG")()).AsBool() {
				var exprRead39 tla.TLAValue
				exprRead39, err = iface.Read(msg24, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(key1, []tla.TLAValue{}, exprRead39.ApplyFunction(tla.MakeTLAString("key")))
				if err != nil {
					return err
				}
				var exprRead40 tla.TLAValue
				exprRead40, err = iface.Read(msg24, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(val1, []tla.TLAValue{}, exprRead40.ApplyFunction(tla.MakeTLAString("value")))
				if err != nil {
					return err
				}
				var exprRead41 tla.TLAValue
				exprRead41, err = iface.Read(val1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead6 tla.TLAValue
				indexRead6, err = iface.Read(key1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(kv0, []tla.TLAValue{indexRead6}, exprRead41)
				if err != nil {
					return err
				}
				var exprRead42 tla.TLAValue
				exprRead42, err = iface.Read(ok, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead7 tla.TLAValue
				indexRead7, err = iface.Read(msg24, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clients0, []tla.TLAValue{indexRead7.ApplyFunction(tla.MakeTLAString("reply_to"))}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("type"), iface.GetConstant("PUT_RESPONSE")()},
					{tla.MakeTLAString("result"), exprRead42},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.respondPendingRequestsLoop")
			} else {
				return iface.Goto("AReplica.respondPendingRequestsLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReplica.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Get.getLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			continue3 := iface.RequireArchetypeResource("Get.continue")
			var condition24 tla.TLAValue
			condition24, err = iface.Read(continue3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if condition24.AsBool() {
				return iface.Goto("Get.getRequest")
			} else {
				return iface.Goto("Get.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Get.getRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			clock, err := iface.RequireArchetypeResourceRef("Get.clock")
			if err != nil {
				return err
			}
			clientId, err := iface.RequireArchetypeResourceRef("Get.clientId")
			if err != nil {
				return err
			}
			continue4 := iface.RequireArchetypeResource("Get.continue")
			getReq := iface.RequireArchetypeResource("Get.getReq")
			key3 := iface.RequireArchetypeResource("Get.key")
			replicas0, err := iface.RequireArchetypeResourceRef("Get.replicas")
			if err != nil {
				return err
			}
			var condition25 tla.TLAValue
			condition25, err = iface.Read(clientId, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition26 tla.TLAValue
			condition26, err = iface.Read(clock, []tla.TLAValue{condition25})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition26, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool() {
				err = iface.Write(continue4, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			} else {
				var exprRead43 tla.TLAValue
				exprRead43, err = iface.Read(clientId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead44 tla.TLAValue
				exprRead44, err = iface.Read(clock, []tla.TLAValue{exprRead43})
				if err != nil {
					return err
				}
				var indexRead8 tla.TLAValue
				indexRead8, err = iface.Read(clientId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clock, []tla.TLAValue{indexRead8}, tla.TLA_PlusSymbol(exprRead44, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				var exprRead45 tla.TLAValue
				exprRead45, err = iface.Read(key3, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead46 tla.TLAValue
				exprRead46, err = iface.Read(clientId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead47 tla.TLAValue
				exprRead47, err = iface.Read(clientId, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead48 tla.TLAValue
				exprRead48, err = iface.Read(clock, []tla.TLAValue{exprRead47})
				if err != nil {
					return err
				}
				err = iface.Write(getReq, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("op"), iface.GetConstant("GET_MSG")()},
					{tla.MakeTLAString("key"), exprRead45},
					{tla.MakeTLAString("client"), exprRead46},
					{tla.MakeTLAString("timestamp"), exprRead48},
					{tla.MakeTLAString("reply_to"), iface.Self()},
				}))
				if err != nil {
					return err
				}
				var dstRead = ReplicaSet(iface)
				if dstRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var dst tla.TLAValue = dstRead.SelectElement(iface.NextFairnessCounter("Get.getRequest.0", uint(dstRead.AsSet().Len())))
				_ = dst
				var exprRead49 tla.TLAValue
				exprRead49, err = iface.Read(getReq, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas0, []tla.TLAValue{dst}, exprRead49)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getReply")
				// no statements
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Get.getReply",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			clock3, err := iface.RequireArchetypeResourceRef("Get.clock")
			if err != nil {
				return err
			}
			clientId4, err := iface.RequireArchetypeResourceRef("Get.clientId")
			if err != nil {
				return err
			}
			continue5 := iface.RequireArchetypeResource("Get.continue")
			getResp := iface.RequireArchetypeResource("Get.getResp")
			clients1, err := iface.RequireArchetypeResourceRef("Get.clients")
			if err != nil {
				return err
			}
			outside, err := iface.RequireArchetypeResourceRef("Get.outside")
			if err != nil {
				return err
			}
			var condition27 tla.TLAValue
			condition27, err = iface.Read(clientId4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition28 tla.TLAValue
			condition28, err = iface.Read(clock3, []tla.TLAValue{condition27})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition28, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool() {
				err = iface.Write(continue5, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			} else {
				var exprRead50 tla.TLAValue
				exprRead50, err = iface.Read(clients1, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(getResp, []tla.TLAValue{}, exprRead50)
				if err != nil {
					return err
				}
				var condition29 tla.TLAValue
				condition29, err = iface.Read(getResp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition29.ApplyFunction(tla.MakeTLAString("type")), iface.GetConstant("GET_RESPONSE")()).AsBool() {
					return fmt.Errorf("%w: ((getResp).type) = (GET_RESPONSE)", distsys.ErrAssertionFailed)
				}
				var exprRead51 tla.TLAValue
				exprRead51, err = iface.Read(getResp, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(outside, []tla.TLAValue{}, exprRead51.ApplyFunction(tla.MakeTLAString("result")))
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Get.getCheckSpin",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			spin := iface.RequireArchetypeResource("Get.spin")
			continue6 := iface.RequireArchetypeResource("Get.continue")
			var condition30 tla.TLAValue
			condition30, err = iface.Read(spin, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LogicalNotSymbol(condition30).AsBool() {
				err = iface.Write(continue6, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getLoop")
			} else {
				return iface.Goto("Get.getLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Get.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.putLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			continue7 := iface.RequireArchetypeResource("Put.continue")
			var condition31 tla.TLAValue
			condition31, err = iface.Read(continue7, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if condition31.AsBool() {
				return iface.Goto("Put.putRequest")
			} else {
				return iface.Goto("Put.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.putRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			clock4, err := iface.RequireArchetypeResourceRef("Put.clock")
			if err != nil {
				return err
			}
			clientId5, err := iface.RequireArchetypeResourceRef("Put.clientId")
			if err != nil {
				return err
			}
			continue8 := iface.RequireArchetypeResource("Put.continue")
			putReq := iface.RequireArchetypeResource("Put.putReq")
			key4 := iface.RequireArchetypeResource("Put.key")
			value := iface.RequireArchetypeResource("Put.value")
			i8 := iface.RequireArchetypeResource("Put.i")
			j := iface.RequireArchetypeResource("Put.j")
			var condition32 tla.TLAValue
			condition32, err = iface.Read(clientId5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition33 tla.TLAValue
			condition33, err = iface.Read(clock4, []tla.TLAValue{condition32})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition33, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool() {
				err = iface.Write(continue8, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Put.putCheckSpin")
			} else {
				var exprRead52 tla.TLAValue
				exprRead52, err = iface.Read(clientId5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead53 tla.TLAValue
				exprRead53, err = iface.Read(clock4, []tla.TLAValue{exprRead52})
				if err != nil {
					return err
				}
				var indexRead9 tla.TLAValue
				indexRead9, err = iface.Read(clientId5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clock4, []tla.TLAValue{indexRead9}, tla.TLA_PlusSymbol(exprRead53, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				var exprRead54 tla.TLAValue
				exprRead54, err = iface.Read(key4, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead55 tla.TLAValue
				exprRead55, err = iface.Read(value, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead56 tla.TLAValue
				exprRead56, err = iface.Read(clientId5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead57 tla.TLAValue
				exprRead57, err = iface.Read(clientId5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead58 tla.TLAValue
				exprRead58, err = iface.Read(clock4, []tla.TLAValue{exprRead57})
				if err != nil {
					return err
				}
				err = iface.Write(putReq, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("op"), iface.GetConstant("PUT_MSG")()},
					{tla.MakeTLAString("key"), exprRead54},
					{tla.MakeTLAString("value"), exprRead55},
					{tla.MakeTLAString("client"), exprRead56},
					{tla.MakeTLAString("timestamp"), exprRead58},
					{tla.MakeTLAString("reply_to"), iface.Self()},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(i8, []tla.TLAValue{}, tla.MakeTLANumber(0))
				if err != nil {
					return err
				}
				err = iface.Write(j, []tla.TLAValue{}, tla.MakeTLANumber(0))
				if err != nil {
					return err
				}
				return iface.Goto("Put.putBroadcast")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.putBroadcast",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			j0 := iface.RequireArchetypeResource("Put.j")
			clock8, err := iface.RequireArchetypeResourceRef("Put.clock")
			if err != nil {
				return err
			}
			clientId10, err := iface.RequireArchetypeResourceRef("Put.clientId")
			if err != nil {
				return err
			}
			replicas1, err := iface.RequireArchetypeResourceRef("Put.replicas")
			if err != nil {
				return err
			}
			putReq0 := iface.RequireArchetypeResource("Put.putReq")
			var condition34 tla.TLAValue
			condition34, err = iface.Read(j0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition35 tla.TLAValue
			condition35, err = iface.Read(clientId10, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition36 tla.TLAValue
			condition36, err = iface.Read(clock8, []tla.TLAValue{condition35})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_LessThanOrEqualSymbol(condition34, tla.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeTLANumber(1))).AsBool() && tla.TLA_NotEqualsSymbol(condition36, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool()).AsBool() {
				var exprRead59 tla.TLAValue
				exprRead59, err = iface.Read(putReq0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead10 tla.TLAValue
				indexRead10, err = iface.Read(j0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas1, []tla.TLAValue{indexRead10}, exprRead59)
				if err != nil {
					return err
				}
				var exprRead60 tla.TLAValue
				exprRead60, err = iface.Read(j0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(j0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead60, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("Put.putBroadcast")
			} else {
				return iface.Goto("Put.putResponse")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.putResponse",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i9 := iface.RequireArchetypeResource("Put.i")
			clock9, err := iface.RequireArchetypeResourceRef("Put.clock")
			if err != nil {
				return err
			}
			clientId11, err := iface.RequireArchetypeResourceRef("Put.clientId")
			if err != nil {
				return err
			}
			continue9 := iface.RequireArchetypeResource("Put.continue")
			putResp := iface.RequireArchetypeResource("Put.putResp")
			clients2, err := iface.RequireArchetypeResourceRef("Put.clients")
			if err != nil {
				return err
			}
			var condition37 tla.TLAValue
			condition37, err = iface.Read(i9, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition37, tla.TLA_Cardinality(ReplicaSet(iface))).AsBool() {
				var condition38 tla.TLAValue
				condition38, err = iface.Read(clientId11, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition39 tla.TLAValue
				condition39, err = iface.Read(clock9, []tla.TLAValue{condition38})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition39, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool() {
					err = iface.Write(continue9, []tla.TLAValue{}, tla.TLA_FALSE)
					if err != nil {
						return err
					}
					return iface.Goto("Put.putLoop")
				} else {
					var exprRead61 tla.TLAValue
					exprRead61, err = iface.Read(clients2, []tla.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					err = iface.Write(putResp, []tla.TLAValue{}, exprRead61)
					if err != nil {
						return err
					}
					var condition40 tla.TLAValue
					condition40, err = iface.Read(putResp, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if !tla.TLA_EqualsSymbol(condition40.ApplyFunction(tla.MakeTLAString("type")), iface.GetConstant("PUT_RESPONSE")()).AsBool() {
						return fmt.Errorf("%w: ((putResp).type) = (PUT_RESPONSE)", distsys.ErrAssertionFailed)
					}
					var exprRead62 tla.TLAValue
					exprRead62, err = iface.Read(i9, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(i9, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead62, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					return iface.Goto("Put.putResponse")
				}
				// no statements
			} else {
				return iface.Goto("Put.putComplete")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.putComplete",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			outside0, err := iface.RequireArchetypeResourceRef("Put.outside")
			if err != nil {
				return err
			}
			err = iface.Write(outside0, []tla.TLAValue{}, iface.GetConstant("PUT_RESPONSE")())
			if err != nil {
				return err
			}
			return iface.Goto("Put.putCheckSpin")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.putCheckSpin",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			spin0 := iface.RequireArchetypeResource("Put.spin")
			continue10 := iface.RequireArchetypeResource("Put.continue")
			var condition41 tla.TLAValue
			condition41, err = iface.Read(spin0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LogicalNotSymbol(condition41).AsBool() {
				err = iface.Write(continue10, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Put.putLoop")
			} else {
				return iface.Goto("Put.putLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Put.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Disconnect.sendDisconnectRequest",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg28 := iface.RequireArchetypeResource("Disconnect.msg")
			clientId12, err := iface.RequireArchetypeResourceRef("Disconnect.clientId")
			if err != nil {
				return err
			}
			clock10, err := iface.RequireArchetypeResourceRef("Disconnect.clock")
			if err != nil {
				return err
			}
			j4 := iface.RequireArchetypeResource("Disconnect.j")
			var exprRead63 tla.TLAValue
			exprRead63, err = iface.Read(clientId12, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(msg28, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("op"), iface.GetConstant("DISCONNECT_MSG")()},
				{tla.MakeTLAString("client"), exprRead63},
			}))
			if err != nil {
				return err
			}
			var indexRead11 tla.TLAValue
			indexRead11, err = iface.Read(clientId12, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(clock10, []tla.TLAValue{indexRead11}, tla.TLA_NegationSymbol(tla.MakeTLANumber(1)))
			if err != nil {
				return err
			}
			err = iface.Write(j4, []tla.TLAValue{}, tla.MakeTLANumber(0))
			if err != nil {
				return err
			}
			return iface.Goto("Disconnect.disconnectBroadcast")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Disconnect.disconnectBroadcast",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			j5 := iface.RequireArchetypeResource("Disconnect.j")
			replicas2, err := iface.RequireArchetypeResourceRef("Disconnect.replicas")
			if err != nil {
				return err
			}
			msg29 := iface.RequireArchetypeResource("Disconnect.msg")
			var condition42 tla.TLAValue
			condition42, err = iface.Read(j5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_LessThanOrEqualSymbol(condition42, tla.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeTLANumber(1))).AsBool() && tla.TLA_NotEqualsSymbol(tla.MakeTLANumber(0), tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool()).AsBool() {
				var exprRead64 tla.TLAValue
				exprRead64, err = iface.Read(msg29, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead12 tla.TLAValue
				indexRead12, err = iface.Read(j5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas2, []tla.TLAValue{indexRead12}, exprRead64)
				if err != nil {
					return err
				}
				var exprRead65 tla.TLAValue
				exprRead65, err = iface.Read(j5, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(j5, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead65, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("Disconnect.disconnectBroadcast")
			} else {
				return iface.Goto("Disconnect.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "Disconnect.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ClockUpdate.clockUpdateLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			continue11 := iface.RequireArchetypeResource("ClockUpdate.continue")
			clock11, err := iface.RequireArchetypeResourceRef("ClockUpdate.clock")
			if err != nil {
				return err
			}
			clientId14, err := iface.RequireArchetypeResourceRef("ClockUpdate.clientId")
			if err != nil {
				return err
			}
			msg30 := iface.RequireArchetypeResource("ClockUpdate.msg")
			j9 := iface.RequireArchetypeResource("ClockUpdate.j")
			var condition43 tla.TLAValue
			condition43, err = iface.Read(continue11, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if condition43.AsBool() {
				var condition44 tla.TLAValue
				condition44, err = iface.Read(clientId14, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition45 tla.TLAValue
				condition45, err = iface.Read(clock11, []tla.TLAValue{condition44})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition45, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool() {
					err = iface.Write(continue11, []tla.TLAValue{}, tla.TLA_FALSE)
					if err != nil {
						return err
					}
					return iface.Goto("ClockUpdate.nullCheckSpin")
				} else {
					var exprRead66 tla.TLAValue
					exprRead66, err = iface.Read(clientId14, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead67 tla.TLAValue
					exprRead67, err = iface.Read(clock11, []tla.TLAValue{exprRead66})
					if err != nil {
						return err
					}
					var indexRead13 tla.TLAValue
					indexRead13, err = iface.Read(clientId14, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(clock11, []tla.TLAValue{indexRead13}, tla.TLA_PlusSymbol(exprRead67, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					var exprRead68 tla.TLAValue
					exprRead68, err = iface.Read(clientId14, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead69 tla.TLAValue
					exprRead69, err = iface.Read(clientId14, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead70 tla.TLAValue
					exprRead70, err = iface.Read(clock11, []tla.TLAValue{exprRead69})
					if err != nil {
						return err
					}
					err = iface.Write(msg30, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("op"), iface.GetConstant("NULL_MSG")()},
						{tla.MakeTLAString("client"), exprRead68},
						{tla.MakeTLAString("timestamp"), exprRead70},
					}))
					if err != nil {
						return err
					}
					err = iface.Write(j9, []tla.TLAValue{}, tla.MakeTLANumber(0))
					if err != nil {
						return err
					}
					return iface.Goto("ClockUpdate.nullBroadcast")
				}
				// no statements
			} else {
				return iface.Goto("ClockUpdate.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ClockUpdate.nullBroadcast",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			j10 := iface.RequireArchetypeResource("ClockUpdate.j")
			clock15, err := iface.RequireArchetypeResourceRef("ClockUpdate.clock")
			if err != nil {
				return err
			}
			clientId19, err := iface.RequireArchetypeResourceRef("ClockUpdate.clientId")
			if err != nil {
				return err
			}
			replicas3, err := iface.RequireArchetypeResourceRef("ClockUpdate.replicas")
			if err != nil {
				return err
			}
			msg31 := iface.RequireArchetypeResource("ClockUpdate.msg")
			var condition46 tla.TLAValue
			condition46, err = iface.Read(j10, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition47 tla.TLAValue
			condition47, err = iface.Read(clientId19, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition48 tla.TLAValue
			condition48, err = iface.Read(clock15, []tla.TLAValue{condition47})
			if err != nil {
				return err
			}
			if tla.MakeTLABool(tla.TLA_LessThanOrEqualSymbol(condition46, tla.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeTLANumber(1))).AsBool() && tla.TLA_NotEqualsSymbol(condition48, tla.TLA_NegationSymbol(tla.MakeTLANumber(1))).AsBool()).AsBool() {
				var exprRead71 tla.TLAValue
				exprRead71, err = iface.Read(msg31, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead14 tla.TLAValue
				indexRead14, err = iface.Read(j10, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas3, []tla.TLAValue{indexRead14}, exprRead71)
				if err != nil {
					return err
				}
				var exprRead72 tla.TLAValue
				exprRead72, err = iface.Read(j10, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(j10, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead72, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("ClockUpdate.nullBroadcast")
			} else {
				return iface.Goto("ClockUpdate.nullCheckSpin")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ClockUpdate.nullCheckSpin",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			spin1 := iface.RequireArchetypeResource("ClockUpdate.spin")
			continue13 := iface.RequireArchetypeResource("ClockUpdate.continue")
			var condition49 tla.TLAValue
			condition49, err = iface.Read(spin1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LogicalNotSymbol(condition49).AsBool() {
				err = iface.Write(continue13, []tla.TLAValue{}, tla.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("ClockUpdate.clockUpdateLoop")
			} else {
				return iface.Goto("ClockUpdate.clockUpdateLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ClockUpdate.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AReplica = distsys.MPCalArchetype{
	Name:              "AReplica",
	Label:             "AReplica.replicaLoop",
	RequiredRefParams: []string{"AReplica.clients", "AReplica.replicas", "AReplica.kv"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AReplica.liveClients", ClientSet(iface))
		iface.EnsureArchetypeResourceLocal("AReplica.pendingRequests", tla.MakeTLAFunction([]tla.TLAValue{iface.ReadArchetypeResourceLocal("AReplica.liveClients")}, func(args []tla.TLAValue) tla.TLAValue {
			var c0 tla.TLAValue = args[0]
			_ = c0
			return tla.MakeTLATuple()
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.stableMessages", tla.MakeTLATuple())
		iface.EnsureArchetypeResourceLocal("AReplica.i", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.firstPending", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.timestamp", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.nextClient", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.lowestPending", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.chooseMessage", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.currentClocks", tla.MakeTLAFunction([]tla.TLAValue{iface.ReadArchetypeResourceLocal("AReplica.liveClients")}, func(args0 []tla.TLAValue) tla.TLAValue {
			var c1 tla.TLAValue = args0[0]
			_ = c1
			return tla.MakeTLANumber(0)
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.minClock", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.continue", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.pendingClients", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.clientsIter", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.ok", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.key", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.val", tla.TLAValue{})
	},
}

var Get = distsys.MPCalArchetype{
	Name:              "Get",
	Label:             "Get.getLoop",
	RequiredRefParams: []string{"Get.clientId", "Get.replicas", "Get.clients", "Get.clock", "Get.outside"},
	RequiredValParams: []string{"Get.key", "Get.spin"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("Get.continue", tla.TLA_TRUE)
		iface.EnsureArchetypeResourceLocal("Get.getReq", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Get.getResp", tla.TLAValue{})
	},
}

var Put = distsys.MPCalArchetype{
	Name:              "Put",
	Label:             "Put.putLoop",
	RequiredRefParams: []string{"Put.clientId", "Put.replicas", "Put.clients", "Put.clock", "Put.outside"},
	RequiredValParams: []string{"Put.key", "Put.value", "Put.spin"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("Put.continue", tla.TLA_TRUE)
		iface.EnsureArchetypeResourceLocal("Put.i", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Put.j", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Put.putReq", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Put.putResp", tla.TLAValue{})
	},
}

var Disconnect = distsys.MPCalArchetype{
	Name:              "Disconnect",
	Label:             "Disconnect.sendDisconnectRequest",
	RequiredRefParams: []string{"Disconnect.clientId", "Disconnect.replicas", "Disconnect.clock"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("Disconnect.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Disconnect.j", tla.TLAValue{})
	},
}

var ClockUpdate = distsys.MPCalArchetype{
	Name:              "ClockUpdate",
	Label:             "ClockUpdate.clockUpdateLoop",
	RequiredRefParams: []string{"ClockUpdate.clientId", "ClockUpdate.replicas", "ClockUpdate.clock"},
	RequiredValParams: []string{"ClockUpdate.spin"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ClockUpdate.continue", tla.TLA_TRUE)
		iface.EnsureArchetypeResourceLocal("ClockUpdate.j", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("ClockUpdate.msg", tla.TLAValue{})
	},
}
