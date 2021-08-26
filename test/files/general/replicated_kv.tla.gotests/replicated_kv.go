package replicatedkv

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

func KeySpace(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLASet(iface.GetConstant("GET_KEY")(), iface.GetConstant("PUT_KEY")())
}
func GET_ORDER(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(0)
}
func PUT_ORDER(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}
func DISCONNECT_ORDER(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}
func NULL_ORDER(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}
func GetSet(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_MinusSymbol(iface.GetConstant("NUM_CLIENTS")(), distsys.NewTLANumber(1))))
}
func PutSet(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")()), distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_MinusSymbol(distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(2), iface.GetConstant("NUM_CLIENTS")()), distsys.NewTLANumber(1))))
}
func DisconnectSet(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(2), iface.GetConstant("NUM_CLIENTS")())), distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_MinusSymbol(distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(3), iface.GetConstant("NUM_CLIENTS")()), distsys.NewTLANumber(1))))
}
func NullSet(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(3), iface.GetConstant("NUM_CLIENTS")())), distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_MinusSymbol(distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(4), iface.GetConstant("NUM_CLIENTS")()), distsys.NewTLANumber(1))))
}
func NUM_NODES(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
}
func ReplicaSet(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.NewTLANumber(0), distsys.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.NewTLANumber(1)))
}
func ClientSet(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.TLA_MinusSymbol(NUM_NODES(iface), distsys.NewTLANumber(1)))
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
			if distsys.TLA_TRUE.AsBool() {
				err = iface.Write(stableMessages, []distsys.TLAValue{}, distsys.NewTLATuple())
				if err != nil {
					return err
				}
				err = iface.Write(continue0, []distsys.TLAValue{}, distsys.TLA_TRUE)
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
			var exprRead distsys.TLAValue
			exprRead, err = iface.Read(replicas, []distsys.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []distsys.TLAValue{}, exprRead)
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
			var condition distsys.TLAValue
			condition, err = iface.Read(msg0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("DISCONNECT_MSG")()).AsBool() {
				var exprRead0 distsys.TLAValue
				exprRead0, err = iface.Read(liveClients, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead1 distsys.TLAValue
				exprRead1, err = iface.Read(msg0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(liveClients, []distsys.TLAValue{}, distsys.TLA_BackslashSymbol(exprRead0, distsys.NewTLASet(exprRead1.ApplyFunction(distsys.NewTLAString("client")))))
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
			var condition0 distsys.TLAValue
			condition0, err = iface.Read(msg2, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition0.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("GET_MSG")()).AsBool() {
				var condition1 distsys.TLAValue
				condition1, err = iface.Read(msg2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition2 distsys.TLAValue
				condition2, err = iface.Read(liveClients1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_InSymbol(condition1.ApplyFunction(distsys.NewTLAString("client")), condition2).AsBool() {
					return fmt.Errorf("%w: ((msg).client) \\in (liveClients)", distsys.ErrAssertionFailed)
				}
				var exprRead2 distsys.TLAValue
				exprRead2, err = iface.Read(msg2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead distsys.TLAValue
				indexRead, err = iface.Read(msg2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks, []distsys.TLAValue{indexRead.ApplyFunction(distsys.NewTLAString("client"))}, exprRead2.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					return err
				}
				var exprRead3 distsys.TLAValue
				exprRead3, err = iface.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead4 distsys.TLAValue
				exprRead4, err = iface.Read(msg2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead5 distsys.TLAValue
				exprRead5, err = iface.Read(msg2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead0 distsys.TLAValue
				indexRead0, err = iface.Read(msg2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests, []distsys.TLAValue{indexRead0.ApplyFunction(distsys.NewTLAString("client"))}, distsys.TLA_Append(exprRead3.ApplyFunction(exprRead4.ApplyFunction(distsys.NewTLAString("client"))), exprRead5))
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
			var condition3 distsys.TLAValue
			condition3, err = iface.Read(msg9, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition3.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("PUT_MSG")()).AsBool() {
				var exprRead6 distsys.TLAValue
				exprRead6, err = iface.Read(msg9, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead1 distsys.TLAValue
				indexRead1, err = iface.Read(msg9, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks0, []distsys.TLAValue{indexRead1.ApplyFunction(distsys.NewTLAString("client"))}, exprRead6.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					return err
				}
				var exprRead7 distsys.TLAValue
				exprRead7, err = iface.Read(pendingRequests1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead8 distsys.TLAValue
				exprRead8, err = iface.Read(msg9, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead9 distsys.TLAValue
				exprRead9, err = iface.Read(msg9, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead2 distsys.TLAValue
				indexRead2, err = iface.Read(msg9, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests1, []distsys.TLAValue{indexRead2.ApplyFunction(distsys.NewTLAString("client"))}, distsys.TLA_Append(exprRead7.ApplyFunction(exprRead8.ApplyFunction(distsys.NewTLAString("client"))), exprRead9))
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
			var condition4 distsys.TLAValue
			condition4, err = iface.Read(msg15, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition4.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("NULL_MSG")()).AsBool() {
				var exprRead10 distsys.TLAValue
				exprRead10, err = iface.Read(msg15, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead3 distsys.TLAValue
				indexRead3, err = iface.Read(msg15, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks1, []distsys.TLAValue{indexRead3.ApplyFunction(distsys.NewTLAString("client"))}, exprRead10.ApplyFunction(distsys.NewTLAString("timestamp")))
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
			var condition5 distsys.TLAValue
			condition5, err = iface.Read(continue1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if condition5.AsBool() {
				var exprRead11 distsys.TLAValue
				exprRead11, err = iface.Read(liveClients2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead12 distsys.TLAValue
				exprRead12, err = iface.Read(pendingRequests3, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingClients, []distsys.TLAValue{}, distsys.TLASetRefinement(exprRead11, func(elem distsys.TLAValue) bool {
					var c distsys.TLAValue = elem
					_ = c
					return distsys.TLA_GreaterThanSymbol(distsys.TLA_Len(exprRead12.ApplyFunction(c)), distsys.NewTLANumber(0)).AsBool()
				}))
				if err != nil {
					return err
				}
				err = iface.Write(nextClient, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(NUM_NODES(iface), distsys.NewTLANumber(1)))
				if err != nil {
					return err
				}
				var exprRead13 distsys.TLAValue
				exprRead13, err = iface.Read(liveClients2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clientsIter, []distsys.TLAValue{}, exprRead13)
				if err != nil {
					return err
				}
				err = iface.Write(i, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err != nil {
					return err
				}
				err = iface.Write(minClock, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClock")
			} else {
				err = iface.Write(i, []distsys.TLAValue{}, distsys.NewTLANumber(1))
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
			var condition6 distsys.TLAValue
			condition6, err = iface.Read(i1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition7 distsys.TLAValue
			condition7, err = iface.Read(clientsIter0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanSymbol(condition6, distsys.TLA_Cardinality(condition7)).AsBool() {
				var clientRead distsys.TLAValue
				clientRead, err = iface.Read(clientsIter0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var client distsys.TLAValue = clientRead.SelectElement()
				var condition8 distsys.TLAValue
				condition8, err = iface.Read(minClock0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition9 distsys.TLAValue
				condition9, err = iface.Read(currentClocks2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition10 distsys.TLAValue
				condition10, err = iface.Read(minClock0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if distsys.TLA_LogicalOrSymbol(distsys.TLA_EqualsSymbol(condition8, distsys.NewTLANumber(0)), distsys.TLA_LessThanSymbol(condition9.ApplyFunction(client), condition10)).AsBool() {
					var exprRead14 distsys.TLAValue
					exprRead14, err = iface.Read(currentClocks2, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(minClock0, []distsys.TLAValue{}, exprRead14.ApplyFunction(client))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead15 distsys.TLAValue
				exprRead15, err = iface.Read(clientsIter0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clientsIter0, []distsys.TLAValue{}, distsys.TLA_BackslashSymbol(exprRead15, distsys.NewTLASet(client)))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClock")
				// no statements
			} else {
				var exprRead16 distsys.TLAValue
				exprRead16, err = iface.Read(minClock0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(lowestPending, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead16, distsys.NewTLANumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(i1, []distsys.TLAValue{}, distsys.NewTLANumber(0))
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
			var condition11 distsys.TLAValue
			condition11, err = iface.Read(i3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition12 distsys.TLAValue
			condition12, err = iface.Read(pendingClients0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanSymbol(condition11, distsys.TLA_Cardinality(condition12)).AsBool() {
				var clientRead0 distsys.TLAValue
				clientRead0, err = iface.Read(pendingClients0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var client0 distsys.TLAValue = clientRead0.SelectElement()
				var exprRead17 distsys.TLAValue
				exprRead17, err = iface.Read(pendingRequests4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(firstPending, []distsys.TLAValue{}, distsys.TLA_Head(exprRead17.ApplyFunction(client0)))
				if err != nil {
					return err
				}
				var condition13 distsys.TLAValue
				condition13, err = iface.Read(firstPending, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition14 distsys.TLAValue
				condition14, err = iface.Read(firstPending, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_LogicalOrSymbol(distsys.TLA_EqualsSymbol(condition13.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("GET_MSG")()), distsys.TLA_EqualsSymbol(condition14.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("PUT_MSG")())).AsBool() {
					return fmt.Errorf("%w: (((firstPending).op) = (GET_MSG)) \\/ (((firstPending).op) = (PUT_MSG))", distsys.ErrAssertionFailed)
				}
				var exprRead18 distsys.TLAValue
				exprRead18, err = iface.Read(firstPending, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(timestamp, []distsys.TLAValue{}, exprRead18.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					return err
				}
				var condition15 distsys.TLAValue
				condition15, err = iface.Read(timestamp, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition16 distsys.TLAValue
				condition16, err = iface.Read(minClock4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if distsys.TLA_LessThanSymbol(condition15, condition16).AsBool() {
					var exprRead19 distsys.TLAValue
					exprRead19, err = iface.Read(timestamp, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead20 distsys.TLAValue
					exprRead20, err = iface.Read(lowestPending0, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead21 distsys.TLAValue
					exprRead21, err = iface.Read(timestamp, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead22 distsys.TLAValue
					exprRead22, err = iface.Read(lowestPending0, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead23 distsys.TLAValue
					exprRead23, err = iface.Read(nextClient0, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(chooseMessage, []distsys.TLAValue{}, distsys.TLA_LogicalOrSymbol(distsys.TLA_LessThanSymbol(exprRead19, exprRead20), distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(exprRead21, exprRead22), distsys.TLA_LessThanSymbol(client0, exprRead23))))
					if err != nil {
						return err
					}
					var condition17 distsys.TLAValue
					condition17, err = iface.Read(chooseMessage, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					if condition17.AsBool() {
						err = iface.Write(nextClient0, []distsys.TLAValue{}, client0)
						if err != nil {
							return err
						}
						var exprRead24 distsys.TLAValue
						exprRead24, err = iface.Read(timestamp, []distsys.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(lowestPending0, []distsys.TLAValue{}, exprRead24)
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
				var exprRead25 distsys.TLAValue
				exprRead25, err = iface.Read(pendingClients0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingClients0, []distsys.TLAValue{}, distsys.TLA_BackslashSymbol(exprRead25, distsys.NewTLASet(client0)))
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
			var condition18 distsys.TLAValue
			condition18, err = iface.Read(lowestPending3, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition19 distsys.TLAValue
			condition19, err = iface.Read(minClock5, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanSymbol(condition18, condition19).AsBool() {
				var exprRead26 distsys.TLAValue
				exprRead26, err = iface.Read(pendingRequests5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead27 distsys.TLAValue
				exprRead27, err = iface.Read(nextClient2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(msg18, []distsys.TLAValue{}, distsys.TLA_Head(exprRead26.ApplyFunction(exprRead27)))
				if err != nil {
					return err
				}
				var exprRead28 distsys.TLAValue
				exprRead28, err = iface.Read(pendingRequests5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead29 distsys.TLAValue
				exprRead29, err = iface.Read(nextClient2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead4 distsys.TLAValue
				indexRead4, err = iface.Read(nextClient2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests5, []distsys.TLAValue{indexRead4}, distsys.TLA_Tail(exprRead28.ApplyFunction(exprRead29)))
				if err != nil {
					return err
				}
				var exprRead30 distsys.TLAValue
				exprRead30, err = iface.Read(stableMessages0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead31 distsys.TLAValue
				exprRead31, err = iface.Read(msg18, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(stableMessages0, []distsys.TLAValue{}, distsys.TLA_Append(exprRead30, exprRead31))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findStableRequestsLoop")
			} else {
				err = iface.Write(continue2, []distsys.TLAValue{}, distsys.TLA_FALSE)
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
			var condition20 distsys.TLAValue
			condition20, err = iface.Read(i4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition21 distsys.TLAValue
			condition21, err = iface.Read(stableMessages2, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition20, distsys.TLA_Len(condition21)).AsBool() {
				var exprRead32 distsys.TLAValue
				exprRead32, err = iface.Read(stableMessages2, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead33 distsys.TLAValue
				exprRead33, err = iface.Read(i4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(msg20, []distsys.TLAValue{}, exprRead32.ApplyFunction(exprRead33))
				if err != nil {
					return err
				}
				var exprRead34 distsys.TLAValue
				exprRead34, err = iface.Read(i4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(i4, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead34, distsys.NewTLANumber(1)))
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
			var condition22 distsys.TLAValue
			condition22, err = iface.Read(msg21, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition22.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("GET_MSG")()).AsBool() {
				var exprRead35 distsys.TLAValue
				exprRead35, err = iface.Read(msg21, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(key, []distsys.TLAValue{}, exprRead35.ApplyFunction(distsys.NewTLAString("key")))
				if err != nil {
					return err
				}
				var exprRead36 distsys.TLAValue
				exprRead36, err = iface.Read(key, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead37 distsys.TLAValue
				exprRead37, err = iface.Read(kv, []distsys.TLAValue{exprRead36})
				if err != nil {
					return err
				}
				err = iface.Write(val, []distsys.TLAValue{}, exprRead37)
				if err != nil {
					return err
				}
				var exprRead38 distsys.TLAValue
				exprRead38, err = iface.Read(val, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead5 distsys.TLAValue
				indexRead5, err = iface.Read(msg21, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clients, []distsys.TLAValue{indexRead5.ApplyFunction(distsys.NewTLAString("reply_to"))}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("type"), iface.GetConstant("GET_RESPONSE")()},
					{distsys.NewTLAString("result"), exprRead38},
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
			var condition23 distsys.TLAValue
			condition23, err = iface.Read(msg24, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition23.ApplyFunction(distsys.NewTLAString("op")), iface.GetConstant("PUT_MSG")()).AsBool() {
				var exprRead39 distsys.TLAValue
				exprRead39, err = iface.Read(msg24, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(key1, []distsys.TLAValue{}, exprRead39.ApplyFunction(distsys.NewTLAString("key")))
				if err != nil {
					return err
				}
				var exprRead40 distsys.TLAValue
				exprRead40, err = iface.Read(msg24, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(val1, []distsys.TLAValue{}, exprRead40.ApplyFunction(distsys.NewTLAString("value")))
				if err != nil {
					return err
				}
				var exprRead41 distsys.TLAValue
				exprRead41, err = iface.Read(val1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead6 distsys.TLAValue
				indexRead6, err = iface.Read(key1, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(kv0, []distsys.TLAValue{indexRead6}, exprRead41)
				if err != nil {
					return err
				}
				var exprRead42 distsys.TLAValue
				exprRead42, err = iface.Read(ok, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead7 distsys.TLAValue
				indexRead7, err = iface.Read(msg24, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clients0, []distsys.TLAValue{indexRead7.ApplyFunction(distsys.NewTLAString("reply_to"))}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("type"), iface.GetConstant("PUT_RESPONSE")()},
					{distsys.NewTLAString("result"), exprRead42},
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
			var condition24 distsys.TLAValue
			condition24, err = iface.Read(continue3, []distsys.TLAValue{})
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
			var condition25 distsys.TLAValue
			condition25, err = iface.Read(clientId, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition26 distsys.TLAValue
			condition26, err = iface.Read(clock, []distsys.TLAValue{condition25})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition26, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
				err = iface.Write(continue4, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			} else {
				var exprRead43 distsys.TLAValue
				exprRead43, err = iface.Read(clientId, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead44 distsys.TLAValue
				exprRead44, err = iface.Read(clock, []distsys.TLAValue{exprRead43})
				if err != nil {
					return err
				}
				var indexRead8 distsys.TLAValue
				indexRead8, err = iface.Read(clientId, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clock, []distsys.TLAValue{indexRead8}, distsys.TLA_PlusSymbol(exprRead44, distsys.NewTLANumber(1)))
				if err != nil {
					return err
				}
				var exprRead45 distsys.TLAValue
				exprRead45, err = iface.Read(key3, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead46 distsys.TLAValue
				exprRead46, err = iface.Read(clientId, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead47 distsys.TLAValue
				exprRead47, err = iface.Read(clientId, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead48 distsys.TLAValue
				exprRead48, err = iface.Read(clock, []distsys.TLAValue{exprRead47})
				if err != nil {
					return err
				}
				err = iface.Write(getReq, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("op"), iface.GetConstant("GET_MSG")()},
					{distsys.NewTLAString("key"), exprRead45},
					{distsys.NewTLAString("client"), exprRead46},
					{distsys.NewTLAString("timestamp"), exprRead48},
					{distsys.NewTLAString("reply_to"), iface.Self()},
				}))
				if err != nil {
					return err
				}
				var dst distsys.TLAValue = ReplicaSet(iface).SelectElement()
				var exprRead49 distsys.TLAValue
				exprRead49, err = iface.Read(getReq, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas0, []distsys.TLAValue{dst}, exprRead49)
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
			var condition27 distsys.TLAValue
			condition27, err = iface.Read(clientId4, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition28 distsys.TLAValue
			condition28, err = iface.Read(clock3, []distsys.TLAValue{condition27})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition28, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
				err = iface.Write(continue5, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			} else {
				var exprRead50 distsys.TLAValue
				exprRead50, err = iface.Read(clients1, []distsys.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(getResp, []distsys.TLAValue{}, exprRead50)
				if err != nil {
					return err
				}
				var condition29 distsys.TLAValue
				condition29, err = iface.Read(getResp, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				if !distsys.TLA_EqualsSymbol(condition29.ApplyFunction(distsys.NewTLAString("type")), iface.GetConstant("GET_RESPONSE")()).AsBool() {
					return fmt.Errorf("%w: ((getResp).type) = (GET_RESPONSE)", distsys.ErrAssertionFailed)
				}
				var exprRead51 distsys.TLAValue
				exprRead51, err = iface.Read(getResp, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(outside, []distsys.TLAValue{}, exprRead51.ApplyFunction(distsys.NewTLAString("result")))
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
			var condition30 distsys.TLAValue
			condition30, err = iface.Read(spin, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalNotSymbol(condition30).AsBool() {
				err = iface.Write(continue6, []distsys.TLAValue{}, distsys.TLA_FALSE)
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
			var condition31 distsys.TLAValue
			condition31, err = iface.Read(continue7, []distsys.TLAValue{})
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
			var condition32 distsys.TLAValue
			condition32, err = iface.Read(clientId5, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition33 distsys.TLAValue
			condition33, err = iface.Read(clock4, []distsys.TLAValue{condition32})
			if err != nil {
				return err
			}
			if distsys.TLA_EqualsSymbol(condition33, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
				err = iface.Write(continue8, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Put.putCheckSpin")
			} else {
				var exprRead52 distsys.TLAValue
				exprRead52, err = iface.Read(clientId5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead53 distsys.TLAValue
				exprRead53, err = iface.Read(clock4, []distsys.TLAValue{exprRead52})
				if err != nil {
					return err
				}
				var indexRead9 distsys.TLAValue
				indexRead9, err = iface.Read(clientId5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(clock4, []distsys.TLAValue{indexRead9}, distsys.TLA_PlusSymbol(exprRead53, distsys.NewTLANumber(1)))
				if err != nil {
					return err
				}
				var exprRead54 distsys.TLAValue
				exprRead54, err = iface.Read(key4, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead55 distsys.TLAValue
				exprRead55, err = iface.Read(value, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead56 distsys.TLAValue
				exprRead56, err = iface.Read(clientId5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead57 distsys.TLAValue
				exprRead57, err = iface.Read(clientId5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead58 distsys.TLAValue
				exprRead58, err = iface.Read(clock4, []distsys.TLAValue{exprRead57})
				if err != nil {
					return err
				}
				err = iface.Write(putReq, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("op"), iface.GetConstant("PUT_MSG")()},
					{distsys.NewTLAString("key"), exprRead54},
					{distsys.NewTLAString("value"), exprRead55},
					{distsys.NewTLAString("client"), exprRead56},
					{distsys.NewTLAString("timestamp"), exprRead58},
					{distsys.NewTLAString("reply_to"), iface.Self()},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(i8, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err != nil {
					return err
				}
				err = iface.Write(j, []distsys.TLAValue{}, distsys.NewTLANumber(0))
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
			var condition34 distsys.TLAValue
			condition34, err = iface.Read(j0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition35 distsys.TLAValue
			condition35, err = iface.Read(clientId10, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition36 distsys.TLAValue
			condition36, err = iface.Read(clock8, []distsys.TLAValue{condition35})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_LessThanOrEqualSymbol(condition34, distsys.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.NewTLANumber(1))), distsys.TLA_NotEqualsSymbol(condition36, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))).AsBool() {
				var exprRead59 distsys.TLAValue
				exprRead59, err = iface.Read(putReq0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead10 distsys.TLAValue
				indexRead10, err = iface.Read(j0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas1, []distsys.TLAValue{indexRead10}, exprRead59)
				if err != nil {
					return err
				}
				var exprRead60 distsys.TLAValue
				exprRead60, err = iface.Read(j0, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(j0, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead60, distsys.NewTLANumber(1)))
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
			var condition37 distsys.TLAValue
			condition37, err = iface.Read(i9, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LessThanSymbol(condition37, distsys.TLA_Cardinality(ReplicaSet(iface))).AsBool() {
				var condition38 distsys.TLAValue
				condition38, err = iface.Read(clientId11, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition39 distsys.TLAValue
				condition39, err = iface.Read(clock9, []distsys.TLAValue{condition38})
				if err != nil {
					return err
				}
				if distsys.TLA_EqualsSymbol(condition39, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
					err = iface.Write(continue9, []distsys.TLAValue{}, distsys.TLA_FALSE)
					if err != nil {
						return err
					}
					return iface.Goto("Put.putLoop")
				} else {
					var exprRead61 distsys.TLAValue
					exprRead61, err = iface.Read(clients2, []distsys.TLAValue{iface.Self()})
					if err != nil {
						return err
					}
					err = iface.Write(putResp, []distsys.TLAValue{}, exprRead61)
					if err != nil {
						return err
					}
					var condition40 distsys.TLAValue
					condition40, err = iface.Read(putResp, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					if !distsys.TLA_EqualsSymbol(condition40.ApplyFunction(distsys.NewTLAString("type")), iface.GetConstant("PUT_RESPONSE")()).AsBool() {
						return fmt.Errorf("%w: ((putResp).type) = (PUT_RESPONSE)", distsys.ErrAssertionFailed)
					}
					var exprRead62 distsys.TLAValue
					exprRead62, err = iface.Read(i9, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(i9, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead62, distsys.NewTLANumber(1)))
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
			err = iface.Write(outside0, []distsys.TLAValue{}, iface.GetConstant("PUT_RESPONSE")())
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
			var condition41 distsys.TLAValue
			condition41, err = iface.Read(spin0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalNotSymbol(condition41).AsBool() {
				err = iface.Write(continue10, []distsys.TLAValue{}, distsys.TLA_FALSE)
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
			var exprRead63 distsys.TLAValue
			exprRead63, err = iface.Read(clientId12, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(msg28, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("op"), iface.GetConstant("DISCONNECT_MSG")()},
				{distsys.NewTLAString("client"), exprRead63},
			}))
			if err != nil {
				return err
			}
			var indexRead11 distsys.TLAValue
			indexRead11, err = iface.Read(clientId12, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(clock10, []distsys.TLAValue{indexRead11}, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))
			if err != nil {
				return err
			}
			err = iface.Write(j4, []distsys.TLAValue{}, distsys.NewTLANumber(0))
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
			var condition42 distsys.TLAValue
			condition42, err = iface.Read(j5, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_LessThanOrEqualSymbol(condition42, distsys.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.NewTLANumber(1))), distsys.TLA_NotEqualsSymbol(distsys.NewTLANumber(0), distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))).AsBool() {
				var exprRead64 distsys.TLAValue
				exprRead64, err = iface.Read(msg29, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead12 distsys.TLAValue
				indexRead12, err = iface.Read(j5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas2, []distsys.TLAValue{indexRead12}, exprRead64)
				if err != nil {
					return err
				}
				var exprRead65 distsys.TLAValue
				exprRead65, err = iface.Read(j5, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(j5, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead65, distsys.NewTLANumber(1)))
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
			var condition43 distsys.TLAValue
			condition43, err = iface.Read(continue11, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if condition43.AsBool() {
				var condition44 distsys.TLAValue
				condition44, err = iface.Read(clientId14, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var condition45 distsys.TLAValue
				condition45, err = iface.Read(clock11, []distsys.TLAValue{condition44})
				if err != nil {
					return err
				}
				if distsys.TLA_EqualsSymbol(condition45, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
					err = iface.Write(continue11, []distsys.TLAValue{}, distsys.TLA_FALSE)
					if err != nil {
						return err
					}
					return iface.Goto("ClockUpdate.nullCheckSpin")
				} else {
					var exprRead66 distsys.TLAValue
					exprRead66, err = iface.Read(clientId14, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead67 distsys.TLAValue
					exprRead67, err = iface.Read(clock11, []distsys.TLAValue{exprRead66})
					if err != nil {
						return err
					}
					var indexRead13 distsys.TLAValue
					indexRead13, err = iface.Read(clientId14, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(clock11, []distsys.TLAValue{indexRead13}, distsys.TLA_PlusSymbol(exprRead67, distsys.NewTLANumber(1)))
					if err != nil {
						return err
					}
					var exprRead68 distsys.TLAValue
					exprRead68, err = iface.Read(clientId14, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead69 distsys.TLAValue
					exprRead69, err = iface.Read(clientId14, []distsys.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead70 distsys.TLAValue
					exprRead70, err = iface.Read(clock11, []distsys.TLAValue{exprRead69})
					if err != nil {
						return err
					}
					err = iface.Write(msg30, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
						{distsys.NewTLAString("op"), iface.GetConstant("NULL_MSG")()},
						{distsys.NewTLAString("client"), exprRead68},
						{distsys.NewTLAString("timestamp"), exprRead70},
					}))
					if err != nil {
						return err
					}
					err = iface.Write(j9, []distsys.TLAValue{}, distsys.NewTLANumber(0))
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
			var condition46 distsys.TLAValue
			condition46, err = iface.Read(j10, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition47 distsys.TLAValue
			condition47, err = iface.Read(clientId19, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var condition48 distsys.TLAValue
			condition48, err = iface.Read(clock15, []distsys.TLAValue{condition47})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_LessThanOrEqualSymbol(condition46, distsys.TLA_MinusSymbol(iface.GetConstant("NUM_REPLICAS")(), distsys.NewTLANumber(1))), distsys.TLA_NotEqualsSymbol(condition48, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))).AsBool() {
				var exprRead71 distsys.TLAValue
				exprRead71, err = iface.Read(msg31, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				var indexRead14 distsys.TLAValue
				indexRead14, err = iface.Read(j10, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(replicas3, []distsys.TLAValue{indexRead14}, exprRead71)
				if err != nil {
					return err
				}
				var exprRead72 distsys.TLAValue
				exprRead72, err = iface.Read(j10, []distsys.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(j10, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead72, distsys.NewTLANumber(1)))
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
			var condition49 distsys.TLAValue
			condition49, err = iface.Read(spin1, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			if distsys.TLA_LogicalNotSymbol(condition49).AsBool() {
				err = iface.Write(continue13, []distsys.TLAValue{}, distsys.TLA_FALSE)
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
		iface.EnsureArchetypeResourceLocal("AReplica.pendingRequests", distsys.NewTLAFunction([]distsys.TLAValue{iface.ReadArchetypeResourceLocal("AReplica.liveClients")}, func(args []distsys.TLAValue) distsys.TLAValue {
			var c0 distsys.TLAValue = args[0]
			_ = c0
			return distsys.NewTLATuple()
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.stableMessages", distsys.NewTLATuple())
		iface.EnsureArchetypeResourceLocal("AReplica.i", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.firstPending", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.timestamp", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.nextClient", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.lowestPending", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.chooseMessage", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.currentClocks", distsys.NewTLAFunction([]distsys.TLAValue{iface.ReadArchetypeResourceLocal("AReplica.liveClients")}, func(args0 []distsys.TLAValue) distsys.TLAValue {
			var c1 distsys.TLAValue = args0[0]
			_ = c1
			return distsys.NewTLANumber(0)
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.minClock", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.continue", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.pendingClients", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.clientsIter", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.msg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.ok", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.key", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AReplica.val", distsys.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("Get.continue", distsys.TLA_TRUE)
		iface.EnsureArchetypeResourceLocal("Get.getReq", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Get.getResp", distsys.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("Put.continue", distsys.TLA_TRUE)
		iface.EnsureArchetypeResourceLocal("Put.i", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Put.j", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Put.putReq", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Put.putResp", distsys.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("Disconnect.msg", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("Disconnect.j", distsys.TLAValue{})
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
		iface.EnsureArchetypeResourceLocal("ClockUpdate.continue", distsys.TLA_TRUE)
		iface.EnsureArchetypeResourceLocal("ClockUpdate.j", distsys.TLAValue{})
		iface.EnsureArchetypeResourceLocal("ClockUpdate.msg", distsys.TLAValue{})
	},
}
