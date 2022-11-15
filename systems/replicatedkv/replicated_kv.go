package replicatedkv

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func KeySpace(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet(iface.GetConstant("GET_KEY")(), iface.GetConstant("PUT_KEY")())
}
func GET_ORDER(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func PUT_ORDER(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func DISCONNECT_ORDER(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func NULL_ORDER(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(3)
}
func GetSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleMinusSymbol(iface.GetConstant("NUM_CLIENTS")(), tla.MakeNumber(1))))
}
func PutSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")()), tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleMinusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(2), iface.GetConstant("NUM_CLIENTS")()), tla.MakeNumber(1))))
}
func DisconnectSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleAsteriskSymbol(tla.MakeNumber(2), iface.GetConstant("NUM_CLIENTS")())), tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleMinusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(3), iface.GetConstant("NUM_CLIENTS")()), tla.MakeNumber(1))))
}
func NullSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleAsteriskSymbol(tla.MakeNumber(3), iface.GetConstant("NUM_CLIENTS")())), tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleMinusSymbol(tla.ModuleAsteriskSymbol(tla.MakeNumber(4), iface.GetConstant("NUM_CLIENTS")()), tla.MakeNumber(1))))
}
func NUM_NODES(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModulePlusSymbol(iface.GetConstant("NUM_REPLICAS")(), iface.GetConstant("NUM_CLIENTS")())
}
func ReplicaSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.MakeNumber(0), tla.ModuleMinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeNumber(1)))
}
func ClientSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.ModuleMinusSymbol(NUM_NODES(iface), tla.MakeNumber(1)))
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
			if tla.ModuleTRUE.AsBool() {
				err = iface.Write(stableMessages, nil, tla.MakeTuple())
				if err != nil {
					return err
				}
				err = iface.Write(continue0, nil, tla.ModuleTRUE)
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
			var exprRead tla.Value
			exprRead, err = iface.Read(replicas, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, nil, exprRead)
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
			var condition tla.Value
			condition, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition.ApplyFunction(tla.MakeString("op")), iface.GetConstant("DISCONNECT_MSG")()).AsBool() {
				var exprRead0 tla.Value
				exprRead0, err = iface.Read(liveClients, nil)
				if err != nil {
					return err
				}
				var exprRead1 tla.Value
				exprRead1, err = iface.Read(msg0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(liveClients, nil, tla.ModuleBackslashSymbol(exprRead0, tla.MakeSet(exprRead1.ApplyFunction(tla.MakeString("client")))))
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
			var condition0 tla.Value
			condition0, err = iface.Read(msg2, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition0.ApplyFunction(tla.MakeString("op")), iface.GetConstant("GET_MSG")()).AsBool() {
				var condition1 tla.Value
				condition1, err = iface.Read(msg2, nil)
				if err != nil {
					return err
				}
				var condition2 tla.Value
				condition2, err = iface.Read(liveClients1, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleInSymbol(condition1.ApplyFunction(tla.MakeString("client")), condition2).AsBool() {
					return fmt.Errorf("%w: ((msg).client) \\in (liveClients)", distsys.ErrAssertionFailed)
				}
				var exprRead2 tla.Value
				exprRead2, err = iface.Read(msg2, nil)
				if err != nil {
					return err
				}
				var indexRead tla.Value
				indexRead, err = iface.Read(msg2, nil)
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks, []tla.Value{indexRead.ApplyFunction(tla.MakeString("client"))}, exprRead2.ApplyFunction(tla.MakeString("timestamp")))
				if err != nil {
					return err
				}
				var exprRead3 tla.Value
				exprRead3, err = iface.Read(pendingRequests, nil)
				if err != nil {
					return err
				}
				var exprRead4 tla.Value
				exprRead4, err = iface.Read(msg2, nil)
				if err != nil {
					return err
				}
				var exprRead5 tla.Value
				exprRead5, err = iface.Read(msg2, nil)
				if err != nil {
					return err
				}
				var indexRead0 tla.Value
				indexRead0, err = iface.Read(msg2, nil)
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests, []tla.Value{indexRead0.ApplyFunction(tla.MakeString("client"))}, tla.ModuleAppend(exprRead3.ApplyFunction(exprRead4.ApplyFunction(tla.MakeString("client"))), exprRead5))
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
			var condition3 tla.Value
			condition3, err = iface.Read(msg9, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition3.ApplyFunction(tla.MakeString("op")), iface.GetConstant("PUT_MSG")()).AsBool() {
				var exprRead6 tla.Value
				exprRead6, err = iface.Read(msg9, nil)
				if err != nil {
					return err
				}
				var indexRead1 tla.Value
				indexRead1, err = iface.Read(msg9, nil)
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks0, []tla.Value{indexRead1.ApplyFunction(tla.MakeString("client"))}, exprRead6.ApplyFunction(tla.MakeString("timestamp")))
				if err != nil {
					return err
				}
				var exprRead7 tla.Value
				exprRead7, err = iface.Read(pendingRequests1, nil)
				if err != nil {
					return err
				}
				var exprRead8 tla.Value
				exprRead8, err = iface.Read(msg9, nil)
				if err != nil {
					return err
				}
				var exprRead9 tla.Value
				exprRead9, err = iface.Read(msg9, nil)
				if err != nil {
					return err
				}
				var indexRead2 tla.Value
				indexRead2, err = iface.Read(msg9, nil)
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests1, []tla.Value{indexRead2.ApplyFunction(tla.MakeString("client"))}, tla.ModuleAppend(exprRead7.ApplyFunction(exprRead8.ApplyFunction(tla.MakeString("client"))), exprRead9))
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
			var condition4 tla.Value
			condition4, err = iface.Read(msg15, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition4.ApplyFunction(tla.MakeString("op")), iface.GetConstant("NULL_MSG")()).AsBool() {
				var exprRead10 tla.Value
				exprRead10, err = iface.Read(msg15, nil)
				if err != nil {
					return err
				}
				var indexRead3 tla.Value
				indexRead3, err = iface.Read(msg15, nil)
				if err != nil {
					return err
				}
				err = iface.Write(currentClocks1, []tla.Value{indexRead3.ApplyFunction(tla.MakeString("client"))}, exprRead10.ApplyFunction(tla.MakeString("timestamp")))
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
			var condition5 tla.Value
			condition5, err = iface.Read(continue1, nil)
			if err != nil {
				return err
			}
			if condition5.AsBool() {
				var exprRead11 tla.Value
				exprRead11, err = iface.Read(liveClients2, nil)
				if err != nil {
					return err
				}
				var exprRead12 tla.Value
				exprRead12, err = iface.Read(pendingRequests3, nil)
				if err != nil {
					return err
				}
				err = iface.Write(pendingClients, nil, tla.SetRefinement(exprRead11, func(elem tla.Value) bool {
					var c tla.Value = elem
					_ = c
					return tla.ModuleGreaterThanSymbol(tla.ModuleLen(exprRead12.ApplyFunction(c)), tla.MakeNumber(0)).AsBool()
				}))
				if err != nil {
					return err
				}
				err = iface.Write(nextClient, nil, tla.ModulePlusSymbol(NUM_NODES(iface), tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				var exprRead13 tla.Value
				exprRead13, err = iface.Read(liveClients2, nil)
				if err != nil {
					return err
				}
				err = iface.Write(clientsIter, nil, exprRead13)
				if err != nil {
					return err
				}
				err = iface.Write(i, nil, tla.MakeNumber(0))
				if err != nil {
					return err
				}
				err = iface.Write(minClock, nil, tla.MakeNumber(0))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClock")
			} else {
				err = iface.Write(i, nil, tla.MakeNumber(1))
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
			var condition6 tla.Value
			condition6, err = iface.Read(i1, nil)
			if err != nil {
				return err
			}
			var condition7 tla.Value
			condition7, err = iface.Read(clientsIter0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition6, tla.ModuleCardinality(condition7)).AsBool() {
				var clientRead tla.Value
				clientRead, err = iface.Read(clientsIter0, nil)
				if err != nil {
					return err
				}
				var clientRead0 = clientRead
				if clientRead0.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var client tla.Value = clientRead0.SelectElement(iface.NextFairnessCounter("AReplica.findMinClock.0", uint(clientRead0.AsSet().Len())))
				_ = client
				var condition8 tla.Value
				condition8, err = iface.Read(minClock0, nil)
				if err != nil {
					return err
				}
				var condition9 tla.Value
				condition9, err = iface.Read(currentClocks2, nil)
				if err != nil {
					return err
				}
				var condition10 tla.Value
				condition10, err = iface.Read(minClock0, nil)
				if err != nil {
					return err
				}
				if tla.MakeBool(tla.ModuleEqualsSymbol(condition8, tla.MakeNumber(0)).AsBool() || tla.ModuleLessThanSymbol(condition9.ApplyFunction(client), condition10).AsBool()).AsBool() {
					var exprRead14 tla.Value
					exprRead14, err = iface.Read(currentClocks2, nil)
					if err != nil {
						return err
					}
					err = iface.Write(minClock0, nil, exprRead14.ApplyFunction(client))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead15 tla.Value
				exprRead15, err = iface.Read(clientsIter0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(clientsIter0, nil, tla.ModuleBackslashSymbol(exprRead15, tla.MakeSet(client)))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findMinClock")
				// no statements
			} else {
				var exprRead16 tla.Value
				exprRead16, err = iface.Read(minClock0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(lowestPending, nil, tla.ModulePlusSymbol(exprRead16, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(i1, nil, tla.MakeNumber(0))
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
			var condition11 tla.Value
			condition11, err = iface.Read(i3, nil)
			if err != nil {
				return err
			}
			var condition12 tla.Value
			condition12, err = iface.Read(pendingClients0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition11, tla.ModuleCardinality(condition12)).AsBool() {
				var clientRead1 tla.Value
				clientRead1, err = iface.Read(pendingClients0, nil)
				if err != nil {
					return err
				}
				var clientRead2 = clientRead1
				if clientRead2.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var client0 tla.Value = clientRead2.SelectElement(iface.NextFairnessCounter("AReplica.findMinClient.0", uint(clientRead2.AsSet().Len())))
				_ = client0
				var exprRead17 tla.Value
				exprRead17, err = iface.Read(pendingRequests4, nil)
				if err != nil {
					return err
				}
				err = iface.Write(firstPending, nil, tla.ModuleHead(exprRead17.ApplyFunction(client0)))
				if err != nil {
					return err
				}
				var condition13 tla.Value
				condition13, err = iface.Read(firstPending, nil)
				if err != nil {
					return err
				}
				var condition14 tla.Value
				condition14, err = iface.Read(firstPending, nil)
				if err != nil {
					return err
				}
				if !tla.MakeBool(tla.ModuleEqualsSymbol(condition13.ApplyFunction(tla.MakeString("op")), iface.GetConstant("GET_MSG")()).AsBool() || tla.ModuleEqualsSymbol(condition14.ApplyFunction(tla.MakeString("op")), iface.GetConstant("PUT_MSG")()).AsBool()).AsBool() {
					return fmt.Errorf("%w: (((firstPending).op) = (GET_MSG)) \\/ (((firstPending).op) = (PUT_MSG))", distsys.ErrAssertionFailed)
				}
				var exprRead18 tla.Value
				exprRead18, err = iface.Read(firstPending, nil)
				if err != nil {
					return err
				}
				err = iface.Write(timestamp, nil, exprRead18.ApplyFunction(tla.MakeString("timestamp")))
				if err != nil {
					return err
				}
				var condition15 tla.Value
				condition15, err = iface.Read(timestamp, nil)
				if err != nil {
					return err
				}
				var condition16 tla.Value
				condition16, err = iface.Read(minClock4, nil)
				if err != nil {
					return err
				}
				if tla.ModuleLessThanSymbol(condition15, condition16).AsBool() {
					var exprRead19 tla.Value
					exprRead19, err = iface.Read(timestamp, nil)
					if err != nil {
						return err
					}
					var exprRead20 tla.Value
					exprRead20, err = iface.Read(lowestPending0, nil)
					if err != nil {
						return err
					}
					var exprRead21 tla.Value
					exprRead21, err = iface.Read(timestamp, nil)
					if err != nil {
						return err
					}
					var exprRead22 tla.Value
					exprRead22, err = iface.Read(lowestPending0, nil)
					if err != nil {
						return err
					}
					var exprRead23 tla.Value
					exprRead23, err = iface.Read(nextClient0, nil)
					if err != nil {
						return err
					}
					err = iface.Write(chooseMessage, nil, tla.MakeBool(tla.ModuleLessThanSymbol(exprRead19, exprRead20).AsBool() || tla.MakeBool(tla.ModuleEqualsSymbol(exprRead21, exprRead22).AsBool() && tla.ModuleLessThanSymbol(client0, exprRead23).AsBool()).AsBool()))
					if err != nil {
						return err
					}
					var condition17 tla.Value
					condition17, err = iface.Read(chooseMessage, nil)
					if err != nil {
						return err
					}
					if condition17.AsBool() {
						err = iface.Write(nextClient0, nil, client0)
						if err != nil {
							return err
						}
						var exprRead24 tla.Value
						exprRead24, err = iface.Read(timestamp, nil)
						if err != nil {
							return err
						}
						err = iface.Write(lowestPending0, nil, exprRead24)
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
				var exprRead25 tla.Value
				exprRead25, err = iface.Read(pendingClients0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(pendingClients0, nil, tla.ModuleBackslashSymbol(exprRead25, tla.MakeSet(client0)))
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
			var condition18 tla.Value
			condition18, err = iface.Read(lowestPending3, nil)
			if err != nil {
				return err
			}
			var condition19 tla.Value
			condition19, err = iface.Read(minClock5, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition18, condition19).AsBool() {
				var exprRead26 tla.Value
				exprRead26, err = iface.Read(pendingRequests5, nil)
				if err != nil {
					return err
				}
				var exprRead27 tla.Value
				exprRead27, err = iface.Read(nextClient2, nil)
				if err != nil {
					return err
				}
				err = iface.Write(msg18, nil, tla.ModuleHead(exprRead26.ApplyFunction(exprRead27)))
				if err != nil {
					return err
				}
				var exprRead28 tla.Value
				exprRead28, err = iface.Read(pendingRequests5, nil)
				if err != nil {
					return err
				}
				var exprRead29 tla.Value
				exprRead29, err = iface.Read(nextClient2, nil)
				if err != nil {
					return err
				}
				var indexRead4 tla.Value
				indexRead4, err = iface.Read(nextClient2, nil)
				if err != nil {
					return err
				}
				err = iface.Write(pendingRequests5, []tla.Value{indexRead4}, tla.ModuleTail(exprRead28.ApplyFunction(exprRead29)))
				if err != nil {
					return err
				}
				var exprRead30 tla.Value
				exprRead30, err = iface.Read(stableMessages0, nil)
				if err != nil {
					return err
				}
				var exprRead31 tla.Value
				exprRead31, err = iface.Read(msg18, nil)
				if err != nil {
					return err
				}
				err = iface.Write(stableMessages0, nil, tla.ModuleAppend(exprRead30, exprRead31))
				if err != nil {
					return err
				}
				return iface.Goto("AReplica.findStableRequestsLoop")
			} else {
				err = iface.Write(continue2, nil, tla.ModuleFALSE)
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
			var condition20 tla.Value
			condition20, err = iface.Read(i4, nil)
			if err != nil {
				return err
			}
			var condition21 tla.Value
			condition21, err = iface.Read(stableMessages2, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanOrEqualSymbol(condition20, tla.ModuleLen(condition21)).AsBool() {
				var exprRead32 tla.Value
				exprRead32, err = iface.Read(stableMessages2, nil)
				if err != nil {
					return err
				}
				var exprRead33 tla.Value
				exprRead33, err = iface.Read(i4, nil)
				if err != nil {
					return err
				}
				err = iface.Write(msg20, nil, exprRead32.ApplyFunction(exprRead33))
				if err != nil {
					return err
				}
				var exprRead34 tla.Value
				exprRead34, err = iface.Read(i4, nil)
				if err != nil {
					return err
				}
				err = iface.Write(i4, nil, tla.ModulePlusSymbol(exprRead34, tla.MakeNumber(1)))
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
			var condition22 tla.Value
			condition22, err = iface.Read(msg21, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition22.ApplyFunction(tla.MakeString("op")), iface.GetConstant("GET_MSG")()).AsBool() {
				var exprRead35 tla.Value
				exprRead35, err = iface.Read(msg21, nil)
				if err != nil {
					return err
				}
				err = iface.Write(key, nil, exprRead35.ApplyFunction(tla.MakeString("key")))
				if err != nil {
					return err
				}
				var exprRead36 tla.Value
				exprRead36, err = iface.Read(key, nil)
				if err != nil {
					return err
				}
				var exprRead37 tla.Value
				exprRead37, err = iface.Read(kv, []tla.Value{exprRead36})
				if err != nil {
					return err
				}
				err = iface.Write(val, nil, exprRead37)
				if err != nil {
					return err
				}
				var exprRead38 tla.Value
				exprRead38, err = iface.Read(val, nil)
				if err != nil {
					return err
				}
				var indexRead5 tla.Value
				indexRead5, err = iface.Read(msg21, nil)
				if err != nil {
					return err
				}
				err = iface.Write(clients, []tla.Value{indexRead5.ApplyFunction(tla.MakeString("reply_to"))}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("type"), iface.GetConstant("GET_RESPONSE")()},
					{tla.MakeString("result"), exprRead38},
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
			var condition23 tla.Value
			condition23, err = iface.Read(msg24, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition23.ApplyFunction(tla.MakeString("op")), iface.GetConstant("PUT_MSG")()).AsBool() {
				var exprRead39 tla.Value
				exprRead39, err = iface.Read(msg24, nil)
				if err != nil {
					return err
				}
				err = iface.Write(key1, nil, exprRead39.ApplyFunction(tla.MakeString("key")))
				if err != nil {
					return err
				}
				var exprRead40 tla.Value
				exprRead40, err = iface.Read(msg24, nil)
				if err != nil {
					return err
				}
				err = iface.Write(val1, nil, exprRead40.ApplyFunction(tla.MakeString("value")))
				if err != nil {
					return err
				}
				var exprRead41 tla.Value
				exprRead41, err = iface.Read(val1, nil)
				if err != nil {
					return err
				}
				var indexRead6 tla.Value
				indexRead6, err = iface.Read(key1, nil)
				if err != nil {
					return err
				}
				err = iface.Write(kv0, []tla.Value{indexRead6}, exprRead41)
				if err != nil {
					return err
				}
				var exprRead42 tla.Value
				exprRead42, err = iface.Read(ok, nil)
				if err != nil {
					return err
				}
				var indexRead7 tla.Value
				indexRead7, err = iface.Read(msg24, nil)
				if err != nil {
					return err
				}
				err = iface.Write(clients0, []tla.Value{indexRead7.ApplyFunction(tla.MakeString("reply_to"))}, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("type"), iface.GetConstant("PUT_RESPONSE")()},
					{tla.MakeString("result"), exprRead42},
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
			var condition24 tla.Value
			condition24, err = iface.Read(continue3, nil)
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
			var condition25 tla.Value
			condition25, err = iface.Read(clientId, nil)
			if err != nil {
				return err
			}
			var condition26 tla.Value
			condition26, err = iface.Read(clock, []tla.Value{condition25})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition26, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool() {
				err = iface.Write(continue4, nil, tla.ModuleFALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			} else {
				var exprRead43 tla.Value
				exprRead43, err = iface.Read(clientId, nil)
				if err != nil {
					return err
				}
				var exprRead44 tla.Value
				exprRead44, err = iface.Read(clock, []tla.Value{exprRead43})
				if err != nil {
					return err
				}
				var indexRead8 tla.Value
				indexRead8, err = iface.Read(clientId, nil)
				if err != nil {
					return err
				}
				err = iface.Write(clock, []tla.Value{indexRead8}, tla.ModulePlusSymbol(exprRead44, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				var exprRead45 tla.Value
				exprRead45, err = iface.Read(key3, nil)
				if err != nil {
					return err
				}
				var exprRead46 tla.Value
				exprRead46, err = iface.Read(clientId, nil)
				if err != nil {
					return err
				}
				var exprRead47 tla.Value
				exprRead47, err = iface.Read(clientId, nil)
				if err != nil {
					return err
				}
				var exprRead48 tla.Value
				exprRead48, err = iface.Read(clock, []tla.Value{exprRead47})
				if err != nil {
					return err
				}
				err = iface.Write(getReq, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("op"), iface.GetConstant("GET_MSG")()},
					{tla.MakeString("key"), exprRead45},
					{tla.MakeString("client"), exprRead46},
					{tla.MakeString("timestamp"), exprRead48},
					{tla.MakeString("reply_to"), iface.Self()},
				}))
				if err != nil {
					return err
				}
				var dstRead = ReplicaSet(iface)
				if dstRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var dst tla.Value = dstRead.SelectElement(iface.NextFairnessCounter("Get.getRequest.0", uint(dstRead.AsSet().Len())))
				_ = dst
				var exprRead49 tla.Value
				exprRead49, err = iface.Read(getReq, nil)
				if err != nil {
					return err
				}
				err = iface.Write(replicas0, []tla.Value{dst}, exprRead49)
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
			var condition27 tla.Value
			condition27, err = iface.Read(clientId4, nil)
			if err != nil {
				return err
			}
			var condition28 tla.Value
			condition28, err = iface.Read(clock3, []tla.Value{condition27})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition28, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool() {
				err = iface.Write(continue5, nil, tla.ModuleFALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Get.getCheckSpin")
			} else {
				var exprRead50 tla.Value
				exprRead50, err = iface.Read(clients1, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(getResp, nil, exprRead50)
				if err != nil {
					return err
				}
				var condition29 tla.Value
				condition29, err = iface.Read(getResp, nil)
				if err != nil {
					return err
				}
				if !tla.ModuleEqualsSymbol(condition29.ApplyFunction(tla.MakeString("type")), iface.GetConstant("GET_RESPONSE")()).AsBool() {
					return fmt.Errorf("%w: ((getResp).type) = (GET_RESPONSE)", distsys.ErrAssertionFailed)
				}
				var exprRead51 tla.Value
				exprRead51, err = iface.Read(getResp, nil)
				if err != nil {
					return err
				}
				err = iface.Write(outside, nil, exprRead51.ApplyFunction(tla.MakeString("result")))
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
			var condition30 tla.Value
			condition30, err = iface.Read(spin, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLogicalNotSymbol(condition30).AsBool() {
				err = iface.Write(continue6, nil, tla.ModuleFALSE)
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
			var condition31 tla.Value
			condition31, err = iface.Read(continue7, nil)
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
			var condition32 tla.Value
			condition32, err = iface.Read(clientId5, nil)
			if err != nil {
				return err
			}
			var condition33 tla.Value
			condition33, err = iface.Read(clock4, []tla.Value{condition32})
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition33, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool() {
				err = iface.Write(continue8, nil, tla.ModuleFALSE)
				if err != nil {
					return err
				}
				return iface.Goto("Put.putCheckSpin")
			} else {
				var exprRead52 tla.Value
				exprRead52, err = iface.Read(clientId5, nil)
				if err != nil {
					return err
				}
				var exprRead53 tla.Value
				exprRead53, err = iface.Read(clock4, []tla.Value{exprRead52})
				if err != nil {
					return err
				}
				var indexRead9 tla.Value
				indexRead9, err = iface.Read(clientId5, nil)
				if err != nil {
					return err
				}
				err = iface.Write(clock4, []tla.Value{indexRead9}, tla.ModulePlusSymbol(exprRead53, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				var exprRead54 tla.Value
				exprRead54, err = iface.Read(key4, nil)
				if err != nil {
					return err
				}
				var exprRead55 tla.Value
				exprRead55, err = iface.Read(value, nil)
				if err != nil {
					return err
				}
				var exprRead56 tla.Value
				exprRead56, err = iface.Read(clientId5, nil)
				if err != nil {
					return err
				}
				var exprRead57 tla.Value
				exprRead57, err = iface.Read(clientId5, nil)
				if err != nil {
					return err
				}
				var exprRead58 tla.Value
				exprRead58, err = iface.Read(clock4, []tla.Value{exprRead57})
				if err != nil {
					return err
				}
				err = iface.Write(putReq, nil, tla.MakeRecord([]tla.RecordField{
					{tla.MakeString("op"), iface.GetConstant("PUT_MSG")()},
					{tla.MakeString("key"), exprRead54},
					{tla.MakeString("value"), exprRead55},
					{tla.MakeString("client"), exprRead56},
					{tla.MakeString("timestamp"), exprRead58},
					{tla.MakeString("reply_to"), iface.Self()},
				}))
				if err != nil {
					return err
				}
				err = iface.Write(i8, nil, tla.MakeNumber(0))
				if err != nil {
					return err
				}
				err = iface.Write(j, nil, tla.MakeNumber(0))
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
			var condition34 tla.Value
			condition34, err = iface.Read(j0, nil)
			if err != nil {
				return err
			}
			var condition35 tla.Value
			condition35, err = iface.Read(clientId10, nil)
			if err != nil {
				return err
			}
			var condition36 tla.Value
			condition36, err = iface.Read(clock8, []tla.Value{condition35})
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleLessThanOrEqualSymbol(condition34, tla.ModuleMinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeNumber(1))).AsBool() && tla.ModuleNotEqualsSymbol(condition36, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool()).AsBool() {
				var exprRead59 tla.Value
				exprRead59, err = iface.Read(putReq0, nil)
				if err != nil {
					return err
				}
				var indexRead10 tla.Value
				indexRead10, err = iface.Read(j0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(replicas1, []tla.Value{indexRead10}, exprRead59)
				if err != nil {
					return err
				}
				var exprRead60 tla.Value
				exprRead60, err = iface.Read(j0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(j0, nil, tla.ModulePlusSymbol(exprRead60, tla.MakeNumber(1)))
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
			var condition37 tla.Value
			condition37, err = iface.Read(i9, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLessThanSymbol(condition37, tla.ModuleCardinality(ReplicaSet(iface))).AsBool() {
				var condition38 tla.Value
				condition38, err = iface.Read(clientId11, nil)
				if err != nil {
					return err
				}
				var condition39 tla.Value
				condition39, err = iface.Read(clock9, []tla.Value{condition38})
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition39, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool() {
					err = iface.Write(continue9, nil, tla.ModuleFALSE)
					if err != nil {
						return err
					}
					return iface.Goto("Put.putLoop")
				} else {
					var exprRead61 tla.Value
					exprRead61, err = iface.Read(clients2, []tla.Value{iface.Self()})
					if err != nil {
						return err
					}
					err = iface.Write(putResp, nil, exprRead61)
					if err != nil {
						return err
					}
					var condition40 tla.Value
					condition40, err = iface.Read(putResp, nil)
					if err != nil {
						return err
					}
					if !tla.ModuleEqualsSymbol(condition40.ApplyFunction(tla.MakeString("type")), iface.GetConstant("PUT_RESPONSE")()).AsBool() {
						return fmt.Errorf("%w: ((putResp).type) = (PUT_RESPONSE)", distsys.ErrAssertionFailed)
					}
					var exprRead62 tla.Value
					exprRead62, err = iface.Read(i9, nil)
					if err != nil {
						return err
					}
					err = iface.Write(i9, nil, tla.ModulePlusSymbol(exprRead62, tla.MakeNumber(1)))
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
			err = iface.Write(outside0, nil, iface.GetConstant("PUT_RESPONSE")())
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
			var condition41 tla.Value
			condition41, err = iface.Read(spin0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLogicalNotSymbol(condition41).AsBool() {
				err = iface.Write(continue10, nil, tla.ModuleFALSE)
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
			var exprRead63 tla.Value
			exprRead63, err = iface.Read(clientId12, nil)
			if err != nil {
				return err
			}
			err = iface.Write(msg28, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("op"), iface.GetConstant("DISCONNECT_MSG")()},
				{tla.MakeString("client"), exprRead63},
			}))
			if err != nil {
				return err
			}
			var indexRead11 tla.Value
			indexRead11, err = iface.Read(clientId12, nil)
			if err != nil {
				return err
			}
			err = iface.Write(clock10, []tla.Value{indexRead11}, tla.ModuleNegationSymbol(tla.MakeNumber(1)))
			if err != nil {
				return err
			}
			err = iface.Write(j4, nil, tla.MakeNumber(0))
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
			var condition42 tla.Value
			condition42, err = iface.Read(j5, nil)
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleLessThanOrEqualSymbol(condition42, tla.ModuleMinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeNumber(1))).AsBool() && tla.ModuleNotEqualsSymbol(tla.MakeNumber(0), tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool()).AsBool() {
				var exprRead64 tla.Value
				exprRead64, err = iface.Read(msg29, nil)
				if err != nil {
					return err
				}
				var indexRead12 tla.Value
				indexRead12, err = iface.Read(j5, nil)
				if err != nil {
					return err
				}
				err = iface.Write(replicas2, []tla.Value{indexRead12}, exprRead64)
				if err != nil {
					return err
				}
				var exprRead65 tla.Value
				exprRead65, err = iface.Read(j5, nil)
				if err != nil {
					return err
				}
				err = iface.Write(j5, nil, tla.ModulePlusSymbol(exprRead65, tla.MakeNumber(1)))
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
			var condition43 tla.Value
			condition43, err = iface.Read(continue11, nil)
			if err != nil {
				return err
			}
			if condition43.AsBool() {
				var condition44 tla.Value
				condition44, err = iface.Read(clientId14, nil)
				if err != nil {
					return err
				}
				var condition45 tla.Value
				condition45, err = iface.Read(clock11, []tla.Value{condition44})
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition45, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool() {
					err = iface.Write(continue11, nil, tla.ModuleFALSE)
					if err != nil {
						return err
					}
					return iface.Goto("ClockUpdate.nullCheckSpin")
				} else {
					var exprRead66 tla.Value
					exprRead66, err = iface.Read(clientId14, nil)
					if err != nil {
						return err
					}
					var exprRead67 tla.Value
					exprRead67, err = iface.Read(clock11, []tla.Value{exprRead66})
					if err != nil {
						return err
					}
					var indexRead13 tla.Value
					indexRead13, err = iface.Read(clientId14, nil)
					if err != nil {
						return err
					}
					err = iface.Write(clock11, []tla.Value{indexRead13}, tla.ModulePlusSymbol(exprRead67, tla.MakeNumber(1)))
					if err != nil {
						return err
					}
					var exprRead68 tla.Value
					exprRead68, err = iface.Read(clientId14, nil)
					if err != nil {
						return err
					}
					var exprRead69 tla.Value
					exprRead69, err = iface.Read(clientId14, nil)
					if err != nil {
						return err
					}
					var exprRead70 tla.Value
					exprRead70, err = iface.Read(clock11, []tla.Value{exprRead69})
					if err != nil {
						return err
					}
					err = iface.Write(msg30, nil, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("op"), iface.GetConstant("NULL_MSG")()},
						{tla.MakeString("client"), exprRead68},
						{tla.MakeString("timestamp"), exprRead70},
					}))
					if err != nil {
						return err
					}
					err = iface.Write(j9, nil, tla.MakeNumber(0))
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
			var condition46 tla.Value
			condition46, err = iface.Read(j10, nil)
			if err != nil {
				return err
			}
			var condition47 tla.Value
			condition47, err = iface.Read(clientId19, nil)
			if err != nil {
				return err
			}
			var condition48 tla.Value
			condition48, err = iface.Read(clock15, []tla.Value{condition47})
			if err != nil {
				return err
			}
			if tla.MakeBool(tla.ModuleLessThanOrEqualSymbol(condition46, tla.ModuleMinusSymbol(iface.GetConstant("NUM_REPLICAS")(), tla.MakeNumber(1))).AsBool() && tla.ModuleNotEqualsSymbol(condition48, tla.ModuleNegationSymbol(tla.MakeNumber(1))).AsBool()).AsBool() {
				var exprRead71 tla.Value
				exprRead71, err = iface.Read(msg31, nil)
				if err != nil {
					return err
				}
				var indexRead14 tla.Value
				indexRead14, err = iface.Read(j10, nil)
				if err != nil {
					return err
				}
				err = iface.Write(replicas3, []tla.Value{indexRead14}, exprRead71)
				if err != nil {
					return err
				}
				var exprRead72 tla.Value
				exprRead72, err = iface.Read(j10, nil)
				if err != nil {
					return err
				}
				err = iface.Write(j10, nil, tla.ModulePlusSymbol(exprRead72, tla.MakeNumber(1)))
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
			var condition49 tla.Value
			condition49, err = iface.Read(spin1, nil)
			if err != nil {
				return err
			}
			if tla.ModuleLogicalNotSymbol(condition49).AsBool() {
				err = iface.Write(continue13, nil, tla.ModuleFALSE)
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
		iface.EnsureArchetypeResourceLocal("AReplica.pendingRequests", tla.MakeFunction([]tla.Value{iface.ReadArchetypeResourceLocal("AReplica.liveClients")}, func(args []tla.Value) tla.Value {
			var c0 tla.Value = args[0]
			_ = c0
			return tla.MakeTuple()
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.stableMessages", tla.MakeTuple())
		iface.EnsureArchetypeResourceLocal("AReplica.i", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.firstPending", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.timestamp", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.nextClient", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.lowestPending", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.chooseMessage", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.currentClocks", tla.MakeFunction([]tla.Value{iface.ReadArchetypeResourceLocal("AReplica.liveClients")}, func(args0 []tla.Value) tla.Value {
			var c1 tla.Value = args0[0]
			_ = c1
			return tla.MakeNumber(0)
		}))
		iface.EnsureArchetypeResourceLocal("AReplica.minClock", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.continue", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.pendingClients", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.clientsIter", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.ok", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.key", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AReplica.val", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("Get.continue", tla.ModuleTRUE)
		iface.EnsureArchetypeResourceLocal("Get.getReq", tla.Value{})
		iface.EnsureArchetypeResourceLocal("Get.getResp", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("Put.continue", tla.ModuleTRUE)
		iface.EnsureArchetypeResourceLocal("Put.i", tla.Value{})
		iface.EnsureArchetypeResourceLocal("Put.j", tla.Value{})
		iface.EnsureArchetypeResourceLocal("Put.putReq", tla.Value{})
		iface.EnsureArchetypeResourceLocal("Put.putResp", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("Disconnect.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("Disconnect.j", tla.Value{})
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
		iface.EnsureArchetypeResourceLocal("ClockUpdate.continue", tla.ModuleTRUE)
		iface.EnsureArchetypeResourceLocal("ClockUpdate.j", tla.Value{})
		iface.EnsureArchetypeResourceLocal("ClockUpdate.msg", tla.Value{})
	},
}
