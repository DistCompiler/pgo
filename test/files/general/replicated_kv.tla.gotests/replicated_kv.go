package replicatedkv

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	BUFFER_SIZE    distsys.TLAValue
	NUM_REPLICAS   distsys.TLAValue
	NUM_CLIENTS    distsys.TLAValue
	DISCONNECT_MSG distsys.TLAValue
	GET_MSG        distsys.TLAValue
	PUT_MSG        distsys.TLAValue
	NULL_MSG       distsys.TLAValue
	GET_RESPONSE   distsys.TLAValue
	PUT_RESPONSE   distsys.TLAValue
	NULL           distsys.TLAValue
	GET_KEY        distsys.TLAValue
	PUT_KEY        distsys.TLAValue
	PUT_VALUE      distsys.TLAValue
}

func KeySpace(constants Constants) distsys.TLAValue {
	return distsys.NewTLASet(constants.GET_KEY, constants.PUT_KEY)
}

func GET_ORDER(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(0)
}

func PUT_ORDER(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}

func DISCONNECT_ORDER(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}

func NULL_ORDER(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}

func GetSet(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(constants.NUM_REPLICAS, distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, distsys.TLA_MinusSymbol(constants.NUM_CLIENTS, distsys.NewTLANumber(1))))
}

func PutSet(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, constants.NUM_CLIENTS), distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, distsys.TLA_MinusSymbol(distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(2), constants.NUM_CLIENTS), distsys.NewTLANumber(1))))
}

func DisconnectSet(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(2), constants.NUM_CLIENTS)), distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, distsys.TLA_MinusSymbol(distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(3), constants.NUM_CLIENTS), distsys.NewTLANumber(1))))
}

func NullSet(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(3), constants.NUM_CLIENTS)), distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, distsys.TLA_MinusSymbol(distsys.TLA_AsteriskSymbol(distsys.NewTLANumber(4), constants.NUM_CLIENTS), distsys.NewTLANumber(1))))
}

func NUM_NODES(constants Constants) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(constants.NUM_REPLICAS, constants.NUM_CLIENTS)
}

func ReplicaSet(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.NewTLANumber(0), distsys.TLA_MinusSymbol(constants.NUM_REPLICAS, distsys.NewTLANumber(1)))
}

func ClientSet(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(constants.NUM_REPLICAS, distsys.TLA_MinusSymbol(func() distsys.TLAValue {
		return NUM_NODES(constants)
	}(), distsys.NewTLANumber(1)))
}

func AReplica(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, clients distsys.ArchetypeResourceHandle, replicas distsys.ArchetypeResourceHandle, kv distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		InitLabelTag = iota
		replicaLoopLabelTag
		receiveClientRequestLabelTag
		clientDisconnectedLabelTag
		replicaGetRequestLabelTag
		replicaPutRequestLabelTag
		replicaNullRequestLabelTag
		findStableRequestsLoopLabelTag
		findMinClockLabelTag
		findMinClientLabelTag
		addStableMessageLabelTag
		respondPendingRequestsLoopLabelTag
		respondStableGetLabelTag
		respondStablePutLabelTag
		DoneLabelTag
	)
	programCounter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag)))
	liveClients := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = liveClients
	pendingRequests := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = pendingRequests
	stableMessages := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = stableMessages
	i := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = i
	firstPending := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = firstPending
	timestamp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = timestamp
	nextClient := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = nextClient
	lowestPending := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = lowestPending
	chooseMessage := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = chooseMessage
	currentClocks := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = currentClocks
	minClock := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = minClock
	continue0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = continue0
	pendingClients := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = pendingClients
	clientsIter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = clientsIter
	msg := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg
	ok := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = ok
	key := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = key
	val := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = val

	for {
		select {
		case <-ctx.Done():
			err = distsys.ErrContextClosed
		default:
		}
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
			err = ctx.Write(liveClients, nil, func() distsys.TLAValue {
				return ClientSet(constants)
			}())
			if err != nil {
				continue
			}
			var resourceRead distsys.TLAValue
			resourceRead, err = ctx.Read(liveClients, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(pendingRequests, nil, distsys.NewTLAFunction([]distsys.TLAValue{resourceRead}, func(args []distsys.TLAValue) distsys.TLAValue {
				var c distsys.TLAValue = args[0]
				_ = c
				return distsys.NewTLATuple()
			}))
			if err != nil {
				continue
			}
			err = ctx.Write(stableMessages, nil, distsys.NewTLATuple())
			if err != nil {
				continue
			}
			var resourceRead0 distsys.TLAValue
			resourceRead0, err = ctx.Read(liveClients, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(currentClocks, nil, distsys.NewTLAFunction([]distsys.TLAValue{resourceRead0}, func(args0 []distsys.TLAValue) distsys.TLAValue {
				var c0 distsys.TLAValue = args0[0]
				_ = c0
				return distsys.NewTLANumber(0)
			}))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaLoopLabelTag))
			if err != nil {
				continue
			}
		case replicaLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(stableMessages, []distsys.TLAValue{}, distsys.NewTLATuple())
				if err != nil {
					continue
				}
				err = ctx.Write(continue0, []distsys.TLAValue{}, distsys.TLA_TRUE)
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(receiveClientRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case receiveClientRequestLabelTag:
			var exprRead distsys.TLAValue
			exprRead, err = ctx.Read(replicas, []distsys.TLAValue{self})
			if err != nil {
				continue
			}
			err = ctx.Write(msg, []distsys.TLAValue{}, exprRead)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(clientDisconnectedLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case clientDisconnectedLabelTag:
			var condition distsys.TLAValue
			condition, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("op")), constants.DISCONNECT_MSG).AsBool() {
				var exprRead0 distsys.TLAValue
				exprRead0, err = ctx.Read(liveClients, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead1 distsys.TLAValue
				exprRead1, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(liveClients, []distsys.TLAValue{}, distsys.TLA_BackslashSymbol(exprRead0, distsys.NewTLASet(exprRead1.ApplyFunction(distsys.NewTLAString("client")))))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaGetRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaGetRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case replicaGetRequestLabelTag:
			var condition0 distsys.TLAValue
			condition0, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition0.ApplyFunction(distsys.NewTLAString("op")), constants.GET_MSG).AsBool() {
				var condition1 distsys.TLAValue
				condition1, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition2 distsys.TLAValue
				condition2, err = ctx.Read(liveClients, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_InSymbol(condition1.ApplyFunction(distsys.NewTLAString("client")), condition2).AsBool() {
					err = fmt.Errorf("%w: ((msg).client) \\in (liveClients)", distsys.ErrAssertionFailed)
					continue
				}
				var exprRead2 distsys.TLAValue
				exprRead2, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead distsys.TLAValue
				indexRead, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(currentClocks, []distsys.TLAValue{indexRead.ApplyFunction(distsys.NewTLAString("client"))}, exprRead2.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					continue
				}
				var exprRead3 distsys.TLAValue
				exprRead3, err = ctx.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead4 distsys.TLAValue
				exprRead4, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead5 distsys.TLAValue
				exprRead5, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead0 distsys.TLAValue
				indexRead0, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(pendingRequests, []distsys.TLAValue{indexRead0.ApplyFunction(distsys.NewTLAString("client"))}, distsys.TLA_Append(exprRead3.ApplyFunction(exprRead4.ApplyFunction(distsys.NewTLAString("client"))), exprRead5))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaPutRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaPutRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case replicaPutRequestLabelTag:
			var condition3 distsys.TLAValue
			condition3, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition3.ApplyFunction(distsys.NewTLAString("op")), constants.PUT_MSG).AsBool() {
				var exprRead6 distsys.TLAValue
				exprRead6, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead1 distsys.TLAValue
				indexRead1, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(currentClocks, []distsys.TLAValue{indexRead1.ApplyFunction(distsys.NewTLAString("client"))}, exprRead6.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					continue
				}
				var exprRead7 distsys.TLAValue
				exprRead7, err = ctx.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead8 distsys.TLAValue
				exprRead8, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
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
				err = ctx.Write(pendingRequests, []distsys.TLAValue{indexRead2.ApplyFunction(distsys.NewTLAString("client"))}, distsys.TLA_Append(exprRead7.ApplyFunction(exprRead8.ApplyFunction(distsys.NewTLAString("client"))), exprRead9))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaNullRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaNullRequestLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case replicaNullRequestLabelTag:
			var condition4 distsys.TLAValue
			condition4, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition4.ApplyFunction(distsys.NewTLAString("op")), constants.NULL_MSG).AsBool() {
				var exprRead10 distsys.TLAValue
				exprRead10, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead3 distsys.TLAValue
				indexRead3, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(currentClocks, []distsys.TLAValue{indexRead3.ApplyFunction(distsys.NewTLAString("client"))}, exprRead10.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findStableRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findStableRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case findStableRequestsLoopLabelTag:
			var condition5 distsys.TLAValue
			condition5, err = ctx.Read(continue0, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if condition5.AsBool() {
				var exprRead11 distsys.TLAValue
				exprRead11, err = ctx.Read(liveClients, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead12 distsys.TLAValue
				exprRead12, err = ctx.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(pendingClients, []distsys.TLAValue{}, distsys.TLASetRefinement(exprRead11, func(elem distsys.TLAValue) bool {
					var c1 distsys.TLAValue = elem
					_ = c1
					return distsys.TLA_GreaterThanSymbol(distsys.TLA_Len(exprRead12.ApplyFunction(c1)), distsys.NewTLANumber(0)).AsBool()
				}))
				if err != nil {
					continue
				}
				err = ctx.Write(nextClient, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(func() distsys.TLAValue {
					return NUM_NODES(constants)
				}(), distsys.NewTLANumber(1)))
				if err != nil {
					continue
				}
				var exprRead13 distsys.TLAValue
				exprRead13, err = ctx.Read(liveClients, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(clientsIter, []distsys.TLAValue{}, exprRead13)
				if err != nil {
					continue
				}
				err = ctx.Write(i, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err != nil {
					continue
				}
				err = ctx.Write(minClock, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findMinClockLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(i, []distsys.TLAValue{}, distsys.NewTLANumber(1))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(respondPendingRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case findMinClockLabelTag:
			var condition6 distsys.TLAValue
			condition6, err = ctx.Read(i, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition7 distsys.TLAValue
			condition7, err = ctx.Read(clientsIter, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanSymbol(condition6, distsys.TLA_Cardinality(condition7)).AsBool() {
				var clientRead distsys.TLAValue
				clientRead, err = ctx.Read(clientsIter, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var client distsys.TLAValue = clientRead.SelectElement()
				var condition8 distsys.TLAValue
				condition8, err = ctx.Read(minClock, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition9 distsys.TLAValue
				condition9, err = ctx.Read(currentClocks, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition10 distsys.TLAValue
				condition10, err = ctx.Read(minClock, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if distsys.TLA_LogicalOrSymbol(distsys.TLA_EqualsSymbol(condition8, distsys.NewTLANumber(0)), distsys.TLA_LessThanSymbol(condition9.ApplyFunction(client), condition10)).AsBool() {
					var exprRead14 distsys.TLAValue
					exprRead14, err = ctx.Read(currentClocks, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					err = ctx.Write(minClock, []distsys.TLAValue{}, exprRead14.ApplyFunction(client))
					if err != nil {
						continue
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead15 distsys.TLAValue
				exprRead15, err = ctx.Read(clientsIter, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(clientsIter, []distsys.TLAValue{}, distsys.TLA_BackslashSymbol(exprRead15, distsys.NewTLASet(client)))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findMinClockLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
				// no statements
			} else {
				var exprRead16 distsys.TLAValue
				exprRead16, err = ctx.Read(minClock, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(lowestPending, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead16, distsys.NewTLANumber(1)))
				if err != nil {
					continue
				}
				err = ctx.Write(i, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findMinClientLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case findMinClientLabelTag:
			var condition11 distsys.TLAValue
			condition11, err = ctx.Read(i, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition12 distsys.TLAValue
			condition12, err = ctx.Read(pendingClients, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanSymbol(condition11, distsys.TLA_Cardinality(condition12)).AsBool() {
				var clientRead0 distsys.TLAValue
				clientRead0, err = ctx.Read(pendingClients, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var client0 distsys.TLAValue = clientRead0.SelectElement()
				var exprRead17 distsys.TLAValue
				exprRead17, err = ctx.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(firstPending, []distsys.TLAValue{}, distsys.TLA_Head(exprRead17.ApplyFunction(client0)))
				if err != nil {
					continue
				}
				var condition13 distsys.TLAValue
				condition13, err = ctx.Read(firstPending, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition14 distsys.TLAValue
				condition14, err = ctx.Read(firstPending, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_LogicalOrSymbol(distsys.TLA_EqualsSymbol(condition13.ApplyFunction(distsys.NewTLAString("op")), constants.GET_MSG), distsys.TLA_EqualsSymbol(condition14.ApplyFunction(distsys.NewTLAString("op")), constants.PUT_MSG)).AsBool() {
					err = fmt.Errorf("%w: (((firstPending).op) = (GET_MSG)) \\/ (((firstPending).op) = (PUT_MSG))", distsys.ErrAssertionFailed)
					continue
				}
				var exprRead18 distsys.TLAValue
				exprRead18, err = ctx.Read(firstPending, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(timestamp, []distsys.TLAValue{}, exprRead18.ApplyFunction(distsys.NewTLAString("timestamp")))
				if err != nil {
					continue
				}
				var condition15 distsys.TLAValue
				condition15, err = ctx.Read(timestamp, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition16 distsys.TLAValue
				condition16, err = ctx.Read(minClock, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if distsys.TLA_LessThanSymbol(condition15, condition16).AsBool() {
					var exprRead19 distsys.TLAValue
					exprRead19, err = ctx.Read(timestamp, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					var exprRead20 distsys.TLAValue
					exprRead20, err = ctx.Read(lowestPending, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					var exprRead21 distsys.TLAValue
					exprRead21, err = ctx.Read(timestamp, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					var exprRead22 distsys.TLAValue
					exprRead22, err = ctx.Read(lowestPending, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					var exprRead23 distsys.TLAValue
					exprRead23, err = ctx.Read(nextClient, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					err = ctx.Write(chooseMessage, []distsys.TLAValue{}, distsys.TLA_LogicalOrSymbol(distsys.TLA_LessThanSymbol(exprRead19, exprRead20), distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(exprRead21, exprRead22), distsys.TLA_LessThanSymbol(client0, exprRead23))))
					if err != nil {
						continue
					}
					var condition17 distsys.TLAValue
					condition17, err = ctx.Read(chooseMessage, []distsys.TLAValue{})
					if err != nil {
						continue
					}
					if condition17.AsBool() {
						err = ctx.Write(nextClient, []distsys.TLAValue{}, client0)
						if err != nil {
							continue
						}
						var exprRead24 distsys.TLAValue
						exprRead24, err = ctx.Read(timestamp, []distsys.TLAValue{})
						if err != nil {
							continue
						}
						err = ctx.Write(lowestPending, []distsys.TLAValue{}, exprRead24)
						if err != nil {
							continue
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
				exprRead25, err = ctx.Read(pendingClients, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(pendingClients, []distsys.TLAValue{}, distsys.TLA_BackslashSymbol(exprRead25, distsys.NewTLASet(client0)))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findMinClientLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
				// no statements
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(addStableMessageLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case addStableMessageLabelTag:
			var condition18 distsys.TLAValue
			condition18, err = ctx.Read(lowestPending, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition19 distsys.TLAValue
			condition19, err = ctx.Read(minClock, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanSymbol(condition18, condition19).AsBool() {
				var exprRead26 distsys.TLAValue
				exprRead26, err = ctx.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead27 distsys.TLAValue
				exprRead27, err = ctx.Read(nextClient, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(msg, []distsys.TLAValue{}, distsys.TLA_Head(exprRead26.ApplyFunction(exprRead27)))
				if err != nil {
					continue
				}
				var exprRead28 distsys.TLAValue
				exprRead28, err = ctx.Read(pendingRequests, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead29 distsys.TLAValue
				exprRead29, err = ctx.Read(nextClient, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead4 distsys.TLAValue
				indexRead4, err = ctx.Read(nextClient, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(pendingRequests, []distsys.TLAValue{indexRead4}, distsys.TLA_Tail(exprRead28.ApplyFunction(exprRead29)))
				if err != nil {
					continue
				}
				var exprRead30 distsys.TLAValue
				exprRead30, err = ctx.Read(stableMessages, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead31 distsys.TLAValue
				exprRead31, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(stableMessages, []distsys.TLAValue{}, distsys.TLA_Append(exprRead30, exprRead31))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findStableRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(continue0, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(findStableRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case respondPendingRequestsLoopLabelTag:
			var condition20 distsys.TLAValue
			condition20, err = ctx.Read(i, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition21 distsys.TLAValue
			condition21, err = ctx.Read(stableMessages, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition20, distsys.TLA_Len(condition21)).AsBool() {
				var exprRead32 distsys.TLAValue
				exprRead32, err = ctx.Read(stableMessages, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead33 distsys.TLAValue
				exprRead33, err = ctx.Read(i, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(msg, []distsys.TLAValue{}, exprRead32.ApplyFunction(exprRead33))
				if err != nil {
					continue
				}
				var exprRead34 distsys.TLAValue
				exprRead34, err = ctx.Read(i, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(i, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead34, distsys.NewTLANumber(1)))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(respondStableGetLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(replicaLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case respondStableGetLabelTag:
			var condition22 distsys.TLAValue
			condition22, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition22.ApplyFunction(distsys.NewTLAString("op")), constants.GET_MSG).AsBool() {
				var exprRead35 distsys.TLAValue
				exprRead35, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(key, []distsys.TLAValue{}, exprRead35.ApplyFunction(distsys.NewTLAString("key")))
				if err != nil {
					continue
				}
				var exprRead36 distsys.TLAValue
				exprRead36, err = ctx.Read(key, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead37 distsys.TLAValue
				exprRead37, err = ctx.Read(kv, []distsys.TLAValue{exprRead36})
				if err != nil {
					continue
				}
				err = ctx.Write(val, []distsys.TLAValue{}, exprRead37)
				if err != nil {
					continue
				}
				var exprRead38 distsys.TLAValue
				exprRead38, err = ctx.Read(val, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead5 distsys.TLAValue
				indexRead5, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(clients, []distsys.TLAValue{indexRead5.ApplyFunction(distsys.NewTLAString("reply_to"))}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("type"), constants.GET_RESPONSE},
					{distsys.NewTLAString("result"), exprRead38},
				}))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(respondStablePutLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(respondStablePutLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case respondStablePutLabelTag:
			var condition23 distsys.TLAValue
			condition23, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition23.ApplyFunction(distsys.NewTLAString("op")), constants.PUT_MSG).AsBool() {
				var exprRead39 distsys.TLAValue
				exprRead39, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(key, []distsys.TLAValue{}, exprRead39.ApplyFunction(distsys.NewTLAString("key")))
				if err != nil {
					continue
				}
				var exprRead40 distsys.TLAValue
				exprRead40, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(val, []distsys.TLAValue{}, exprRead40.ApplyFunction(distsys.NewTLAString("value")))
				if err != nil {
					continue
				}
				var exprRead41 distsys.TLAValue
				exprRead41, err = ctx.Read(val, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead6 distsys.TLAValue
				indexRead6, err = ctx.Read(key, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(kv, []distsys.TLAValue{indexRead6}, exprRead41)
				if err != nil {
					continue
				}
				var exprRead42 distsys.TLAValue
				exprRead42, err = ctx.Read(ok, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead7 distsys.TLAValue
				indexRead7, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(clients, []distsys.TLAValue{indexRead7.ApplyFunction(distsys.NewTLAString("reply_to"))}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("type"), constants.PUT_RESPONSE},
					{distsys.NewTLAString("result"), exprRead42},
				}))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(respondPendingRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(respondPendingRequestsLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case DoneLabelTag:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag)
		}
	}
}

func Get(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, clientId distsys.ArchetypeResourceHandle, replicas0 distsys.ArchetypeResourceHandle, clients0 distsys.ArchetypeResourceHandle, key0 distsys.TLAValue, clock distsys.ArchetypeResourceHandle, spin distsys.TLAValue, outside distsys.ArchetypeResourceHandle) error {
	var err0 error
	// label tags
	const (
		InitLabelTag0 = iota
		getLoopLabelTag
		getRequestLabelTag
		getReplyLabelTag
		getCheckSpinLabelTag
		DoneLabelTag0
	)
	programCounter0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag0)))
	key1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(key0))
	spin0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(spin))
	continue1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = continue1
	getReq := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = getReq
	getResp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = getResp

	for {
		select {
		case <-ctx.Done():
			err0 = distsys.ErrContextClosed
		default:
		}
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
			err0 = ctx.Write(continue1, nil, distsys.TLA_TRUE)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getLoopLabelTag))
			if err0 != nil {
				continue
			}
		case getLoopLabelTag:
			var condition24 distsys.TLAValue
			condition24, err0 = ctx.Read(continue1, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			if condition24.AsBool() {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getRequestLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag0))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case getRequestLabelTag:
			var condition25 distsys.TLAValue
			condition25, err0 = ctx.Read(clientId, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition26 distsys.TLAValue
			condition26, err0 = ctx.Read(clock, []distsys.TLAValue{condition25})
			if err0 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition26, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
				err0 = ctx.Write(continue1, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getCheckSpinLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				var exprRead43 distsys.TLAValue
				exprRead43, err0 = ctx.Read(clientId, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var exprRead44 distsys.TLAValue
				exprRead44, err0 = ctx.Read(clock, []distsys.TLAValue{exprRead43})
				if err0 != nil {
					continue
				}
				var indexRead8 distsys.TLAValue
				indexRead8, err0 = ctx.Read(clientId, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(clock, []distsys.TLAValue{indexRead8}, distsys.TLA_PlusSymbol(exprRead44, distsys.NewTLANumber(1)))
				if err0 != nil {
					continue
				}
				var exprRead45 distsys.TLAValue
				exprRead45, err0 = ctx.Read(key1, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var exprRead46 distsys.TLAValue
				exprRead46, err0 = ctx.Read(clientId, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var exprRead47 distsys.TLAValue
				exprRead47, err0 = ctx.Read(clientId, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				var exprRead48 distsys.TLAValue
				exprRead48, err0 = ctx.Read(clock, []distsys.TLAValue{exprRead47})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(getReq, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("op"), constants.GET_MSG},
					{distsys.NewTLAString("key"), exprRead45},
					{distsys.NewTLAString("client"), exprRead46},
					{distsys.NewTLAString("timestamp"), exprRead48},
					{distsys.NewTLAString("reply_to"), self},
				}))
				if err0 != nil {
					continue
				}
				var dst distsys.TLAValue = func() distsys.TLAValue {
					return ReplicaSet(constants)
				}().SelectElement()
				var exprRead49 distsys.TLAValue
				exprRead49, err0 = ctx.Read(getReq, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(replicas0, []distsys.TLAValue{dst}, exprRead49)
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getReplyLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
				// no statements
			}
			// no statements
		case getReplyLabelTag:
			var condition27 distsys.TLAValue
			condition27, err0 = ctx.Read(clientId, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition28 distsys.TLAValue
			condition28, err0 = ctx.Read(clock, []distsys.TLAValue{condition27})
			if err0 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition28, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
				err0 = ctx.Write(continue1, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getCheckSpinLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				var exprRead50 distsys.TLAValue
				exprRead50, err0 = ctx.Read(clients0, []distsys.TLAValue{self})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(getResp, []distsys.TLAValue{}, exprRead50)
				if err0 != nil {
					continue
				}
				var condition29 distsys.TLAValue
				condition29, err0 = ctx.Read(getResp, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				if !distsys.TLA_EqualsSymbol(condition29.ApplyFunction(distsys.NewTLAString("type")), constants.GET_RESPONSE).AsBool() {
					err0 = fmt.Errorf("%w: ((getResp).type) = (GET_RESPONSE)", distsys.ErrAssertionFailed)
					continue
				}
				var exprRead51 distsys.TLAValue
				exprRead51, err0 = ctx.Read(getResp, []distsys.TLAValue{})
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(outside, []distsys.TLAValue{}, exprRead51.ApplyFunction(distsys.NewTLAString("result")))
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getCheckSpinLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case getCheckSpinLabelTag:
			var condition30 distsys.TLAValue
			condition30, err0 = ctx.Read(spin0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			if distsys.TLA_LogicalNotSymbol(condition30).AsBool() {
				err0 = ctx.Write(continue1, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err0 != nil {
					continue
				}
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getLoopLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(getLoopLabelTag))
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

func Put(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, clientId0 distsys.ArchetypeResourceHandle, replicas1 distsys.ArchetypeResourceHandle, clients1 distsys.ArchetypeResourceHandle, key2 distsys.TLAValue, value distsys.TLAValue, clock0 distsys.ArchetypeResourceHandle, spin1 distsys.TLAValue, outside0 distsys.ArchetypeResourceHandle) error {
	var err1 error
	// label tags
	const (
		InitLabelTag1 = iota
		putLoopLabelTag
		putRequestLabelTag
		putBroadcastLabelTag
		putResponseLabelTag
		putCompleteLabelTag
		putCheckSpinLabelTag
		DoneLabelTag1
	)
	programCounter1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag1)))
	key3 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(key2))
	value0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(value))
	spin2 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(spin1))
	continue2 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = continue2
	i0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = i0
	j := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = j
	putReq := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = putReq
	putResp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = putResp

	for {
		select {
		case <-ctx.Done():
			err1 = distsys.ErrContextClosed
		default:
		}
		if err1 != nil {
			if err1 == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err1 = nil
			} else {
				return err1
			}
		}
		var labelTag1 distsys.TLAValue
		labelTag1, err1 = ctx.Read(programCounter1, []distsys.TLAValue{})
		if err1 != nil {
			return err1
		}
		switch labelTag1.AsNumber() {
		case InitLabelTag1:
			err1 = ctx.Write(continue2, nil, distsys.TLA_TRUE)
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putLoopLabelTag))
			if err1 != nil {
				continue
			}
		case putLoopLabelTag:
			var condition31 distsys.TLAValue
			condition31, err1 = ctx.Read(continue2, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			if condition31.AsBool() {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putRequestLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			} else {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag1))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			}
			// no statements
		case putRequestLabelTag:
			var condition32 distsys.TLAValue
			condition32, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var condition33 distsys.TLAValue
			condition33, err1 = ctx.Read(clock0, []distsys.TLAValue{condition32})
			if err1 != nil {
				continue
			}
			if distsys.TLA_EqualsSymbol(condition33, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
				err1 = ctx.Write(continue2, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putCheckSpinLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			} else {
				var exprRead52 distsys.TLAValue
				exprRead52, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var exprRead53 distsys.TLAValue
				exprRead53, err1 = ctx.Read(clock0, []distsys.TLAValue{exprRead52})
				if err1 != nil {
					continue
				}
				var indexRead9 distsys.TLAValue
				indexRead9, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(clock0, []distsys.TLAValue{indexRead9}, distsys.TLA_PlusSymbol(exprRead53, distsys.NewTLANumber(1)))
				if err1 != nil {
					continue
				}
				var exprRead54 distsys.TLAValue
				exprRead54, err1 = ctx.Read(key3, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var exprRead55 distsys.TLAValue
				exprRead55, err1 = ctx.Read(value0, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var exprRead56 distsys.TLAValue
				exprRead56, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var exprRead57 distsys.TLAValue
				exprRead57, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var exprRead58 distsys.TLAValue
				exprRead58, err1 = ctx.Read(clock0, []distsys.TLAValue{exprRead57})
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(putReq, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("op"), constants.PUT_MSG},
					{distsys.NewTLAString("key"), exprRead54},
					{distsys.NewTLAString("value"), exprRead55},
					{distsys.NewTLAString("client"), exprRead56},
					{distsys.NewTLAString("timestamp"), exprRead58},
					{distsys.NewTLAString("reply_to"), self},
				}))
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(i0, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(j, []distsys.TLAValue{}, distsys.NewTLANumber(0))
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putBroadcastLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			}
			// no statements
		case putBroadcastLabelTag:
			var condition34 distsys.TLAValue
			condition34, err1 = ctx.Read(j, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var condition35 distsys.TLAValue
			condition35, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var condition36 distsys.TLAValue
			condition36, err1 = ctx.Read(clock0, []distsys.TLAValue{condition35})
			if err1 != nil {
				continue
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_LessThanOrEqualSymbol(condition34, distsys.TLA_MinusSymbol(constants.NUM_REPLICAS, distsys.NewTLANumber(1))), distsys.TLA_NotEqualsSymbol(condition36, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))).AsBool() {
				var exprRead59 distsys.TLAValue
				exprRead59, err1 = ctx.Read(putReq, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var indexRead10 distsys.TLAValue
				indexRead10, err1 = ctx.Read(j, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(replicas1, []distsys.TLAValue{indexRead10}, exprRead59)
				if err1 != nil {
					continue
				}
				var exprRead60 distsys.TLAValue
				exprRead60, err1 = ctx.Read(j, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(j, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead60, distsys.NewTLANumber(1)))
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putBroadcastLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			} else {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putResponseLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			}
			// no statements
		case putResponseLabelTag:
			var condition37 distsys.TLAValue
			condition37, err1 = ctx.Read(i0, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			if distsys.TLA_LessThanSymbol(condition37, distsys.TLA_Cardinality(func() distsys.TLAValue {
				return ReplicaSet(constants)
			}())).AsBool() {
				var condition38 distsys.TLAValue
				condition38, err1 = ctx.Read(clientId0, []distsys.TLAValue{})
				if err1 != nil {
					continue
				}
				var condition39 distsys.TLAValue
				condition39, err1 = ctx.Read(clock0, []distsys.TLAValue{condition38})
				if err1 != nil {
					continue
				}
				if distsys.TLA_EqualsSymbol(condition39, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
					err1 = ctx.Write(continue2, []distsys.TLAValue{}, distsys.TLA_FALSE)
					if err1 != nil {
						continue
					}
					err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putLoopLabelTag))
					if err1 != nil {
						continue
					}
					err1 = ctx.Commit()
					if err1 != nil {
						continue
					}
				} else {
					var exprRead61 distsys.TLAValue
					exprRead61, err1 = ctx.Read(clients1, []distsys.TLAValue{self})
					if err1 != nil {
						continue
					}
					err1 = ctx.Write(putResp, []distsys.TLAValue{}, exprRead61)
					if err1 != nil {
						continue
					}
					var condition40 distsys.TLAValue
					condition40, err1 = ctx.Read(putResp, []distsys.TLAValue{})
					if err1 != nil {
						continue
					}
					if !distsys.TLA_EqualsSymbol(condition40.ApplyFunction(distsys.NewTLAString("type")), constants.PUT_RESPONSE).AsBool() {
						err1 = fmt.Errorf("%w: ((putResp).type) = (PUT_RESPONSE)", distsys.ErrAssertionFailed)
						continue
					}
					var exprRead62 distsys.TLAValue
					exprRead62, err1 = ctx.Read(i0, []distsys.TLAValue{})
					if err1 != nil {
						continue
					}
					err1 = ctx.Write(i0, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead62, distsys.NewTLANumber(1)))
					if err1 != nil {
						continue
					}
					err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putResponseLabelTag))
					if err1 != nil {
						continue
					}
					err1 = ctx.Commit()
					if err1 != nil {
						continue
					}
				}
				// no statements
			} else {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putCompleteLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			}
			// no statements
		case putCompleteLabelTag:
			err1 = ctx.Write(outside0, []distsys.TLAValue{}, constants.PUT_RESPONSE)
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putCheckSpinLabelTag))
			if err1 != nil {
				continue
			}
			err1 = ctx.Commit()
			if err1 != nil {
				continue
			}
		case putCheckSpinLabelTag:
			var condition41 distsys.TLAValue
			condition41, err1 = ctx.Read(spin2, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			if distsys.TLA_LogicalNotSymbol(condition41).AsBool() {
				err1 = ctx.Write(continue2, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err1 != nil {
					continue
				}
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putLoopLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			} else {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(putLoopLabelTag))
				if err1 != nil {
					continue
				}
				err1 = ctx.Commit()
				if err1 != nil {
					continue
				}
			}
			// no statements
		case DoneLabelTag1:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag1)
		}
	}
}

func Disconnect(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, clientId1 distsys.ArchetypeResourceHandle, replicas2 distsys.ArchetypeResourceHandle, clock1 distsys.ArchetypeResourceHandle) error {
	var err2 error
	// label tags
	const (
		InitLabelTag2 = iota
		sendDisconnectRequestLabelTag
		disconnectBroadcastLabelTag
		DoneLabelTag2
	)
	programCounter2 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag2)))
	msg0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg0
	j0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = j0

	for {
		select {
		case <-ctx.Done():
			err2 = distsys.ErrContextClosed
		default:
		}
		if err2 != nil {
			if err2 == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err2 = nil
			} else {
				return err2
			}
		}
		var labelTag2 distsys.TLAValue
		labelTag2, err2 = ctx.Read(programCounter2, []distsys.TLAValue{})
		if err2 != nil {
			return err2
		}
		switch labelTag2.AsNumber() {
		case InitLabelTag2:
			err2 = ctx.Write(programCounter2, []distsys.TLAValue{}, distsys.NewTLANumber(sendDisconnectRequestLabelTag))
			if err2 != nil {
				continue
			}
		case sendDisconnectRequestLabelTag:
			var exprRead63 distsys.TLAValue
			exprRead63, err2 = ctx.Read(clientId1, []distsys.TLAValue{})
			if err2 != nil {
				continue
			}
			err2 = ctx.Write(msg0, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("op"), constants.DISCONNECT_MSG},
				{distsys.NewTLAString("client"), exprRead63},
			}))
			if err2 != nil {
				continue
			}
			var indexRead11 distsys.TLAValue
			indexRead11, err2 = ctx.Read(clientId1, []distsys.TLAValue{})
			if err2 != nil {
				continue
			}
			err2 = ctx.Write(clock1, []distsys.TLAValue{indexRead11}, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))
			if err2 != nil {
				continue
			}
			err2 = ctx.Write(j0, []distsys.TLAValue{}, distsys.NewTLANumber(0))
			if err2 != nil {
				continue
			}
			err2 = ctx.Write(programCounter2, []distsys.TLAValue{}, distsys.NewTLANumber(disconnectBroadcastLabelTag))
			if err2 != nil {
				continue
			}
			err2 = ctx.Commit()
			if err2 != nil {
				continue
			}
		case disconnectBroadcastLabelTag:
			var condition42 distsys.TLAValue
			condition42, err2 = ctx.Read(j0, []distsys.TLAValue{})
			if err2 != nil {
				continue
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_LessThanOrEqualSymbol(condition42, distsys.TLA_MinusSymbol(constants.NUM_REPLICAS, distsys.NewTLANumber(1))), distsys.TLA_NotEqualsSymbol(distsys.NewTLANumber(0), distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))).AsBool() {
				var exprRead64 distsys.TLAValue
				exprRead64, err2 = ctx.Read(msg0, []distsys.TLAValue{})
				if err2 != nil {
					continue
				}
				var indexRead12 distsys.TLAValue
				indexRead12, err2 = ctx.Read(j0, []distsys.TLAValue{})
				if err2 != nil {
					continue
				}
				err2 = ctx.Write(replicas2, []distsys.TLAValue{indexRead12}, exprRead64)
				if err2 != nil {
					continue
				}
				var exprRead65 distsys.TLAValue
				exprRead65, err2 = ctx.Read(j0, []distsys.TLAValue{})
				if err2 != nil {
					continue
				}
				err2 = ctx.Write(j0, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead65, distsys.NewTLANumber(1)))
				if err2 != nil {
					continue
				}
				err2 = ctx.Write(programCounter2, []distsys.TLAValue{}, distsys.NewTLANumber(disconnectBroadcastLabelTag))
				if err2 != nil {
					continue
				}
				err2 = ctx.Commit()
				if err2 != nil {
					continue
				}
			} else {
				err2 = ctx.Write(programCounter2, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag2))
				if err2 != nil {
					continue
				}
				err2 = ctx.Commit()
				if err2 != nil {
					continue
				}
			}
			// no statements
		case DoneLabelTag2:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag2)
		}
	}
}

func ClockUpdate(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, clientId2 distsys.ArchetypeResourceHandle, replicas3 distsys.ArchetypeResourceHandle, clock2 distsys.ArchetypeResourceHandle, spin3 distsys.TLAValue) error {
	var err3 error
	// label tags
	const (
		InitLabelTag3 = iota
		clockUpdateLoopLabelTag
		nullBroadcastLabelTag
		nullCheckSpinLabelTag
		DoneLabelTag3
	)
	programCounter3 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag3)))
	spin4 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(spin3))
	continue3 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = continue3
	j1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = j1
	msg1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg1

	for {
		select {
		case <-ctx.Done():
			err3 = distsys.ErrContextClosed
		default:
		}
		if err3 != nil {
			if err3 == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err3 = nil
			} else {
				return err3
			}
		}
		var labelTag3 distsys.TLAValue
		labelTag3, err3 = ctx.Read(programCounter3, []distsys.TLAValue{})
		if err3 != nil {
			return err3
		}
		switch labelTag3.AsNumber() {
		case InitLabelTag3:
			err3 = ctx.Write(continue3, nil, distsys.TLA_TRUE)
			if err3 != nil {
				continue
			}
			err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(clockUpdateLoopLabelTag))
			if err3 != nil {
				continue
			}
		case clockUpdateLoopLabelTag:
			var condition43 distsys.TLAValue
			condition43, err3 = ctx.Read(continue3, []distsys.TLAValue{})
			if err3 != nil {
				continue
			}
			if condition43.AsBool() {
				var condition44 distsys.TLAValue
				condition44, err3 = ctx.Read(clientId2, []distsys.TLAValue{})
				if err3 != nil {
					continue
				}
				var condition45 distsys.TLAValue
				condition45, err3 = ctx.Read(clock2, []distsys.TLAValue{condition44})
				if err3 != nil {
					continue
				}
				if distsys.TLA_EqualsSymbol(condition45, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1))).AsBool() {
					err3 = ctx.Write(continue3, []distsys.TLAValue{}, distsys.TLA_FALSE)
					if err3 != nil {
						continue
					}
					err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(nullCheckSpinLabelTag))
					if err3 != nil {
						continue
					}
					err3 = ctx.Commit()
					if err3 != nil {
						continue
					}
				} else {
					var exprRead66 distsys.TLAValue
					exprRead66, err3 = ctx.Read(clientId2, []distsys.TLAValue{})
					if err3 != nil {
						continue
					}
					var exprRead67 distsys.TLAValue
					exprRead67, err3 = ctx.Read(clock2, []distsys.TLAValue{exprRead66})
					if err3 != nil {
						continue
					}
					var indexRead13 distsys.TLAValue
					indexRead13, err3 = ctx.Read(clientId2, []distsys.TLAValue{})
					if err3 != nil {
						continue
					}
					err3 = ctx.Write(clock2, []distsys.TLAValue{indexRead13}, distsys.TLA_PlusSymbol(exprRead67, distsys.NewTLANumber(1)))
					if err3 != nil {
						continue
					}
					var exprRead68 distsys.TLAValue
					exprRead68, err3 = ctx.Read(clientId2, []distsys.TLAValue{})
					if err3 != nil {
						continue
					}
					var exprRead69 distsys.TLAValue
					exprRead69, err3 = ctx.Read(clientId2, []distsys.TLAValue{})
					if err3 != nil {
						continue
					}
					var exprRead70 distsys.TLAValue
					exprRead70, err3 = ctx.Read(clock2, []distsys.TLAValue{exprRead69})
					if err3 != nil {
						continue
					}
					err3 = ctx.Write(msg1, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
						{distsys.NewTLAString("op"), constants.NULL_MSG},
						{distsys.NewTLAString("client"), exprRead68},
						{distsys.NewTLAString("timestamp"), exprRead70},
					}))
					if err3 != nil {
						continue
					}
					err3 = ctx.Write(j1, []distsys.TLAValue{}, distsys.NewTLANumber(0))
					if err3 != nil {
						continue
					}
					err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(nullBroadcastLabelTag))
					if err3 != nil {
						continue
					}
					err3 = ctx.Commit()
					if err3 != nil {
						continue
					}
				}
				// no statements
			} else {
				err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag3))
				if err3 != nil {
					continue
				}
				err3 = ctx.Commit()
				if err3 != nil {
					continue
				}
			}
			// no statements
		case nullBroadcastLabelTag:
			var condition46 distsys.TLAValue
			condition46, err3 = ctx.Read(j1, []distsys.TLAValue{})
			if err3 != nil {
				continue
			}
			var condition47 distsys.TLAValue
			condition47, err3 = ctx.Read(clientId2, []distsys.TLAValue{})
			if err3 != nil {
				continue
			}
			var condition48 distsys.TLAValue
			condition48, err3 = ctx.Read(clock2, []distsys.TLAValue{condition47})
			if err3 != nil {
				continue
			}
			if distsys.TLA_LogicalAndSymbol(distsys.TLA_LessThanOrEqualSymbol(condition46, distsys.TLA_MinusSymbol(constants.NUM_REPLICAS, distsys.NewTLANumber(1))), distsys.TLA_NotEqualsSymbol(condition48, distsys.TLA_NegationSymbol(distsys.NewTLANumber(1)))).AsBool() {
				var exprRead71 distsys.TLAValue
				exprRead71, err3 = ctx.Read(msg1, []distsys.TLAValue{})
				if err3 != nil {
					continue
				}
				var indexRead14 distsys.TLAValue
				indexRead14, err3 = ctx.Read(j1, []distsys.TLAValue{})
				if err3 != nil {
					continue
				}
				err3 = ctx.Write(replicas3, []distsys.TLAValue{indexRead14}, exprRead71)
				if err3 != nil {
					continue
				}
				var exprRead72 distsys.TLAValue
				exprRead72, err3 = ctx.Read(j1, []distsys.TLAValue{})
				if err3 != nil {
					continue
				}
				err3 = ctx.Write(j1, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead72, distsys.NewTLANumber(1)))
				if err3 != nil {
					continue
				}
				err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(nullBroadcastLabelTag))
				if err3 != nil {
					continue
				}
				err3 = ctx.Commit()
				if err3 != nil {
					continue
				}
			} else {
				err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(nullCheckSpinLabelTag))
				if err3 != nil {
					continue
				}
				err3 = ctx.Commit()
				if err3 != nil {
					continue
				}
			}
			// no statements
		case nullCheckSpinLabelTag:
			var condition49 distsys.TLAValue
			condition49, err3 = ctx.Read(spin4, []distsys.TLAValue{})
			if err3 != nil {
				continue
			}
			if distsys.TLA_LogicalNotSymbol(condition49).AsBool() {
				err3 = ctx.Write(continue3, []distsys.TLAValue{}, distsys.TLA_FALSE)
				if err3 != nil {
					continue
				}
				err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(clockUpdateLoopLabelTag))
				if err3 != nil {
					continue
				}
				err3 = ctx.Commit()
				if err3 != nil {
					continue
				}
			} else {
				err3 = ctx.Write(programCounter3, []distsys.TLAValue{}, distsys.NewTLANumber(clockUpdateLoopLabelTag))
				if err3 != nil {
					continue
				}
				err3 = ctx.Commit()
				if err3 != nil {
					continue
				}
			}
			// no statements
		case DoneLabelTag3:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag3)
		}
	}
}
