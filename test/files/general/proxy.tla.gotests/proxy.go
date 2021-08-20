package proxy

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	NUM_SERVERS  distsys.TLAValue
	NUM_CLIENTS  distsys.TLAValue
	EXPLORE_FAIL distsys.TLAValue
	F            distsys.TLAValue
}

func FAIL(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(100)
}

func NUM_NODES(constants Constants) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(distsys.TLA_PlusSymbol(constants.NUM_SERVERS, constants.NUM_CLIENTS), distsys.NewTLANumber(1))
}

func ProxyID(constants Constants) distsys.TLAValue {
	return func() distsys.TLAValue {
		return NUM_NODES(constants)
	}()
}

func REQ_MSG_TYP(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(1)
}

func RESP_MSG_TYP(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(2)
}

func PROXY_REQ_MSG_TYP(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(3)
}

func PROXY_RESP_MSG_TYP(constants Constants) distsys.TLAValue {
	return distsys.NewTLANumber(4)
}

func NODE_SET(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.NewTLANumber(1), func() distsys.TLAValue {
		return NUM_NODES(constants)
	}())
}

func SERVER_SET(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.NewTLANumber(1), constants.NUM_SERVERS)
}

func CLIENT_SET(constants Constants) distsys.TLAValue {
	return distsys.TLA_DotDotSymbol(distsys.TLA_PlusSymbol(constants.NUM_SERVERS, distsys.NewTLANumber(1)), distsys.TLA_PlusSymbol(constants.NUM_SERVERS, constants.NUM_CLIENTS))
}

func MSG_TYP_SET(constants Constants) distsys.TLAValue {
	return distsys.NewTLASet(func() distsys.TLAValue {
		return REQ_MSG_TYP(constants)
	}(), func() distsys.TLAValue {
		return RESP_MSG_TYP(constants)
	}(), func() distsys.TLAValue {
		return PROXY_REQ_MSG_TYP(constants)
	}(), func() distsys.TLAValue {
		return PROXY_RESP_MSG_TYP(constants)
	}())
}

func AProxy(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net distsys.ArchetypeResourceHandle, fd distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		InitLabelTag = iota
		proxyLoopLabelTag
		rcvMsgFromClientLabelTag
		proxyMsgLabelTag
		serversLoopLabelTag
		proxySendMsgLabelTag
		proxyRcvMsgLabelTag
		sendMsgToClientLabelTag
		DoneLabelTag
	)
	programCounter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag)))
	msg := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg
	proxyMsg0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = proxyMsg0
	idx := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = idx
	resp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = resp
	proxyResp := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = proxyResp
	var fairnessCounter int = 0
	var fairnessCounter0 int = 0

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
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(proxyLoopLabelTag))
			if err != nil {
				continue
			}
		case proxyLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgFromClientLabelTag))
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
		case rcvMsgFromClientLabelTag:
			var exprRead distsys.TLAValue
			exprRead, err = ctx.Read(net, []distsys.TLAValue{distsys.NewTLATuple(func() distsys.TLAValue {
				return ProxyID(constants)
			}(), func() distsys.TLAValue {
				return REQ_MSG_TYP(constants)
			}())})
			if err != nil {
				continue
			}
			err = ctx.Write(msg, []distsys.TLAValue{}, exprRead)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(proxyMsgLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case proxyMsgLabelTag:
			var condition distsys.TLAValue
			condition, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var condition0 distsys.TLAValue
			condition0, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if !distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition.ApplyFunction(distsys.NewTLAString("to")), func() distsys.TLAValue {
				return ProxyID(constants)
			}()), distsys.TLA_EqualsSymbol(condition0.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
				return REQ_MSG_TYP(constants)
			}())).AsBool() {
				err = fmt.Errorf("%w: (((msg).to) = (ProxyID)) /\\ (((msg).typ) = (REQ_MSG_TYP))", distsys.ErrAssertionFailed)
				continue
			}
			var exprRead0 distsys.TLAValue
			exprRead0, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead1 distsys.TLAValue
			exprRead1, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(proxyResp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), func() distsys.TLAValue {
					return ProxyID(constants)
				}()},
				{distsys.NewTLAString("to"), exprRead0.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), func() distsys.TLAValue {
					return FAIL(constants)
				}()},
				{distsys.NewTLAString("id"), exprRead1.ApplyFunction(distsys.NewTLAString("id"))},
				{distsys.NewTLAString("typ"), func() distsys.TLAValue {
					return PROXY_RESP_MSG_TYP(constants)
				}()},
			}))
			if err != nil {
				continue
			}
			err = ctx.Write(idx, []distsys.TLAValue{}, distsys.NewTLANumber(1))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(serversLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case serversLoopLabelTag:
			var condition1 distsys.TLAValue
			condition1, err = ctx.Read(idx, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			if distsys.TLA_LessThanOrEqualSymbol(condition1, constants.NUM_SERVERS).AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(proxySendMsgLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sendMsgToClientLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case proxySendMsgLabelTag:
			fairnessCounterCurrent := fairnessCounter
			fairnessCounter = (fairnessCounter + 1) % 2
			switch fairnessCounterCurrent {
			case 0:
				var exprRead6 distsys.TLAValue
				exprRead6, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead7 distsys.TLAValue
				exprRead7, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var exprRead8 distsys.TLAValue
				exprRead8, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(proxyMsg0, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
					{distsys.NewTLAString("from"), func() distsys.TLAValue {
						return ProxyID(constants)
					}()},
					{distsys.NewTLAString("to"), exprRead6},
					{distsys.NewTLAString("body"), exprRead7.ApplyFunction(distsys.NewTLAString("body"))},
					{distsys.NewTLAString("id"), exprRead8.ApplyFunction(distsys.NewTLAString("id"))},
					{distsys.NewTLAString("typ"), func() distsys.TLAValue {
						return PROXY_REQ_MSG_TYP(constants)
					}()},
				}))
				if err != nil {
					continue
				}
				var exprRead9 distsys.TLAValue
				exprRead9, err = ctx.Read(proxyMsg0, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var indexRead1 distsys.TLAValue
				indexRead1, err = ctx.Read(proxyMsg0, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(net, []distsys.TLAValue{distsys.NewTLATuple(indexRead1.ApplyFunction(distsys.NewTLAString("to")), func() distsys.TLAValue {
					return PROXY_REQ_MSG_TYP(constants)
				}())}, exprRead9)
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(proxyRcvMsgLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			case 1:
				var condition2 distsys.TLAValue
				condition2, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition3 distsys.TLAValue
				condition3, err = ctx.Read(fd, []distsys.TLAValue{condition2})
				if err != nil {
					continue
				}
				if !condition3.AsBool() {
					err = distsys.ErrCriticalSectionAborted
					continue
				}
				var exprRead10 distsys.TLAValue
				exprRead10, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(idx, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead10, distsys.NewTLANumber(1)))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(serversLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		case proxyRcvMsgLabelTag:
			fairnessCounterCurrent0 := fairnessCounter0
			fairnessCounter0 = (fairnessCounter0 + 1) % 2
			switch fairnessCounterCurrent0 {
			case 0:
				var exprRead11 distsys.TLAValue
				exprRead11, err = ctx.Read(net, []distsys.TLAValue{distsys.NewTLATuple(func() distsys.TLAValue {
					return ProxyID(constants)
				}(), func() distsys.TLAValue {
					return PROXY_RESP_MSG_TYP(constants)
				}())})
				if err != nil {
					continue
				}
				err = ctx.Write(proxyResp, []distsys.TLAValue{}, exprRead11)
				if err != nil {
					continue
				}
				var condition4 distsys.TLAValue
				condition4, err = ctx.Read(proxyResp, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition5 distsys.TLAValue
				condition5, err = ctx.Read(proxyResp, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition6 distsys.TLAValue
				condition6, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition7 distsys.TLAValue
				condition7, err = ctx.Read(proxyResp, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition8 distsys.TLAValue
				condition8, err = ctx.Read(msg, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition9 distsys.TLAValue
				condition9, err = ctx.Read(proxyResp, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				if !distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition4.ApplyFunction(distsys.NewTLAString("to")), func() distsys.TLAValue {
					return ProxyID(constants)
				}()), distsys.TLA_EqualsSymbol(condition5.ApplyFunction(distsys.NewTLAString("from")), condition6)), distsys.TLA_EqualsSymbol(condition7.ApplyFunction(distsys.NewTLAString("id")), condition8.ApplyFunction(distsys.NewTLAString("id")))), distsys.TLA_EqualsSymbol(condition9.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
					return PROXY_RESP_MSG_TYP(constants)
				}())).AsBool() {
					err = fmt.Errorf("%w: (((((proxyResp).to) = (ProxyID)) /\\ (((proxyResp).from) = (idx))) /\\ (((proxyResp).id) = ((msg).id))) /\\ (((proxyResp).typ) = (PROXY_RESP_MSG_TYP))", distsys.ErrAssertionFailed)
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sendMsgToClientLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			case 1:
				var condition10 distsys.TLAValue
				condition10, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				var condition11 distsys.TLAValue
				condition11, err = ctx.Read(fd, []distsys.TLAValue{condition10})
				if err != nil {
					continue
				}
				if !condition11.AsBool() {
					err = distsys.ErrCriticalSectionAborted
					continue
				}
				var exprRead12 distsys.TLAValue
				exprRead12, err = ctx.Read(idx, []distsys.TLAValue{})
				if err != nil {
					continue
				}
				err = ctx.Write(idx, []distsys.TLAValue{}, distsys.TLA_PlusSymbol(exprRead12, distsys.NewTLANumber(1)))
				if err != nil {
					continue
				}
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(serversLoopLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			default:
				panic("current branch of either matches no code paths!")
			}
			// no statements
		case sendMsgToClientLabelTag:
			var exprRead2 distsys.TLAValue
			exprRead2, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead3 distsys.TLAValue
			exprRead3, err = ctx.Read(proxyResp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead4 distsys.TLAValue
			exprRead4, err = ctx.Read(proxyResp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(resp, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), func() distsys.TLAValue {
					return ProxyID(constants)
				}()},
				{distsys.NewTLAString("to"), exprRead2.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead3.ApplyFunction(distsys.NewTLAString("body"))},
				{distsys.NewTLAString("id"), exprRead4.ApplyFunction(distsys.NewTLAString("id"))},
				{distsys.NewTLAString("typ"), func() distsys.TLAValue {
					return RESP_MSG_TYP(constants)
				}()},
			}))
			if err != nil {
				continue
			}
			var exprRead5 distsys.TLAValue
			exprRead5, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead distsys.TLAValue
			indexRead, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err = ctx.Read(resp, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(net, []distsys.TLAValue{distsys.NewTLATuple(indexRead.ApplyFunction(distsys.NewTLAString("to")), indexRead0.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead5)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(proxyLoopLabelTag))
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

func AServer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net0 distsys.ArchetypeResourceHandle, netEnabled distsys.ArchetypeResourceHandle, fd0 distsys.ArchetypeResourceHandle) error {
	var err0 error
	// label tags
	const (
		InitLabelTag0 = iota
		serverLoopLabelTag
		serverRcvMsgLabelTag
		serverSendMsgLabelTag
		failLabelLabelTag
		DoneLabelTag0
	)
	programCounter0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag0)))
	msg0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg0
	resp0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = resp0
	var fairnessCounter1 int = 0
	var fairnessCounter2 int = 0
	var fairnessCounter3 int = 0

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
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverLoopLabelTag))
			if err0 != nil {
				continue
			}
		case serverLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				if constants.EXPLORE_FAIL.AsBool() {
					fairnessCounterCurrent1 := fairnessCounter1
					fairnessCounter1 = (fairnessCounter1 + 1) % 2
					switch fairnessCounterCurrent1 {
					case 0:
						// skip
						err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverRcvMsgLabelTag))
						if err0 != nil {
							continue
						}
						err0 = ctx.Commit()
						if err0 != nil {
							continue
						}
					case 1:
						err0 = ctx.Write(netEnabled, []distsys.TLAValue{self}, distsys.TLA_FALSE)
						if err0 != nil {
							continue
						}
						err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(failLabelLabelTag))
						if err0 != nil {
							continue
						}
						err0 = ctx.Commit()
						if err0 != nil {
							continue
						}
					default:
						panic("current branch of either matches no code paths!")
					}
					// no statements
				} else {
					err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverRcvMsgLabelTag))
					if err0 != nil {
						continue
					}
					err0 = ctx.Commit()
					if err0 != nil {
						continue
					}
				}
				// no statements
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(failLabelLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case serverRcvMsgLabelTag:
			var exprRead13 distsys.TLAValue
			exprRead13, err0 = ctx.Read(net0, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
				return PROXY_REQ_MSG_TYP(constants)
			}())})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(msg0, []distsys.TLAValue{}, exprRead13)
			if err0 != nil {
				continue
			}
			var condition12 distsys.TLAValue
			condition12, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition13 distsys.TLAValue
			condition13, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var condition14 distsys.TLAValue
			condition14, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			if !distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition12.ApplyFunction(distsys.NewTLAString("to")), self), distsys.TLA_EqualsSymbol(condition13.ApplyFunction(distsys.NewTLAString("from")), func() distsys.TLAValue {
				return ProxyID(constants)
			}())), distsys.TLA_EqualsSymbol(condition14.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
				return PROXY_REQ_MSG_TYP(constants)
			}())).AsBool() {
				err0 = fmt.Errorf("%w: ((((msg).to) = (self)) /\\ (((msg).from) = (ProxyID))) /\\ (((msg).typ) = (PROXY_REQ_MSG_TYP))", distsys.ErrAssertionFailed)
				continue
			}
			if constants.EXPLORE_FAIL.AsBool() {
				fairnessCounterCurrent2 := fairnessCounter2
				fairnessCounter2 = (fairnessCounter2 + 1) % 2
				switch fairnessCounterCurrent2 {
				case 0:
					// skip
					err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverSendMsgLabelTag))
					if err0 != nil {
						continue
					}
					err0 = ctx.Commit()
					if err0 != nil {
						continue
					}
				case 1:
					err0 = ctx.Write(netEnabled, []distsys.TLAValue{self}, distsys.TLA_FALSE)
					if err0 != nil {
						continue
					}
					err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(failLabelLabelTag))
					if err0 != nil {
						continue
					}
					err0 = ctx.Commit()
					if err0 != nil {
						continue
					}
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverSendMsgLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case serverSendMsgLabelTag:
			var exprRead14 distsys.TLAValue
			exprRead14, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var exprRead15 distsys.TLAValue
			exprRead15, err0 = ctx.Read(msg0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(resp0, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), self},
				{distsys.NewTLAString("to"), exprRead14.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), self},
				{distsys.NewTLAString("id"), exprRead15.ApplyFunction(distsys.NewTLAString("id"))},
				{distsys.NewTLAString("typ"), func() distsys.TLAValue {
					return PROXY_RESP_MSG_TYP(constants)
				}()},
			}))
			if err0 != nil {
				continue
			}
			var exprRead16 distsys.TLAValue
			exprRead16, err0 = ctx.Read(resp0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var indexRead2 distsys.TLAValue
			indexRead2, err0 = ctx.Read(resp0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var indexRead3 distsys.TLAValue
			indexRead3, err0 = ctx.Read(resp0, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(net0, []distsys.TLAValue{distsys.NewTLATuple(indexRead2.ApplyFunction(distsys.NewTLAString("to")), indexRead3.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead16)
			if err0 != nil {
				continue
			}
			if constants.EXPLORE_FAIL.AsBool() {
				fairnessCounterCurrent3 := fairnessCounter3
				fairnessCounter3 = (fairnessCounter3 + 1) % 2
				switch fairnessCounterCurrent3 {
				case 0:
					// skip
					err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverLoopLabelTag))
					if err0 != nil {
						continue
					}
					err0 = ctx.Commit()
					if err0 != nil {
						continue
					}
				case 1:
					err0 = ctx.Write(netEnabled, []distsys.TLAValue{self}, distsys.TLA_FALSE)
					if err0 != nil {
						continue
					}
					err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(failLabelLabelTag))
					if err0 != nil {
						continue
					}
					err0 = ctx.Commit()
					if err0 != nil {
						continue
					}
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(serverLoopLabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case failLabelLabelTag:
			err0 = ctx.Write(fd0, []distsys.TLAValue{self}, distsys.TLA_TRUE)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag0))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case DoneLabelTag0:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag0)
		}
	}
}

func AClient(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net1 distsys.ArchetypeResourceHandle) error {
	var err1 error
	// label tags
	const (
		InitLabelTag1 = iota
		clientLoopLabelTag
		clientSendReqLabelTag
		clientRcvRespLabelTag
		DoneLabelTag1
	)
	programCounter1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag1)))
	req := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = req
	resp1 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = resp1

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
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientLoopLabelTag))
			if err1 != nil {
				continue
			}
		case clientLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientSendReqLabelTag))
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
		case clientSendReqLabelTag:
			err1 = ctx.Write(req, []distsys.TLAValue{}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), self},
				{distsys.NewTLAString("to"), func() distsys.TLAValue {
					return ProxyID(constants)
				}()},
				{distsys.NewTLAString("body"), self},
				{distsys.NewTLAString("id"), distsys.NewTLANumber(0)},
				{distsys.NewTLAString("typ"), func() distsys.TLAValue {
					return REQ_MSG_TYP(constants)
				}()},
			}))
			if err1 != nil {
				continue
			}
			var exprRead17 distsys.TLAValue
			exprRead17, err1 = ctx.Read(req, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var indexRead4 distsys.TLAValue
			indexRead4, err1 = ctx.Read(req, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var indexRead5 distsys.TLAValue
			indexRead5, err1 = ctx.Read(req, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(net1, []distsys.TLAValue{distsys.NewTLATuple(indexRead4.ApplyFunction(distsys.NewTLAString("to")), indexRead5.ApplyFunction(distsys.NewTLAString("typ")))}, exprRead17)
			if err1 != nil {
				continue
			}
			var toPrint distsys.TLAValue
			toPrint, err1 = ctx.Read(req, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			distsys.NewTLATuple(distsys.NewTLAString("CLIENT START"), toPrint).PCalPrint()
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientRcvRespLabelTag))
			if err1 != nil {
				continue
			}
			err1 = ctx.Commit()
			if err1 != nil {
				continue
			}
		case clientRcvRespLabelTag:
			var exprRead18 distsys.TLAValue
			exprRead18, err1 = ctx.Read(net1, []distsys.TLAValue{distsys.NewTLATuple(self, func() distsys.TLAValue {
				return RESP_MSG_TYP(constants)
			}())})
			if err1 != nil {
				continue
			}
			err1 = ctx.Write(resp1, []distsys.TLAValue{}, exprRead18)
			if err1 != nil {
				continue
			}
			var condition15 distsys.TLAValue
			condition15, err1 = ctx.Read(resp1, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var condition16 distsys.TLAValue
			condition16, err1 = ctx.Read(resp1, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			var condition17 distsys.TLAValue
			condition17, err1 = ctx.Read(resp1, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			if !distsys.TLA_LogicalAndSymbol(distsys.TLA_LogicalAndSymbol(distsys.TLA_EqualsSymbol(condition15.ApplyFunction(distsys.NewTLAString("to")), self), distsys.TLA_EqualsSymbol(condition16.ApplyFunction(distsys.NewTLAString("id")), distsys.NewTLANumber(0))), distsys.TLA_EqualsSymbol(condition17.ApplyFunction(distsys.NewTLAString("typ")), func() distsys.TLAValue {
				return RESP_MSG_TYP(constants)
			}())).AsBool() {
				err1 = fmt.Errorf("%w: ((((resp).to) = (self)) /\\ (((resp).id) = (0))) /\\ (((resp).typ) = (RESP_MSG_TYP))", distsys.ErrAssertionFailed)
				continue
			}
			var toPrint0 distsys.TLAValue
			toPrint0, err1 = ctx.Read(resp1, []distsys.TLAValue{})
			if err1 != nil {
				continue
			}
			distsys.NewTLATuple(distsys.NewTLAString("CLIENT RESP"), toPrint0).PCalPrint()
			err1 = ctx.Write(programCounter1, []distsys.TLAValue{}, distsys.NewTLANumber(clientLoopLabelTag))
			if err1 != nil {
				continue
			}
			err1 = ctx.Commit()
			if err1 != nil {
				continue
			}
		case DoneLabelTag1:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag1)
		}
	}
}
