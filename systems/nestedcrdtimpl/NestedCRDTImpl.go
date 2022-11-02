package nestedcrdtimpl

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func MAX_NODE_ID(iface distsys.ArchetypeInterface) tla.Value {
	return tla.Choose(iface.GetConstant("NODE_IDS")(), func(element tla.Value) bool {
		var n tla.Value = element
		_ = n
		return tla.QuantifiedUniversal([]tla.Value{iface.GetConstant("NODE_IDS")()}, func(args []tla.Value) bool {
			var n2 tla.Value = args[0]
			_ = n2
			return tla.Symbol_GreaterThanOrEqualSymbol(n, n2).AsBool()
		}).AsBool()
	})
}
func RESOURCE_OF(iface distsys.ArchetypeInterface, n0 tla.Value) tla.Value {
	return tla.Symbol_PlusSymbol(MAX_NODE_ID(iface), n0)
}
func RESOURCE_IDS(iface distsys.ArchetypeInterface) tla.Value {
	return tla.SetComprehension([]tla.Value{iface.GetConstant("NODE_IDS")()}, func(args0 []tla.Value) tla.Value {
		var n1 tla.Value = args0[0]
		_ = n1
		return RESOURCE_OF(iface, n1)
	})
}
func IncStart(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func IncFinish(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ATestRig.loop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i := iface.RequireArchetypeResource("ATestRig.i")
			iterCount := iface.RequireArchetypeResource("ATestRig.iterCount")
			crdt, err := iface.RequireArchetypeResourceRef("ATestRig.crdt")
			if err != nil {
				return err
			}
			countingCh, err := iface.RequireArchetypeResourceRef("ATestRig.countingCh")
			if err != nil {
				return err
			}
			var condition tla.Value
			condition, err = iface.Read(i, nil)
			if err != nil {
				return err
			}
			var condition0 tla.Value
			condition0, err = iface.Read(iterCount, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_LessThanSymbol(condition, condition0).AsBool() {
				var exprRead tla.Value
				exprRead, err = iface.Read(i, nil)
				if err != nil {
					return err
				}
				err = iface.Write(i, nil, tla.Symbol_PlusSymbol(exprRead, tla.MakeNumber(1)))
				if err != nil {
					return err
				}
				err = iface.Write(crdt, nil, tla.MakeNumber(1))
				if err != nil {
					return err
				}
				var exprRead0 tla.Value
				exprRead0, err = iface.Read(crdt, nil)
				if err != nil {
					return err
				}
				err = iface.Write(countingCh, nil, exprRead0)
				if err != nil {
					return err
				}
				return iface.Goto("ATestRig.loop")
			} else {
				return iface.Goto("ATestRig.endLoop")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ATestRig.endLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			countingCh0, err := iface.RequireArchetypeResourceRef("ATestRig.countingCh")
			if err != nil {
				return err
			}
			crdt1, err := iface.RequireArchetypeResourceRef("ATestRig.crdt")
			if err != nil {
				return err
			}
			var exprRead1 tla.Value
			exprRead1, err = iface.Read(crdt1, nil)
			if err != nil {
				return err
			}
			err = iface.Write(countingCh0, nil, exprRead1)
			if err != nil {
				return err
			}
			return iface.Goto("ATestRig.endLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ATestRig.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ATestBench.benchLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			r := iface.RequireArchetypeResource("ATestBench.r")
			iterCount0 := iface.RequireArchetypeResource("ATestBench.iterCount")
			var condition1 tla.Value
			condition1, err = iface.Read(r, nil)
			if err != nil {
				return err
			}
			var condition2 tla.Value
			condition2, err = iface.Read(iterCount0, nil)
			if err != nil {
				return err
			}
			if tla.Symbol_LessThanSymbol(condition1, condition2).AsBool() {
				return iface.Goto("ATestBench.inc")
			} else {
				return iface.Goto("ATestBench.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ATestBench.inc",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt2, err := iface.RequireArchetypeResourceRef("ATestBench.crdt")
			if err != nil {
				return err
			}
			out, err := iface.RequireArchetypeResourceRef("ATestBench.out")
			if err != nil {
				return err
			}
			err = iface.Write(crdt2, nil, tla.MakeNumber(1))
			if err != nil {
				return err
			}
			err = iface.Write(out, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("node"), iface.Self()},
				{tla.MakeString("event"), IncStart(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("ATestBench.waitInc")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ATestBench.waitInc",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			crdt3, err := iface.RequireArchetypeResourceRef("ATestBench.crdt")
			if err != nil {
				return err
			}
			r0 := iface.RequireArchetypeResource("ATestBench.r")
			numNodes := iface.RequireArchetypeResource("ATestBench.numNodes")
			out0, err := iface.RequireArchetypeResourceRef("ATestBench.out")
			if err != nil {
				return err
			}
			var condition3 tla.Value
			condition3, err = iface.Read(crdt3, nil)
			if err != nil {
				return err
			}
			var condition4 tla.Value
			condition4, err = iface.Read(r0, nil)
			if err != nil {
				return err
			}
			var condition5 tla.Value
			condition5, err = iface.Read(numNodes, nil)
			if err != nil {
				return err
			}
			if !tla.Symbol_GreaterThanOrEqualSymbol(condition3, tla.Symbol_AsteriskSymbol(tla.Symbol_PlusSymbol(condition4, tla.MakeNumber(1)), condition5)).AsBool() {
				return distsys.ErrCriticalSectionAborted
			}
			err = iface.Write(out0, nil, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("node"), iface.Self()},
				{tla.MakeString("event"), IncFinish(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead2 tla.Value
			exprRead2, err = iface.Read(r0, nil)
			if err != nil {
				return err
			}
			err = iface.Write(r0, nil, tla.Symbol_PlusSymbol(exprRead2, tla.MakeNumber(1)))
			if err != nil {
				return err
			}
			return iface.Goto("ATestBench.benchLoop")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ATestBench.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACRDTResource.receiveReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req := iface.RequireArchetypeResource("ACRDTResource.req")
			in, err := iface.RequireArchetypeResourceRef("ACRDTResource.in")
			if err != nil {
				return err
			}
			criticalSectionInProgress := iface.RequireArchetypeResource("ACRDTResource.criticalSectionInProgress")
			readState := iface.RequireArchetypeResource("ACRDTResource.readState")
			state := iface.RequireArchetypeResource("ACRDTResource.state")
			out1, err := iface.RequireArchetypeResourceRef("ACRDTResource.out")
			if err != nil {
				return err
			}
			remainingPeersToUpdate := iface.RequireArchetypeResource("ACRDTResource.remainingPeersToUpdate")
			peers, err := iface.RequireArchetypeResourceRef("ACRDTResource.peers")
			if err != nil {
				return err
			}
			network, err := iface.RequireArchetypeResourceRef("ACRDTResource.network")
			if err != nil {
				return err
			}
			timer, err := iface.RequireArchetypeResourceRef("ACRDTResource.timer")
			if err != nil {
				return err
			}
			switch iface.NextFairnessCounter("ACRDTResource.receiveReq.0", 3) {
			case 0:
				var exprRead3 tla.Value
				exprRead3, err = iface.Read(in, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(req, nil, exprRead3)
				if err != nil {
					return err
				}
				var condition6 tla.Value
				condition6, err = iface.Read(req, nil)
				if err != nil {
					return err
				}
				if tla.Symbol_EqualsSymbol(condition6.ApplyFunction(tla.MakeString("tpe")), iface.GetConstant("READ_REQ")()).AsBool() {
					var condition7 tla.Value
					condition7, err = iface.Read(criticalSectionInProgress, nil)
					if err != nil {
						return err
					}
					if tla.Symbol_LogicalNotSymbol(condition7).AsBool() {
						var exprRead4 tla.Value
						exprRead4, err = iface.Read(state, nil)
						if err != nil {
							return err
						}
						err = iface.Write(readState, nil, exprRead4)
						if err != nil {
							return err
						}
						err = iface.Write(criticalSectionInProgress, nil, tla.Symbol_TRUE)
						if err != nil {
							return err
						}
						// no statements
					} else {
						// no statements
					}
					var exprRead5 tla.Value
					exprRead5, err = iface.Read(readState, nil)
					if err != nil {
						return err
					}
					err = iface.Write(out1, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
						{tla.MakeString("tpe"), iface.GetConstant("READ_ACK")()},
						{tla.MakeString("value"), iface.GetConstant("VIEW_FN")(exprRead5)},
					}))
					if err != nil {
						return err
					}
					// no statements
				} else {
					var condition8 tla.Value
					condition8, err = iface.Read(req, nil)
					if err != nil {
						return err
					}
					if tla.Symbol_EqualsSymbol(condition8.ApplyFunction(tla.MakeString("tpe")), iface.GetConstant("WRITE_REQ")()).AsBool() {
						var condition9 tla.Value
						condition9, err = iface.Read(criticalSectionInProgress, nil)
						if err != nil {
							return err
						}
						if tla.Symbol_LogicalNotSymbol(condition9).AsBool() {
							var exprRead6 tla.Value
							exprRead6, err = iface.Read(state, nil)
							if err != nil {
								return err
							}
							err = iface.Write(readState, nil, exprRead6)
							if err != nil {
								return err
							}
							err = iface.Write(criticalSectionInProgress, nil, tla.Symbol_TRUE)
							if err != nil {
								return err
							}
							// no statements
						} else {
							// no statements
						}
						var exprRead7 tla.Value
						exprRead7, err = iface.Read(readState, nil)
						if err != nil {
							return err
						}
						var exprRead8 tla.Value
						exprRead8, err = iface.Read(req, nil)
						if err != nil {
							return err
						}
						err = iface.Write(readState, nil, iface.GetConstant("UPDATE_FN")(iface.Self(), exprRead7, exprRead8.ApplyFunction(tla.MakeString("value"))))
						if err != nil {
							return err
						}
						err = iface.Write(out1, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
							{tla.MakeString("tpe"), iface.GetConstant("WRITE_ACK")()},
						}))
						if err != nil {
							return err
						}
						// no statements
					} else {
						var condition10 tla.Value
						condition10, err = iface.Read(req, nil)
						if err != nil {
							return err
						}
						if tla.Symbol_EqualsSymbol(condition10.ApplyFunction(tla.MakeString("tpe")), iface.GetConstant("ABORT_REQ")()).AsBool() {
							err = iface.Write(readState, nil, iface.GetConstant("ZERO_VALUE")())
							if err != nil {
								return err
							}
							err = iface.Write(criticalSectionInProgress, nil, tla.Symbol_FALSE)
							if err != nil {
								return err
							}
							err = iface.Write(out1, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
								{tla.MakeString("tpe"), iface.GetConstant("ABORT_ACK")()},
							}))
							if err != nil {
								return err
							}
							// no statements
						} else {
							var condition11 tla.Value
							condition11, err = iface.Read(req, nil)
							if err != nil {
								return err
							}
							if tla.Symbol_EqualsSymbol(condition11.ApplyFunction(tla.MakeString("tpe")), iface.GetConstant("PRECOMMIT_REQ")()).AsBool() {
								err = iface.Write(out1, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
									{tla.MakeString("tpe"), iface.GetConstant("PRECOMMIT_ACK")()},
								}))
								if err != nil {
									return err
								}
								// no statements
							} else {
								var condition12 tla.Value
								condition12, err = iface.Read(req, nil)
								if err != nil {
									return err
								}
								if tla.Symbol_EqualsSymbol(condition12.ApplyFunction(tla.MakeString("tpe")), iface.GetConstant("COMMIT_REQ")()).AsBool() {
									var condition13 tla.Value
									condition13, err = iface.Read(state, nil)
									if err != nil {
										return err
									}
									var condition14 tla.Value
									condition14, err = iface.Read(readState, nil)
									if err != nil {
										return err
									}
									if tla.Symbol_NotEqualsSymbol(condition13, condition14).AsBool() {
										var exprRead9 tla.Value
										exprRead9, err = iface.Read(peers, nil)
										if err != nil {
											return err
										}
										err = iface.Write(remainingPeersToUpdate, nil, exprRead9)
										if err != nil {
											return err
										}
										// no statements
									} else {
										// no statements
									}
									var exprRead10 tla.Value
									exprRead10, err = iface.Read(state, nil)
									if err != nil {
										return err
									}
									var exprRead11 tla.Value
									exprRead11, err = iface.Read(readState, nil)
									if err != nil {
										return err
									}
									err = iface.Write(state, nil, iface.GetConstant("COMBINE_FN")(exprRead10, exprRead11))
									if err != nil {
										return err
									}
									err = iface.Write(readState, nil, iface.GetConstant("ZERO_VALUE")())
									if err != nil {
										return err
									}
									err = iface.Write(criticalSectionInProgress, nil, tla.Symbol_FALSE)
									if err != nil {
										return err
									}
									err = iface.Write(out1, []tla.Value{iface.Self()}, tla.MakeRecord([]tla.RecordField{
										{tla.MakeString("tpe"), iface.GetConstant("COMMIT_ACK")()},
									}))
									if err != nil {
										return err
									}
									// no statements
								} else {
									if !tla.Symbol_FALSE.AsBool() {
										return fmt.Errorf("%w: FALSE", distsys.ErrAssertionFailed)
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
				}
				// no statements
			case 1:
				var updateValRead tla.Value
				updateValRead, err = iface.Read(network, []tla.Value{iface.Self()})
				if err != nil {
					return err
				}
				var updateVal tla.Value = updateValRead
				_ = updateVal
				var exprRead12 tla.Value
				exprRead12, err = iface.Read(state, nil)
				if err != nil {
					return err
				}
				err = iface.Write(state, nil, iface.GetConstant("COMBINE_FN")(updateVal, exprRead12))
				if err != nil {
					return err
				}
				// no statements
				// no statements
			case 2:
				var condition15 tla.Value
				condition15, err = iface.Read(timer, nil)
				if err != nil {
					return err
				}
				if !condition15.AsBool() {
					return distsys.ErrCriticalSectionAborted
				}
				var targetRead tla.Value
				targetRead, err = iface.Read(remainingPeersToUpdate, nil)
				if err != nil {
					return err
				}
				var targetRead0 = targetRead
				if targetRead0.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var target tla.Value = targetRead0.SelectElement(iface.NextFairnessCounter("ACRDTResource.receiveReq.1", uint(targetRead0.AsSet().Len())))
				_ = target
				var exprRead13 tla.Value
				exprRead13, err = iface.Read(state, nil)
				if err != nil {
					return err
				}
				err = iface.Write(network, []tla.Value{target}, exprRead13)
				if err != nil {
					return err
				}
				var exprRead14 tla.Value
				exprRead14, err = iface.Read(remainingPeersToUpdate, nil)
				if err != nil {
					return err
				}
				err = iface.Write(remainingPeersToUpdate, nil, tla.Symbol_BackslashSymbol(exprRead14, tla.MakeSet(target)))
				if err != nil {
					return err
				}
				// no statements
				// no statements
			default:
				panic("current branch of either matches no code paths!")
			}
			return iface.Goto("ACRDTResource.receiveReq")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ACRDTResource.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ATestRig = distsys.MPCalArchetype{
	Name:              "ATestRig",
	Label:             "ATestRig.loop",
	RequiredRefParams: []string{"ATestRig.crdt", "ATestRig.countingCh"},
	RequiredValParams: []string{"ATestRig.iterCount"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ATestRig.i", tla.MakeNumber(0))
	},
}

var ATestBench = distsys.MPCalArchetype{
	Name:              "ATestBench",
	Label:             "ATestBench.benchLoop",
	RequiredRefParams: []string{"ATestBench.crdt", "ATestBench.out"},
	RequiredValParams: []string{"ATestBench.iterCount", "ATestBench.numNodes"},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ATestBench.r", tla.MakeNumber(0))
	},
}

var ACRDTResource = distsys.MPCalArchetype{
	Name:              "ACRDTResource",
	Label:             "ACRDTResource.receiveReq",
	RequiredRefParams: []string{"ACRDTResource.in", "ACRDTResource.out", "ACRDTResource.network", "ACRDTResource.peers", "ACRDTResource.timer"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ACRDTResource.remainingPeersToUpdate", tla.MakeSet())
		iface.EnsureArchetypeResourceLocal("ACRDTResource.req", tla.Value{})
		iface.EnsureArchetypeResourceLocal("ACRDTResource.criticalSectionInProgress", tla.Symbol_FALSE)
		iface.EnsureArchetypeResourceLocal("ACRDTResource.state", iface.GetConstant("ZERO_VALUE")())
		iface.EnsureArchetypeResourceLocal("ACRDTResource.readState", iface.ReadArchetypeResourceLocal("ACRDTResource.state"))
	},
}
