package kvs

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
func Key1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key1")
}
func Key2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key2")
}
func Key3(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key3")
}
func Key4(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key4")
}
func KeySet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(Key1(iface), Key2(iface), Key3(iface), Key4(iface))
}
func Value1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value1")
}
func Value2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value2")
}
func Value3(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value3")
}
func Value4(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value4")
}
func GetRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func GetResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func PutRequest(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func PutResponse(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(4)
}
func Get(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func Put(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func ServerSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumServers")())
}
func ClientSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NumServers")(), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(iface.GetConstant("NumServers")(), iface.GetConstant("NumClients")()))
}
func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_UnionSymbol(ServerSet(iface), ClientSet(iface))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req := iface.RequireArchetypeResource("AServer.req")
			net, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var exprRead tla.TLAValue
				exprRead, err = iface.Read(net, []tla.TLAValue{iface.Self()})
				if err != nil {
					return err
				}
				err = iface.Write(req, []tla.TLAValue{}, exprRead)
				if err != nil {
					return err
				}
				var condition tla.TLAValue
				condition, err = iface.Read(req, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if !tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("dest")), iface.Self()).AsBool() {
					return fmt.Errorf("%w: ((req).dest) = (self)", distsys.ErrAssertionFailed)
				}
				return iface.Goto("AServer.handleReq")
			} else {
				return iface.Goto("AServer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.handleReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req1 := iface.RequireArchetypeResource("AServer.req")
			kvs, err := iface.RequireArchetypeResourceRef("AServer.kvs")
			if err != nil {
				return err
			}
			net0, err := iface.RequireArchetypeResourceRef("AServer.net")
			if err != nil {
				return err
			}
			var condition0 tla.TLAValue
			condition0, err = iface.Read(req1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition0.ApplyFunction(tla.MakeTLAString("type")), GetRequest(iface)).AsBool() {
				var i tla.TLAValue = iface.Self()
				_ = i
				var jRead tla.TLAValue
				jRead, err = iface.Read(req1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var j tla.TLAValue = jRead.ApplyFunction(tla.MakeTLAString("source"))
				_ = j
				var foundRead tla.TLAValue
				foundRead, err = iface.Read(req1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var foundRead0 tla.TLAValue
				foundRead0, err = iface.Read(kvs, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var found tla.TLAValue = tla.TLA_InSymbol(foundRead.ApplyFunction(tla.MakeTLAString("key")), tla.TLA_DomainSymbol(foundRead0))
				_ = found
				var valueRead tla.TLAValue
				valueRead, err = iface.Read(kvs, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var valueRead0 tla.TLAValue
				valueRead0, err = iface.Read(req1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var value tla.TLAValue = func() tla.TLAValue {
					if found.AsBool() {
						return valueRead.ApplyFunction(valueRead0.ApplyFunction(tla.MakeTLAString("key")))
					} else {
						return Nil(iface)
					}
				}()
				_ = value
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(req1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(req1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(net0, []tla.TLAValue{j}, tla.MakeTLARecord([]tla.TLARecordField{
					{tla.MakeTLAString("type"), GetResponse(iface)},
					{tla.MakeTLAString("found"), found},
					{tla.MakeTLAString("key"), exprRead0.ApplyFunction(tla.MakeTLAString("key"))},
					{tla.MakeTLAString("value"), value},
					{tla.MakeTLAString("idx"), exprRead1.ApplyFunction(tla.MakeTLAString("idx"))},
					{tla.MakeTLAString("source"), i},
					{tla.MakeTLAString("dest"), j},
				}))
				if err != nil {
					return err
				}
				return iface.Goto("AServer.serverLoop")
				// no statements
			} else {
				var condition1 tla.TLAValue
				condition1, err = iface.Read(req1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition1.ApplyFunction(tla.MakeTLAString("type")), PutRequest(iface)).AsBool() {
					var condition2 tla.TLAValue
					condition2, err = iface.Read(req1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition3 tla.TLAValue
					condition3, err = iface.Read(kvs, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_NotInSymbol(condition2.ApplyFunction(tla.MakeTLAString("key")), tla.TLA_DomainSymbol(condition3)).AsBool() {
						var exprRead2 tla.TLAValue
						exprRead2, err = iface.Read(kvs, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead3 tla.TLAValue
						exprRead3, err = iface.Read(req1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead4 tla.TLAValue
						exprRead4, err = iface.Read(req1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(kvs, []tla.TLAValue{}, tla.TLA_DoubleAtSignSymbol(exprRead2, tla.TLA_ColonGreaterThanSymbol(exprRead3.ApplyFunction(tla.MakeTLAString("key")), exprRead4.ApplyFunction(tla.MakeTLAString("value")))))
						if err != nil {
							return err
						}
						// no statements
					} else {
						var exprRead5 tla.TLAValue
						exprRead5, err = iface.Read(kvs, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead6 tla.TLAValue
						exprRead6, err = iface.Read(req1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead7 tla.TLAValue
						exprRead7, err = iface.Read(req1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(kvs, []tla.TLAValue{}, tla.TLAFunctionSubstitution(exprRead5, []tla.TLAFunctionSubstitutionRecord{
							{[]tla.TLAValue{exprRead6.ApplyFunction(tla.MakeTLAString("key"))}, func(anchor tla.TLAValue) tla.TLAValue {
								return exprRead7.ApplyFunction(tla.MakeTLAString("value"))
							}},
						}))
						if err != nil {
							return err
						}
						// no statements
					}
					var i0 tla.TLAValue = iface.Self()
					_ = i0
					var jRead0 tla.TLAValue
					jRead0, err = iface.Read(req1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var j0 tla.TLAValue = jRead0.ApplyFunction(tla.MakeTLAString("source"))
					_ = j0
					var exprRead8 tla.TLAValue
					exprRead8, err = iface.Read(req1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead9 tla.TLAValue
					exprRead9, err = iface.Read(req1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead10 tla.TLAValue
					exprRead10, err = iface.Read(req1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net0, []tla.TLAValue{j0}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("type"), PutResponse(iface)},
						{tla.MakeTLAString("key"), exprRead8.ApplyFunction(tla.MakeTLAString("key"))},
						{tla.MakeTLAString("value"), exprRead9.ApplyFunction(tla.MakeTLAString("value"))},
						{tla.MakeTLAString("idx"), exprRead10.ApplyFunction(tla.MakeTLAString("idx"))},
						{tla.MakeTLAString("source"), i0},
						{tla.MakeTLAString("dest"), j0},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AServer.serverLoop")
					// no statements
				} else {
					return iface.Goto("AServer.serverLoop")
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
		Name: "AClient.clientLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req17 := iface.RequireArchetypeResource("AClient.req")
			in, err := iface.RequireArchetypeResourceRef("AClient.in")
			if err != nil {
				return err
			}
			reqIdx := iface.RequireArchetypeResource("AClient.reqIdx")
			if tla.TLA_TRUE.AsBool() {
				var exprRead11 tla.TLAValue
				exprRead11, err = iface.Read(in, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(req17, []tla.TLAValue{}, exprRead11)
				if err != nil {
					return err
				}
				var exprRead12 tla.TLAValue
				exprRead12, err = iface.Read(reqIdx, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(reqIdx, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead12, tla.MakeTLANumber(1)))
				if err != nil {
					return err
				}
				return iface.Goto("AClient.selectServer")
			} else {
				return iface.Goto("AClient.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.selectServer",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			srv := iface.RequireArchetypeResource("AClient.srv")
			fd, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			var condition4 tla.TLAValue
			condition4, err = iface.Read(srv, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanOrEqualSymbol(condition4, iface.GetConstant("NumServers")()).AsBool() {
				var condition5 tla.TLAValue
				condition5, err = iface.Read(srv, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var condition6 tla.TLAValue
				condition6, err = iface.Read(fd, []tla.TLAValue{condition5})
				if err != nil {
					return err
				}
				if tla.TLA_LogicalNotSymbol(condition6).AsBool() {
					return iface.Goto("AClient.sndReq")
				} else {
					var exprRead13 tla.TLAValue
					exprRead13, err = iface.Read(srv, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(srv, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead13, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					var condition7 tla.TLAValue
					condition7, err = iface.Read(srv, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_GreaterThanSymbol(condition7, iface.GetConstant("NumServers")()).AsBool() {
						err = iface.Write(srv, []tla.TLAValue{}, tla.MakeTLANumber(1))
						if err != nil {
							return err
						}
						return iface.Goto("AClient.selectServer")
					} else {
						return iface.Goto("AClient.selectServer")
					}
					// no statements
				}
				// no statements
			} else {
				return iface.Goto("AClient.sndReq")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sndReq",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			req18 := iface.RequireArchetypeResource("AClient.req")
			net2, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			srv5 := iface.RequireArchetypeResource("AClient.srv")
			reqIdx1 := iface.RequireArchetypeResource("AClient.reqIdx")
			fd0, err := iface.RequireArchetypeResourceRef("AClient.fd")
			if err != nil {
				return err
			}
			var condition8 tla.TLAValue
			condition8, err = iface.Read(req18, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition8.ApplyFunction(tla.MakeTLAString("type")), Put(iface)).AsBool() {
				switch iface.NextFairnessCounter("AClient.sndReq.0", 2) {
				case 0:
					var exprRead14 tla.TLAValue
					exprRead14, err = iface.Read(reqIdx1, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead15 tla.TLAValue
					exprRead15, err = iface.Read(req18, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead16 tla.TLAValue
					exprRead16, err = iface.Read(req18, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead17 tla.TLAValue
					exprRead17, err = iface.Read(srv5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead tla.TLAValue
					indexRead, err = iface.Read(srv5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(net2, []tla.TLAValue{indexRead}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("type"), PutRequest(iface)},
						{tla.MakeTLAString("idx"), exprRead14},
						{tla.MakeTLAString("key"), exprRead15.ApplyFunction(tla.MakeTLAString("key"))},
						{tla.MakeTLAString("value"), exprRead16.ApplyFunction(tla.MakeTLAString("value"))},
						{tla.MakeTLAString("source"), iface.Self()},
						{tla.MakeTLAString("dest"), exprRead17},
					}))
					if err != nil {
						return err
					}
					return iface.Goto("AClient.rcvResp")
				case 1:
					var condition10 tla.TLAValue
					condition10, err = iface.Read(srv5, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var condition11 tla.TLAValue
					condition11, err = iface.Read(fd0, []tla.TLAValue{condition10})
					if err != nil {
						return err
					}
					if !condition11.AsBool() {
						return distsys.ErrCriticalSectionAborted
					}
					return iface.Goto("AClient.rcvResp")
				default:
					panic("current branch of either matches no code paths!")
				}
				// no statements
			} else {
				var condition9 tla.TLAValue
				condition9, err = iface.Read(req18, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition9.ApplyFunction(tla.MakeTLAString("type")), Get(iface)).AsBool() {
					switch iface.NextFairnessCounter("AClient.sndReq.1", 2) {
					case 0:
						var exprRead18 tla.TLAValue
						exprRead18, err = iface.Read(reqIdx1, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead19 tla.TLAValue
						exprRead19, err = iface.Read(req18, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var exprRead20 tla.TLAValue
						exprRead20, err = iface.Read(srv5, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead0 tla.TLAValue
						indexRead0, err = iface.Read(srv5, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(net2, []tla.TLAValue{indexRead0}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("type"), GetRequest(iface)},
							{tla.MakeTLAString("idx"), exprRead18},
							{tla.MakeTLAString("key"), exprRead19.ApplyFunction(tla.MakeTLAString("key"))},
							{tla.MakeTLAString("source"), iface.Self()},
							{tla.MakeTLAString("dest"), exprRead20},
						}))
						if err != nil {
							return err
						}
						return iface.Goto("AClient.rcvResp")
					case 1:
						var condition12 tla.TLAValue
						condition12, err = iface.Read(srv5, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var condition13 tla.TLAValue
						condition13, err = iface.Read(fd0, []tla.TLAValue{condition12})
						if err != nil {
							return err
						}
						if !condition13.AsBool() {
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
			net4, err := iface.RequireArchetypeResourceRef("AClient.net")
			if err != nil {
				return err
			}
			reqIdx3 := iface.RequireArchetypeResource("AClient.reqIdx")
			out, err := iface.RequireArchetypeResourceRef("AClient.out")
			if err != nil {
				return err
			}
			var exprRead21 tla.TLAValue
			exprRead21, err = iface.Read(net4, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(resp, []tla.TLAValue{}, exprRead21)
			if err != nil {
				return err
			}
			var condition14 tla.TLAValue
			condition14, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			var condition15 tla.TLAValue
			condition15, err = iface.Read(reqIdx3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition14.ApplyFunction(tla.MakeTLAString("idx")), condition15).AsBool() {
				return fmt.Errorf("%w: ((resp).idx) = (reqIdx)", distsys.ErrAssertionFailed)
			}
			var exprRead22 tla.TLAValue
			exprRead22, err = iface.Read(resp, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(out, []tla.TLAValue{}, exprRead22)
			if err != nil {
				return err
			}
			return iface.Goto("AClient.clientLoop")
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
	RequiredRefParams: []string{"AServer.net", "AServer.kvs"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.req", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.clientLoop",
	RequiredRefParams: []string{"AClient.net", "AClient.in", "AClient.out", "AClient.fd"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.req", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.reqIdx", tla.MakeTLANumber(0))
		iface.EnsureArchetypeResourceLocal("AClient.srv", tla.MakeTLANumber(1))
		iface.EnsureArchetypeResourceLocal("AClient.resp", tla.TLAValue{})
	},
}
