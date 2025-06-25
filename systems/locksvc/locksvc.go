package locksvc

import (
	"fmt"
	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.Value{} // same, for tla

func ServerID(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(0)
}
func ServerSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeSet(ServerID(iface))
}
func ClientSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleDotDotSymbol(tla.MakeNumber(1), iface.GetConstant("NumClients")())
}
func NodeSet(iface distsys.ArchetypeInterface) tla.Value {
	return tla.ModuleUnionSymbol(ServerSet(iface), ClientSet(iface))
}
func LockMsg(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(1)
}
func UnlockMsg(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(2)
}
func GrantMsg(iface distsys.ArchetypeInterface) tla.Value {
	return tla.MakeNumber(3)
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.ModuleTRUE.AsBool() {
				return iface.Goto("AServer.serverReceive")
			} else {
				return iface.Goto("AServer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverReceive",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg := iface.RequireArchetypeResource("AServer.msg")
			network, err := iface.RequireArchetypeResourceRef("AServer.network")
			if err != nil {
				return err
			}
			var exprRead tla.Value
			exprRead, err = iface.Read(network, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, nil, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("AServer.serverRespond")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverRespond",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg0 := iface.RequireArchetypeResource("AServer.msg")
			q := iface.RequireArchetypeResource("AServer.q")
			network0, err := iface.RequireArchetypeResourceRef("AServer.network")
			if err != nil {
				return err
			}
			var condition tla.Value
			condition, err = iface.Read(msg0, nil)
			if err != nil {
				return err
			}
			if tla.ModuleEqualsSymbol(condition.ApplyFunction(tla.MakeString("type")), LockMsg(iface)).AsBool() {
				var condition0 tla.Value
				condition0, err = iface.Read(q, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition0, tla.MakeTuple()).AsBool() {
					var indexRead tla.Value
					indexRead, err = iface.Read(msg0, nil)
					if err != nil {
						return err
					}
					err = iface.Write(network0, []tla.Value{indexRead.ApplyFunction(tla.MakeString("from"))}, GrantMsg(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead0 tla.Value
				exprRead0, err = iface.Read(q, nil)
				if err != nil {
					return err
				}
				var exprRead1 tla.Value
				exprRead1, err = iface.Read(msg0, nil)
				if err != nil {
					return err
				}
				err = iface.Write(q, nil, tla.ModuleAppend(exprRead0, exprRead1.ApplyFunction(tla.MakeString("from"))))
				if err != nil {
					return err
				}
				return iface.Goto("AServer.serverLoop")
			} else {
				var condition1 tla.Value
				condition1, err = iface.Read(msg0, nil)
				if err != nil {
					return err
				}
				if tla.ModuleEqualsSymbol(condition1.ApplyFunction(tla.MakeString("type")), UnlockMsg(iface)).AsBool() {
					var exprRead2 tla.Value
					exprRead2, err = iface.Read(q, nil)
					if err != nil {
						return err
					}
					err = iface.Write(q, nil, tla.ModuleTail(exprRead2))
					if err != nil {
						return err
					}
					var condition2 tla.Value
					condition2, err = iface.Read(q, nil)
					if err != nil {
						return err
					}
					if tla.ModuleNotEqualsSymbol(condition2, tla.MakeTuple()).AsBool() {
						var indexRead0 tla.Value
						indexRead0, err = iface.Read(q, nil)
						if err != nil {
							return err
						}
						err = iface.Write(network0, []tla.Value{tla.ModuleHead(indexRead0)}, GrantMsg(iface))
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
		Name: "AClient.acquireLock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			network2, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			err = iface.Write(network2, []tla.Value{ServerID(iface)}, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("type"), LockMsg(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("AClient.criticalSection")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.criticalSection",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			network3, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			hasLock, err := iface.RequireArchetypeResourceRef("AClient.hasLock")
			if err != nil {
				return err
			}
			var respRead tla.Value
			respRead, err = iface.Read(network3, []tla.Value{iface.Self()})
			if err != nil {
				return err
			}
			var resp tla.Value = respRead
			_ = resp
			if !tla.ModuleEqualsSymbol(resp, GrantMsg(iface)).AsBool() {
				return fmt.Errorf("%w: (resp) = (GrantMsg)", distsys.ErrAssertionFailed)
			}
			// no statements
			err = iface.Write(hasLock, []tla.Value{iface.Self()}, tla.ModuleTRUE)
			if err != nil {
				return err
			}
			return iface.Goto("AClient.unlock")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.unlock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			hasLock0, err := iface.RequireArchetypeResourceRef("AClient.hasLock")
			if err != nil {
				return err
			}
			network4, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			err = iface.Write(hasLock0, []tla.Value{iface.Self()}, tla.ModuleFALSE)
			if err != nil {
				return err
			}
			err = iface.Write(network4, []tla.Value{ServerID(iface)}, tla.MakeRecord([]tla.RecordField{
				{tla.MakeString("from"), iface.Self()},
				{tla.MakeString("type"), UnlockMsg(iface)},
			}))
			if err != nil {
				return err
			}
			return iface.Goto("AClient.Done")
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
	RequiredRefParams: []string{"AServer.network"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.msg", tla.Value{})
		iface.EnsureArchetypeResourceLocal("AServer.q", tla.MakeTuple())
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.acquireLock",
	RequiredRefParams: []string{"AClient.network", "AClient.hasLock"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
