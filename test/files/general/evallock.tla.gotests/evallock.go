package evallock

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func ServerID(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(0)
}
func ServerSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(ServerID(iface))
}
func ClientSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumClients")())
}
func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_UnionSymbol(ServerSet(iface), ClientSet(iface))
}
func LockMsg(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func UnlockMsg(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func GrantMsg(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.serverLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if tla.TLA_TRUE.AsBool() {
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
			var exprRead tla.TLAValue
			exprRead, err = iface.Read(network, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg, []tla.TLAValue{}, exprRead)
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
			var condition tla.TLAValue
			condition, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("type")), LockMsg(iface)).AsBool() {
				var condition0 tla.TLAValue
				condition0, err = iface.Read(q, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition0, tla.MakeTLATuple()).AsBool() {
					var indexRead tla.TLAValue
					indexRead, err = iface.Read(msg0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(network0, []tla.TLAValue{indexRead.ApplyFunction(tla.MakeTLAString("from"))}, GrantMsg(iface))
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead0 tla.TLAValue
				exprRead0, err = iface.Read(q, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(msg0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(q, []tla.TLAValue{}, tla.TLA_Append(exprRead0, exprRead1.ApplyFunction(tla.MakeTLAString("from"))))
				if err != nil {
					return err
				}
				return iface.Goto("AServer.serverLoop")
			} else {
				var condition1 tla.TLAValue
				condition1, err = iface.Read(msg0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition1.ApplyFunction(tla.MakeTLAString("type")), UnlockMsg(iface)).AsBool() {
					var exprRead2 tla.TLAValue
					exprRead2, err = iface.Read(q, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(q, []tla.TLAValue{}, tla.TLA_Tail(exprRead2))
					if err != nil {
						return err
					}
					var condition2 tla.TLAValue
					condition2, err = iface.Read(q, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_NotEqualsSymbol(condition2, tla.MakeTLATuple()).AsBool() {
						var indexRead0 tla.TLAValue
						indexRead0, err = iface.Read(q, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(network0, []tla.TLAValue{tla.TLA_Head(indexRead0)}, GrantMsg(iface))
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
			err = iface.Write(network2, []tla.TLAValue{ServerID(iface)}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("type"), LockMsg(iface)},
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
			hasLock := iface.RequireArchetypeResource("AClient.hasLock")
			var respRead tla.TLAValue
			respRead, err = iface.Read(network3, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			var resp tla.TLAValue = respRead
			_ = resp
			if !tla.TLA_EqualsSymbol(resp, GrantMsg(iface)).AsBool() {
				return fmt.Errorf("%w: (resp) = (GrantMsg)", distsys.ErrAssertionFailed)
			}
			// no statements
			err = iface.Write(hasLock, []tla.TLAValue{}, tla.TLA_TRUE)
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
			network4, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			hasLock0 := iface.RequireArchetypeResource("AClient.hasLock")
			err = iface.Write(network4, []tla.TLAValue{ServerID(iface)}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("type"), UnlockMsg(iface)},
			}))
			if err != nil {
				return err
			}
			err = iface.Write(hasLock0, []tla.TLAValue{}, tla.TLA_FALSE)
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
		iface.EnsureArchetypeResourceLocal("AServer.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AServer.q", tla.MakeTLATuple())
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.acquireLock",
	RequiredRefParams: []string{"AClient.network"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.hasLock", tla.TLA_FALSE)
	},
}
