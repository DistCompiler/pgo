package my_lock

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func ServerID(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func LockMsg(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("Lock!")
}
func UnlockMsg(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("Unlock!")
}
func GrantMsg(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("Has Lock!")
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
			var toPrint tla.TLAValue
			toPrint, err = iface.Read(msg, []tla.TLAValue{})
			if err != nil {
				return err
			}
			toPrint.PCalPrint()
			return iface.Goto("AServer.serverRespond")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.serverRespond",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg1 := iface.RequireArchetypeResource("AServer.msg")
			q := iface.RequireArchetypeResource("AServer.q")
			network0, err := iface.RequireArchetypeResourceRef("AServer.network")
			if err != nil {
				return err
			}
			var condition tla.TLAValue
			condition, err = iface.Read(msg1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("type")), LockMsg(iface)).AsBool() {
				tla.MakeTLAString("Receive LockMsg").PCalPrint()
				var condition0 tla.TLAValue
				condition0, err = iface.Read(q, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition0, tla.MakeTLATuple()).AsBool() {
					var indexRead tla.TLAValue
					indexRead, err = iface.Read(msg1, []tla.TLAValue{})
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
				exprRead1, err = iface.Read(msg1, []tla.TLAValue{})
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
				condition1, err = iface.Read(msg1, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition1.ApplyFunction(tla.MakeTLAString("type")), UnlockMsg(iface)).AsBool() {
					tla.MakeTLAString("Receive UnlockMsg").PCalPrint()
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
		Name: "AClient.requestLock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			network2, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			err = iface.Write(network2, []tla.TLAValue{ServerID(iface)}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("type"), LockMsg(iface)},
				{tla.MakeTLAString("from"), iface.Self()},
			}))
			if err != nil {
				return err
			}
			LockMsg(iface).PCalPrint()
			return iface.Goto("AClient.receiveLock")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.receiveLock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg5 := iface.RequireArchetypeResource("AClient.msg")
			network3, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			var exprRead3 tla.TLAValue
			exprRead3, err = iface.Read(network3, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg5, []tla.TLAValue{}, exprRead3)
			if err != nil {
				return err
			}
			var toPrint0 tla.TLAValue
			toPrint0, err = iface.Read(msg5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			toPrint0.PCalPrint()
			var condition3 tla.TLAValue
			condition3, err = iface.Read(msg5, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition3, GrantMsg(iface)).AsBool() {
				return fmt.Errorf("%w: (msg) = (GrantMsg)", distsys.ErrAssertionFailed)
			}
			return iface.Goto("AClient.sendUnlock")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.sendUnlock",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			network4, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			err = iface.Write(network4, []tla.TLAValue{ServerID(iface)}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("type"), UnlockMsg(iface)},
				{tla.MakeTLAString("from"), iface.Self()},
			}))
			if err != nil {
				return err
			}
			UnlockMsg(iface).PCalPrint()
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
	Label:             "AClient.requestLock",
	RequiredRefParams: []string{"AClient.network"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.msg", tla.TLAValue{})
	},
}
