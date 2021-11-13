package keylock_verdi

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrContextClosed
var _ = tla.TLAValue{} // same, for tla

func GrantMsgType(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func UnlockMsgType(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func LockMsgType(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(3)
}
func LOCK_SERVER_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(iface.GetConstant("LOCK_SERVER_ID")())
}
func CLIENT_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(2), tla.TLA_PlusSymbol(iface.GetConstant("NUM_CLIENTS")(), tla.MakeTLANumber(1)))
}
func NODE_SET(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), tla.TLA_PlusSymbol(iface.GetConstant("NUM_CLIENTS")(), tla.MakeTLANumber(1)))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AServer.server_l1",
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
			return iface.Goto("AServer.server_l2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.server_l2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg0 := iface.RequireArchetypeResource("AServer.msg")
			s := iface.RequireArchetypeResource("AServer.s")
			reply := iface.RequireArchetypeResource("AServer.reply")
			network0, err := iface.RequireArchetypeResourceRef("AServer.network")
			if err != nil {
				return err
			}
			var condition tla.TLAValue
			condition, err = iface.Read(msg0, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_EqualsSymbol(condition.ApplyFunction(tla.MakeTLAString("type")), LockMsgType(iface)).AsBool() {
				var condition0 tla.TLAValue
				condition0, err = iface.Read(s, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition0, tla.MakeTLATuple()).AsBool() {
					err = iface.Write(reply, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
						{tla.MakeTLAString("from"), iface.Self()},
						{tla.MakeTLAString("type"), GrantMsgType(iface)},
					}))
					if err != nil {
						return err
					}
					var exprRead0 tla.TLAValue
					exprRead0, err = iface.Read(reply, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var indexRead tla.TLAValue
					indexRead, err = iface.Read(msg0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(network0, []tla.TLAValue{indexRead.ApplyFunction(tla.MakeTLAString("from"))}, exprRead0)
					if err != nil {
						return err
					}
					// no statements
				} else {
					// no statements
				}
				var exprRead1 tla.TLAValue
				exprRead1, err = iface.Read(s, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var exprRead2 tla.TLAValue
				exprRead2, err = iface.Read(msg0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				err = iface.Write(s, []tla.TLAValue{}, tla.TLA_Append(exprRead1, exprRead2.ApplyFunction(tla.MakeTLAString("from"))))
				if err != nil {
					return err
				}
				// no statements
			} else {
				var condition1 tla.TLAValue
				condition1, err = iface.Read(msg0, []tla.TLAValue{})
				if err != nil {
					return err
				}
				if tla.TLA_EqualsSymbol(condition1.ApplyFunction(tla.MakeTLAString("type")), UnlockMsgType(iface)).AsBool() {
					var exprRead3 tla.TLAValue
					exprRead3, err = iface.Read(s, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(s, []tla.TLAValue{}, tla.TLA_Tail(exprRead3))
					if err != nil {
						return err
					}
					var condition2 tla.TLAValue
					condition2, err = iface.Read(s, []tla.TLAValue{})
					if err != nil {
						return err
					}
					if tla.TLA_NotEqualsSymbol(condition2, tla.MakeTLATuple()).AsBool() {
						err = iface.Write(reply, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
							{tla.MakeTLAString("from"), iface.Self()},
							{tla.MakeTLAString("type"), GrantMsgType(iface)},
						}))
						if err != nil {
							return err
						}
						var exprRead4 tla.TLAValue
						exprRead4, err = iface.Read(reply, []tla.TLAValue{})
						if err != nil {
							return err
						}
						var indexRead0 tla.TLAValue
						indexRead0, err = iface.Read(s, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(network0, []tla.TLAValue{tla.TLA_Head(indexRead0)}, exprRead4)
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
				// no statements
			}
			return iface.Goto("AServer.server_l1")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AServer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.client_l1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			request := iface.RequireArchetypeResource("AClient.request")
			network2, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			err = iface.Write(request, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("type"), LockMsgType(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead5 tla.TLAValue
			exprRead5, err = iface.Read(request, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(network2, []tla.TLAValue{iface.GetConstant("LOCK_SERVER_ID")()}, exprRead5)
			if err != nil {
				return err
			}
			return iface.Goto("AClient.client_l2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.client_l2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			msg4 := iface.RequireArchetypeResource("AClient.msg")
			network3, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			var exprRead6 tla.TLAValue
			exprRead6, err = iface.Read(network3, []tla.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(msg4, []tla.TLAValue{}, exprRead6)
			if err != nil {
				return err
			}
			var condition3 tla.TLAValue
			condition3, err = iface.Read(msg4, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if !tla.TLA_EqualsSymbol(condition3.ApplyFunction(tla.MakeTLAString("type")), GrantMsgType(iface)).AsBool() {
				return fmt.Errorf("%w: ((msg).type) = (GrantMsgType)", distsys.ErrAssertionFailed)
			}
			return iface.Goto("AClient.client_l3")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AClient.client_l3",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			request1 := iface.RequireArchetypeResource("AClient.request")
			network4, err := iface.RequireArchetypeResourceRef("AClient.network")
			if err != nil {
				return err
			}
			err = iface.Write(request1, []tla.TLAValue{}, tla.MakeTLARecord([]tla.TLARecordField{
				{tla.MakeTLAString("from"), iface.Self()},
				{tla.MakeTLAString("type"), UnlockMsgType(iface)},
			}))
			if err != nil {
				return err
			}
			var exprRead7 tla.TLAValue
			exprRead7, err = iface.Read(request1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(network4, []tla.TLAValue{iface.GetConstant("LOCK_SERVER_ID")()}, exprRead7)
			if err != nil {
				return err
			}
			return iface.Goto("AClient.client_l1")
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
	Label:             "AServer.server_l1",
	RequiredRefParams: []string{"AServer.network"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AServer.msg", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AServer.s", tla.MakeTLATuple())
		iface.EnsureArchetypeResourceLocal("AServer.reply", tla.TLAValue{})
	},
}

var AClient = distsys.MPCalArchetype{
	Name:              "AClient",
	Label:             "AClient.client_l1",
	RequiredRefParams: []string{"AClient.network"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AClient.request", tla.TLAValue{})
		iface.EnsureArchetypeResourceLocal("AClient.msg", tla.TLAValue{})
	},
}
