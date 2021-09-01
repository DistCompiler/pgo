package dqueue

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

func NUM_NODES(iface distsys.ArchetypeInterface) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(iface.GetConstant("NUM_CONSUMERS")(), distsys.NewTLANumber(1))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AConsumer.c",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if distsys.TLA_TRUE.AsBool() {
				return iface.Goto("AConsumer.c1")
			} else {
				return iface.Goto("AConsumer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AConsumer.c1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net, err := iface.RequireArchetypeResourceRef("AConsumer.net")
			if err != nil {
				return err
			}
			err = iface.Write(net, []distsys.TLAValue{iface.GetConstant("PRODUCER")()}, iface.Self())
			if err != nil {
				return err
			}
			return iface.Goto("AConsumer.c2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AConsumer.c2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			proc, err := iface.RequireArchetypeResourceRef("AConsumer.proc")
			if err != nil {
				return err
			}
			net0, err := iface.RequireArchetypeResourceRef("AConsumer.net")
			if err != nil {
				return err
			}
			var exprRead distsys.TLAValue
			exprRead, err = iface.Read(net0, []distsys.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(proc, []distsys.TLAValue{}, exprRead)
			if err != nil {
				return err
			}
			return iface.Goto("AConsumer.c")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AConsumer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProducer.p",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			if distsys.TLA_TRUE.AsBool() {
				return iface.Goto("AProducer.p1")
			} else {
				return iface.Goto("AProducer.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProducer.p1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			requester := iface.RequireArchetypeResource("AProducer.requester")
			net1, err := iface.RequireArchetypeResourceRef("AProducer.net")
			if err != nil {
				return err
			}
			var exprRead0 distsys.TLAValue
			exprRead0, err = iface.Read(net1, []distsys.TLAValue{iface.Self()})
			if err != nil {
				return err
			}
			err = iface.Write(requester, []distsys.TLAValue{}, exprRead0)
			if err != nil {
				return err
			}
			return iface.Goto("AProducer.p2")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProducer.p2",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			net2, err := iface.RequireArchetypeResourceRef("AProducer.net")
			if err != nil {
				return err
			}
			requester0 := iface.RequireArchetypeResource("AProducer.requester")
			s, err := iface.RequireArchetypeResourceRef("AProducer.s")
			if err != nil {
				return err
			}
			var exprRead1 distsys.TLAValue
			exprRead1, err = iface.Read(s, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			var indexRead distsys.TLAValue
			indexRead, err = iface.Read(requester0, []distsys.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(net2, []distsys.TLAValue{indexRead}, exprRead1)
			if err != nil {
				return err
			}
			return iface.Goto("AProducer.p")
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AProducer.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AConsumer = distsys.MPCalArchetype{
	Name:              "AConsumer",
	Label:             "AConsumer.c",
	RequiredRefParams: []string{"AConsumer.net", "AConsumer.proc"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var AProducer = distsys.MPCalArchetype{
	Name:              "AProducer",
	Label:             "AProducer.p",
	RequiredRefParams: []string{"AProducer.net", "AProducer.s"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("AProducer.requester", distsys.TLAValue{})
	},
}
