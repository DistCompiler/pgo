package kvs

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func Key1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key1")
}
func Key2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("key2")
}
func KeySet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(Key1(iface), Key2(iface))
}
func Value1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value1")
}
func Value2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("value2")
}
func ValueSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(Value1(iface), Value2(iface))
}
func WriteNodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumWriteNodes")())
}
func ReadNodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.TLA_PlusSymbol(iface.GetConstant("NumWriteNodes")(), tla.MakeTLANumber(1)), tla.TLA_PlusSymbol(iface.GetConstant("NumWriteNodes")(), iface.GetConstant("NumReadNodes")()))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "AWriteNode.writeNodeLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			kvs, err := iface.RequireArchetypeResourceRef("AWriteNode.kvs")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var keyRead = KeySet(iface)
				if keyRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var key tla.TLAValue = keyRead.SelectElement(iface.NextFairnessCounter("AWriteNode.writeNodeLoop.0", uint(keyRead.AsSet().Len())))
				_ = key
				var valRead = ValueSet(iface)
				if valRead.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var val tla.TLAValue = valRead.SelectElement(iface.NextFairnessCounter("AWriteNode.writeNodeLoop.1", uint(valRead.AsSet().Len())))
				_ = val
				err = iface.Write(kvs, []tla.TLAValue{key}, val)
				if err != nil {
					return err
				}
				return iface.Goto("AWriteNode.writeNodeLoop")
				// no statements
			} else {
				return iface.Goto("AWriteNode.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AWriteNode.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReadNode.readNodeLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			kvs0, err := iface.RequireArchetypeResourceRef("AReadNode.kvs")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var keyRead0 = KeySet(iface)
				if keyRead0.AsSet().Len() == 0 {
					return distsys.ErrCriticalSectionAborted
				}
				var key0 tla.TLAValue = keyRead0.SelectElement(iface.NextFairnessCounter("AReadNode.readNodeLoop.0", uint(keyRead0.AsSet().Len())))
				_ = key0
				var toPrint tla.TLAValue
				toPrint, err = iface.Read(kvs0, []tla.TLAValue{key0})
				if err != nil {
					return err
				}
				tla.MakeTLATuple(key0, toPrint).PCalPrint()
				return iface.Goto("AReadNode.readNodeLoop")
				// no statements
			} else {
				return iface.Goto("AReadNode.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "AReadNode.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var AWriteNode = distsys.MPCalArchetype{
	Name:              "AWriteNode",
	Label:             "AWriteNode.writeNodeLoop",
	RequiredRefParams: []string{"AWriteNode.kvs"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}

var AReadNode = distsys.MPCalArchetype{
	Name:              "AReadNode",
	Label:             "AReadNode.readNodeLoop",
	RequiredRefParams: []string{"AReadNode.kvs"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
