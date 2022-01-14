package shopcart

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func AddCmd(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(1)
}
func RemoveCmd(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLANumber(2)
}
func Elem1(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("elem1")
}
func Elem2(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLAString("elem2")
}
func NodeSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.TLA_DotDotSymbol(tla.MakeTLANumber(1), iface.GetConstant("NumNodes")())
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ANode.nodeLoop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			in, err := iface.RequireArchetypeResourceRef("ANode.in")
			if err != nil {
				return err
			}
			cart, err := iface.RequireArchetypeResourceRef("ANode.cart")
			if err != nil {
				return err
			}
			if tla.TLA_TRUE.AsBool() {
				var reqRead tla.TLAValue
				reqRead, err = iface.Read(in, []tla.TLAValue{})
				if err != nil {
					return err
				}
				var req tla.TLAValue = reqRead
				_ = req
				if tla.TLA_EqualsSymbol(req.ApplyFunction(tla.MakeTLAString("cmd")), AddCmd(iface)).AsBool() {
					var exprRead tla.TLAValue
					exprRead, err = iface.Read(cart, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(cart, []tla.TLAValue{}, tla.TLA_UnionSymbol(exprRead, tla.MakeTLASet(req.ApplyFunction(tla.MakeTLAString("elem")))))
					if err != nil {
						return err
					}
					return iface.Goto("ANode.nodeLoop")
				} else {
					if tla.TLA_EqualsSymbol(req.ApplyFunction(tla.MakeTLAString("cmd")), RemoveCmd(iface)).AsBool() {
						var exprRead0 tla.TLAValue
						exprRead0, err = iface.Read(cart, []tla.TLAValue{})
						if err != nil {
							return err
						}
						err = iface.Write(cart, []tla.TLAValue{}, tla.TLA_BackslashSymbol(exprRead0, tla.MakeTLASet(req.ApplyFunction(tla.MakeTLAString("elem")))))
						if err != nil {
							return err
						}
						return iface.Goto("ANode.nodeLoop")
					} else {
						return iface.Goto("ANode.nodeLoop")
					}
					// no statements
				}
				// no statements
				// no statements
			} else {
				return iface.Goto("ANode.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANode.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ANode = distsys.MPCalArchetype{
	Name:              "ANode",
	Label:             "ANode.nodeLoop",
	RequiredRefParams: []string{"ANode.cart", "ANode.in"},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
	},
}
