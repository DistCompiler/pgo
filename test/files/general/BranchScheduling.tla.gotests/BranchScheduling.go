package branchscheduling

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.ErrDone
var _ = tla.TLAValue{} // same, for tla

func TheSet(iface distsys.ArchetypeInterface) tla.TLAValue {
	return tla.MakeTLASet(tla.MakeTLANumber(1), tla.MakeTLANumber(2))
}

var procTable = distsys.MakeMPCalProcTable()

var jumpTable = distsys.MakeMPCalJumpTable(
	distsys.MPCalCriticalSection{
		Name: "ABranch.loop",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i := iface.RequireArchetypeResource("ABranch.i")
			var condition tla.TLAValue
			condition, err = iface.Read(i, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition, tla.MakeTLANumber(20)).AsBool() {
				return iface.Goto("ABranch.branchlabel")
			} else {
				return iface.Goto("ABranch.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ABranch.branchlabel",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i0 := iface.RequireArchetypeResource("ABranch.i")
			j := iface.RequireArchetypeResource("ABranch.j")
			k := iface.RequireArchetypeResource("ABranch.k")

			val, _ := iface.Read(i0, []tla.TLAValue{})
			fmt.Printf("i0: %v\n", val)
			val, _ = iface.Read(j, []tla.TLAValue{})
			fmt.Printf("j: %v\n", val)
			val, _ = iface.Read(k, []tla.TLAValue{})
			fmt.Printf("k: %v\n", val)

			return iface.RunBranchConcurrently(
				func(branchResourceMap distsys.BranchResourceMap) error {
					fmt.Println("CASE 0")
					var exprRead tla.TLAValue
					exprRead, err = iface.BranchRead(i0, []tla.TLAValue{}, branchResourceMap)
					if err != nil {
						return err
					}
					err = iface.BranchWrite(i0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead, tla.MakeTLANumber(1)), branchResourceMap)
					if err != nil {
						return err
					}

					val, _ := iface.Read(i0, []tla.TLAValue{})
					fmt.Printf("i0: %v\n", val)
					val, _ = iface.Read(j, []tla.TLAValue{})
					fmt.Printf("j: %v\n", val)
					val, _ = iface.Read(k, []tla.TLAValue{})
					fmt.Printf("k: %v\n", val)

					return iface.Goto("ABranch.lbl1")
				},
				func(branchResourceMap distsys.BranchResourceMap) error {
					fmt.Println("CASE 1")
					var exprRead0 tla.TLAValue
					exprRead0, err = iface.BranchRead(j, []tla.TLAValue{}, branchResourceMap)
					if err != nil {
						return err
					}
					err = iface.BranchWrite(j, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead0, tla.MakeTLANumber(5)), branchResourceMap)
					if err != nil {
						return err
					}

					val, _ := iface.Read(i0, []tla.TLAValue{})
					fmt.Printf("i0: %v\n", val)
					val, _ = iface.Read(j, []tla.TLAValue{})
					fmt.Printf("j: %v\n", val)
					val, _ = iface.Read(k, []tla.TLAValue{})
					fmt.Printf("k: %v\n", val)

					return iface.Goto("ABranch.lbl1")
				},
				func(branchResourceMap distsys.BranchResourceMap) error {
					fmt.Println("CASE 2")
					var exprRead1 tla.TLAValue
					exprRead1, err = iface.BranchRead(j, []tla.TLAValue{}, branchResourceMap)
					if err != nil {
						return err
					}
					var exprRead2 tla.TLAValue
					exprRead2, err = iface.BranchRead(k, []tla.TLAValue{}, branchResourceMap)
					if err != nil {
						return err
					}
					err = iface.BranchWrite(k, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead1, exprRead2), branchResourceMap)
					if err != nil {
						return err
					}

					val, _ := iface.Read(i0, []tla.TLAValue{})
					fmt.Printf("i0: %v\n", val)
					val, _ = iface.Read(j, []tla.TLAValue{})
					fmt.Printf("j: %v\n", val)
					val, _ = iface.Read(k, []tla.TLAValue{})
					fmt.Printf("k: %v\n", val)

					return iface.Goto("ABranch.lbl1")
				})

			//Just fork all the variables above into some kind of structure where each go routine gets its own set
			//PrepareBranches()
			//Switch all cases into functional go routines sharing one channel that lets us know when they are done
			//switch iface.NextFairnessCounter("ABranch.branchlabel.0", 3) {
			//case 0:
			//	fmt.Println("CASE 0")
			//	var exprRead tla.TLAValue
			//	exprRead, err = iface.Read(i0, []tla.TLAValue{})
			//	if err != nil {
			//		return err
			//	}
			//	err = iface.Write(i0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead, tla.MakeTLANumber(1)))
			//	if err != nil {
			//		return err
			//	}
			//	return iface.Goto("ABranch.lbl1")
			//case 1:
			//	fmt.Println("CASE 1")
			//	var exprRead0 tla.TLAValue
			//	exprRead0, err = iface.Read(j, []tla.TLAValue{})
			//	if err != nil {
			//		return err
			//	}
			//	err = iface.Write(j, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead0, tla.MakeTLANumber(5)))
			//	if err != nil {
			//		return err
			//	}
			//	return iface.Goto("ABranch.lbl1")
			//case 2:
			//	fmt.Println("CASE 2")
			//	var exprRead1 tla.TLAValue
			//	exprRead1, err = iface.Read(j, []tla.TLAValue{})
			//	if err != nil {
			//		return err
			//	}
			//	var exprRead2 tla.TLAValue
			//	exprRead2, err = iface.Read(k, []tla.TLAValue{})
			//	if err != nil {
			//		return err
			//	}
			//	err = iface.Write(k, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead1, exprRead2))
			//	if err != nil {
			//		return err
			//	}
			//	return iface.Goto("ABranch.lbl1")
			//default:
			//	panic("current branch of either matches no code paths!")
			//}
			//RecognizeBranch()
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ABranch.lbl1",
		Body: func(iface distsys.ArchetypeInterface) error {
			var err error
			_ = err
			mark := iface.RequireArchetypeResource("ABranch.mark")
			var aRead = TheSet(iface)
			if aRead.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a tla.TLAValue = aRead.SelectElement(iface.NextFairnessCounter("ABranch.lbl1.0", uint(aRead.AsSet().Len())))
			_ = a
			var exprRead3 tla.TLAValue
			exprRead3, err = iface.Read(mark, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mark, []tla.TLAValue{}, tla.TLA_UnionSymbol(exprRead3, tla.MakeTLASet(a)))
			if err != nil {
				return err
			}
			return iface.Goto("ABranch.loop")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ABranch.Done",
		Body: func(distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
)

var ABranch = distsys.MPCalArchetype{
	Name:              "ABranch",
	Label:             "ABranch.loop",
	RequiredRefParams: []string{},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ABranch.i", tla.MakeTLANumber(0))
		iface.EnsureArchetypeResourceLocal("ABranch.j", tla.MakeTLANumber(2))
		iface.EnsureArchetypeResourceLocal("ABranch.k", tla.MakeTLANumber(4))
		iface.EnsureArchetypeResourceLocal("ABranch.mark", tla.MakeTLASet())
	},
}
