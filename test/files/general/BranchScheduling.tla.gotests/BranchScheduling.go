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
		Body: func(iface *distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i := iface.RequireArchetypeResource("ABranch.i")
			var condition tla.TLAValue
			condition, err = iface.Read(i, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition, tla.MakeTLANumber(10)).AsBool() {
				return iface.Goto("ABranch.branchlabel")
			} else {
				return iface.Goto("ABranch.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ABranch.branchlabel",
		Body: func(iface *distsys.ArchetypeInterface) error {
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
				//switch iface.NextFairnessCounter("ABranch.branchlabel.0", 3) {
				func(iface *distsys.ArchetypeInterface) error {
					//fmt.Println("CASE 0")
					var exprRead tla.TLAValue
					exprRead, err = iface.Read(i0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(i0, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead, tla.MakeTLANumber(1)))
					if err != nil {
						return err
					}
					return iface.Goto("ABranch.lbl1")
				},
				func(iface *distsys.ArchetypeInterface) error {
					//fmt.Println("CASE 1")
					var exprRead0 tla.TLAValue
					exprRead0, err = iface.Read(j, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(j, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead0, tla.MakeTLANumber(5)))
					if err != nil {
						return err
					}
					return iface.Goto("ABranch.lbl1")
				},
				func(iface *distsys.ArchetypeInterface) error {
					//fmt.Println("CASE 2")
					var exprRead1 tla.TLAValue
					exprRead1, err = iface.Read(i0, []tla.TLAValue{})
					if err != nil {
						return err
					}
					var exprRead2 tla.TLAValue
					exprRead2, err = iface.Read(k, []tla.TLAValue{})
					if err != nil {
						return err
					}
					err = iface.Write(k, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead1, exprRead2))
					if err != nil {
						return err
					}
					return iface.Goto("ABranch.lbl1")
				})
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ABranch.lbl1",
		Body: func(iface *distsys.ArchetypeInterface) error {
			var err error
			_ = err
			mark := iface.RequireArchetypeResource("ABranch.mark")
			var aRead = TheSet(*iface)
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
		Body: func(*distsys.ArchetypeInterface) error {
			return distsys.ErrDone
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANestedBranch.loop",
		Body: func(iface *distsys.ArchetypeInterface) error {
			var err error
			_ = err
			i3 := iface.RequireArchetypeResource("ANestedBranch.i")
			var condition0 tla.TLAValue
			condition0, err = iface.Read(i3, []tla.TLAValue{})
			if err != nil {
				return err
			}
			if tla.TLA_LessThanSymbol(condition0, tla.MakeTLANumber(10)).AsBool() {
				return iface.Goto("ANestedBranch.branchlabel")
			} else {
				return iface.Goto("ANestedBranch.Done")
			}
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANestedBranch.branchlabel",
		Body: func(iface *distsys.ArchetypeInterface) error {
			fmt.Println("starting branching")
			var err error
			_ = err
			i4 := iface.RequireArchetypeResource("ANestedBranch.i")
			j1 := iface.RequireArchetypeResource("ANestedBranch.j")
			k1 := iface.RequireArchetypeResource("ANestedBranch.k")

			val, _ := iface.Read(i4, []tla.TLAValue{})
			fmt.Printf("i: %v\n", val)
			val, _ = iface.Read(j1, []tla.TLAValue{})
			fmt.Printf("j: %v\n", val)
			val, _ = iface.Read(k1, []tla.TLAValue{})
			fmt.Printf("k: %v\n", val)
			return iface.RunBranchConcurrently(
				func(iface *distsys.ArchetypeInterface) error {
					return iface.RunBranchConcurrently(
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead4 tla.TLAValue
							exprRead4, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(i4, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead4, tla.MakeTLANumber(1)))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						},
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead5 tla.TLAValue
							exprRead5, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(i4, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead5, tla.MakeTLANumber(2)))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						},
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead6 tla.TLAValue
							exprRead6, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(i4, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead6, tla.MakeTLANumber(3)))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						},
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead7 tla.TLAValue
							exprRead7, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(i4, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead7, tla.MakeTLANumber(4)))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						})
					// no statements
				},
				func(iface *distsys.ArchetypeInterface) error {
					return iface.RunBranchConcurrently(
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead8 tla.TLAValue
							exprRead8, err = iface.Read(j1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(j1, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead8, tla.MakeTLANumber(5)))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						},
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead9 tla.TLAValue
							exprRead9, err = iface.Read(j1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead10 tla.TLAValue
							exprRead10, err = iface.Read(j1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(j1, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead9, exprRead10))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						})
					// no statements
				},
				func(iface *distsys.ArchetypeInterface) error {
					return iface.RunBranchConcurrently(
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead11 tla.TLAValue
							exprRead11, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead12 tla.TLAValue
							exprRead12, err = iface.Read(k1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(k1, []tla.TLAValue{}, tla.TLA_PlusSymbol(exprRead11, exprRead12))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						},
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead13 tla.TLAValue
							exprRead13, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead14 tla.TLAValue
							exprRead14, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead15 tla.TLAValue
							exprRead15, err = iface.Read(k1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(k1, []tla.TLAValue{}, tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(exprRead13, exprRead14), exprRead15))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						},
						func(iface *distsys.ArchetypeInterface) error {
							var exprRead16 tla.TLAValue
							exprRead16, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead17 tla.TLAValue
							exprRead17, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead18 tla.TLAValue
							exprRead18, err = iface.Read(i4, []tla.TLAValue{})
							if err != nil {
								return err
							}
							var exprRead19 tla.TLAValue
							exprRead19, err = iface.Read(k1, []tla.TLAValue{})
							if err != nil {
								return err
							}
							err = iface.Write(k1, []tla.TLAValue{}, tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(tla.TLA_PlusSymbol(exprRead16, exprRead17), exprRead18), exprRead19))
							if err != nil {
								return err
							}
							return iface.Goto("ANestedBranch.lbl1")
						})
					// no statements
				})
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANestedBranch.lbl1",
		Body: func(iface *distsys.ArchetypeInterface) error {
			var err error
			_ = err
			mark1 := iface.RequireArchetypeResource("ANestedBranch.mark")
			var aRead0 = TheSet(*iface)
			if aRead0.AsSet().Len() == 0 {
				return distsys.ErrCriticalSectionAborted
			}
			var a0 tla.TLAValue = aRead0.SelectElement(iface.NextFairnessCounter("ANestedBranch.lbl1.0", uint(aRead0.AsSet().Len())))
			_ = a0
			var exprRead20 tla.TLAValue
			exprRead20, err = iface.Read(mark1, []tla.TLAValue{})
			if err != nil {
				return err
			}
			err = iface.Write(mark1, []tla.TLAValue{}, tla.TLA_UnionSymbol(exprRead20, tla.MakeTLASet(a0)))
			if err != nil {
				return err
			}
			return iface.Goto("ANestedBranch.loop")
			// no statements
		},
	},
	distsys.MPCalCriticalSection{
		Name: "ANestedBranch.Done",
		Body: func(*distsys.ArchetypeInterface) error {
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
	PreAmble: func(iface *distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ABranch.i", tla.MakeTLANumber(0))
		iface.EnsureArchetypeResourceLocal("ABranch.j", tla.MakeTLANumber(2))
		iface.EnsureArchetypeResourceLocal("ABranch.k", tla.MakeTLANumber(4))
		iface.EnsureArchetypeResourceLocal("ABranch.mark", tla.MakeTLASet())
	},
}

var ANestedBranch = distsys.MPCalArchetype{
	Name:              "ANestedBranch",
	Label:             "ANestedBranch.loop",
	RequiredRefParams: []string{},
	RequiredValParams: []string{},
	JumpTable:         jumpTable,
	ProcTable:         procTable,
	PreAmble: func(iface *distsys.ArchetypeInterface) {
		iface.EnsureArchetypeResourceLocal("ANestedBranch.i", tla.MakeTLANumber(0))
		iface.EnsureArchetypeResourceLocal("ANestedBranch.j", tla.MakeTLANumber(2))
		iface.EnsureArchetypeResourceLocal("ANestedBranch.k", tla.MakeTLANumber(4))
		iface.EnsureArchetypeResourceLocal("ANestedBranch.mark", tla.MakeTLASet())
	},
}
