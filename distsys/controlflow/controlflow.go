package controlflow

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/locals"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type Label struct {
	Name string
}

func NewLabel(name string) *Label {
	return &Label{
		Name: name,
	}
}

func (label *Label) Goto() distsys.Eval {
	return PC.Write(tla.MakeTLAString(label.Name))
}

type Procedure struct {
	Name      string
	Params    []*locals.Local
	Preamble  distsys.Eval
	InitLabel *Label
}

func (proc *Procedure) Call() distsys.Eval {
	panic("???")
}

type CriticalSection struct {
	Label *Label
	Eval  distsys.Eval
}

var (
	PC    = locals.NewLocal(".pc")
	Stack = locals.NewLocal(".stack")
)

func JumpTable(criticalSections ...CriticalSection) distsys.Eval {
	table := make(map[string]distsys.Eval, len(criticalSections))
	for _, criticalSection := range criticalSections {
		table[criticalSection.Label.Name] = criticalSection.Eval
	}

	return PC.Read().FlatMap(func(pc tla.TLAValue) distsys.Eval {
		if eval, ok := table[pc.AsString()]; ok {
			return eval
		} else {
			panic("critical section not found")
		}
	})
}
