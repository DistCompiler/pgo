package util

import "github.com/UBC-NSS/pgo/distsys"

type SinglePathInterpreter interface {
	AttemptProgress(effect distsys.Effect) distsys.Effect
	Cleanup(effect distsys.Effect) distsys.Effect
	Clone() SinglePathInterpreter
}

type SinglePathInterpreterAdapter struct {
	interpreters []SinglePathInterpreter
}

var _ distsys.EffectInterpreter = &SinglePathInterpreterAdapter{}

func NewSinglePathInterpreterAdapter(singleInterp SinglePathInterpreter) *SinglePathInterpreterAdapter {
	return &SinglePathInterpreterAdapter{
		interpreters: []SinglePathInterpreter{singleInterp},
	}
}

func (interp *SinglePathInterpreterAdapter) CountPaths() int {
	return len(interp.interpreters)
}

func (interp *SinglePathInterpreterAdapter) GetSinglePathInterpreter(idx int) SinglePathInterpreter {
	return interp.interpreters[idx]
}

func (interp *SinglePathInterpreterAdapter) CloneStateFrom(idx, cloneCount int) {
	baseInterp := interp.interpreters[idx]
	for i := 0; i < cloneCount; i++ {
		interp.interpreters = append(interp.interpreters, baseInterp.Clone())
	}
}

func (interp *SinglePathInterpreterAdapter) AttemptProgress(effects []distsys.Effect) bool {
	progress := false
	for idx, effect := range effects {
		result := interp.interpreters[idx].AttemptProgress(effect)
		if result != nil {
			progress = true
			effects[idx] = result
		}
	}
	return progress
}

func (interp *SinglePathInterpreterAdapter) Cleanup(effects []distsys.Effect) bool {
	progress := false
	for idx, effect := range effects {
		result := interp.interpreters[idx].Cleanup(effect)
		if result != nil {
			progress = true
			effects[idx] = result
		}
	}
	return progress
}
