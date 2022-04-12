package locals

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/util"
)

type Local struct {
	Name string
}

func NewLocal(name string) *Local {
	return &Local{
		Name: name,
	}
}

func (local *Local) Read() distsys.Eval {
	return distsys.EvalEffect(LocalReadEffect{
		Local: local,
	})
}

func (local *Local) Write(value tla.TLAValue) distsys.Eval {
	return distsys.EvalEffect(LocalWriteEffect{
		Local: local,
		Value: value,
	})
}

func (local *Local) Ensure(value tla.TLAValue) distsys.Eval {
	return distsys.EvalEffect(LocalEnsureEffect{
		Local: local,
		Value: value,
	})
}

type LocalReadEffect struct {
	Local *Local
}

type LocalWriteEffect struct {
	Local *Local
	Value tla.TLAValue
}

type LocalEnsureEffect struct {
	Local *Local
	Value tla.TLAValue
}

type localsEffectContext struct {
	data map[*Local]tla.TLAValue
}

type ConfigFn func(ctx *localsEffectContext)

func MakeEffectContext(configs ...ConfigFn) distsys.EffectContext {
	result := &localsEffectContext{
		data: make(map[*Local]tla.TLAValue),
	}
	for _, config := range configs {
		config(result)
	}
	return result
}

func EnsureBinding(local *Local, value tla.TLAValue) ConfigFn {
	return func(ctx *localsEffectContext) {
		ctx.data[local] = value
	}
}

func (ctx *localsEffectContext) BeginEffectInterpreter() distsys.EffectInterpreter {
	interp := &localsEffectInterpreter{
		ctx:  ctx,
		done: false,
	}
	interp.singlePathAdapter = util.NewSinglePathInterpreterAdapter(&localsEffectInterpreterSingle{
		interp:  interp,
		changes: make(map[*Local]tla.TLAValue),
	})
	return interp
}

func (ctx *localsEffectContext) Interrupt() {
	// pass
}

func (ctx *localsEffectContext) Cleanup() error {
	return nil
}

type localsEffectInterpreter struct {
	ctx               *localsEffectContext
	done              bool
	singlePathAdapter *util.SinglePathInterpreterAdapter
}

func (interp *localsEffectInterpreter) CloneStateFrom(idx, cloneCount int) {
	interp.singlePathAdapter.CloneStateFrom(idx, cloneCount)
}

func (interp *localsEffectInterpreter) AttemptProgress(effects []distsys.Effect) bool {
	return interp.singlePathAdapter.AttemptProgress(effects)
}

func (interp *localsEffectInterpreter) Cleanup(effects []distsys.Effect) bool {
	if interp.done {
		return false
	}
	return interp.singlePathAdapter.Cleanup(effects) ||
		util.MatchUnambiguousCommit(effects, func(idx int) bool {
			interp.done = true
			changes := interp.singlePathAdapter.GetSinglePathInterpreter(idx).(*localsEffectInterpreterSingle).changes
			for local, value := range changes {
				interp.ctx.data[local] = value
			}
			return true
		}) ||
		util.MatchAllPathsAbort(effects, func() bool {
			interp.done = true
			return true
		})
}

type localsEffectInterpreterSingle struct {
	interp  *localsEffectInterpreter
	changes map[*Local]tla.TLAValue
}

func (interp *localsEffectInterpreterSingle) AttemptProgress(effect distsys.Effect) distsys.Effect {
	switch effect := effect.(type) {
	case LocalReadEffect:
		if value, ok := interp.changes[effect.Local]; ok {
			return distsys.ResumeEffect{Value: value}
		} else if value, ok := interp.interp.ctx.data[effect.Local]; ok {
			return distsys.ResumeEffect{Value: value}
		} else {
			panic("value not found")
		}
	case LocalWriteEffect:
		if _, ok := interp.changes[effect.Local]; ok {
			// pass
		} else if _, ok := interp.interp.ctx.data[effect.Local]; ok {
			// pass
		} else {
			panic("value not found")
		}
		interp.changes[effect.Local] = effect.Value
		return distsys.ResumeEffect{Value: tla.TLAValue{}}
	case LocalEnsureEffect:
		interp.changes[effect.Local] = effect.Value
		return distsys.ResumeEffect{Value: tla.TLAValue{}}
	}
	return nil
}

func (interp *localsEffectInterpreterSingle) Cleanup(effect distsys.Effect) distsys.Effect {
	return nil
}

func (interp *localsEffectInterpreterSingle) Clone() util.SinglePathInterpreter {
	clonedChanges := make(map[*Local]tla.TLAValue, len(interp.changes))
	for local, value := range interp.changes {
		clonedChanges[local] = value
	}
	return &localsEffectInterpreterSingle{
		interp:  interp.interp,
		changes: clonedChanges,
	}
}
