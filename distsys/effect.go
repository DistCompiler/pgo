package distsys

import (
	"github.com/UBC-NSS/pgo/distsys/tla"
	"go.uber.org/multierr"
)

type EffectContext interface {
	BeginEffectInterpreter() EffectInterpreter
	Interrupt()
	Cleanup() error
}

type EffectInterpreter interface {
	CloneStateFrom(idx, cloneCount int)
	AttemptProgress(effects []Effect) bool
	Cleanup(effects []Effect) bool
}

type Effect interface{}

type AbortEffect struct{}

type CommitEffect struct {
	Done bool
}

type ResumeEffect struct {
	Value tla.TLAValue
}

type SplitEffect struct {
	Evals []Eval
}

type FailEffect struct {
	Err error
}

type effectContextStack struct {
	effectContexts              []EffectContext
	effectInterpreterStackCache []EffectInterpreter
}

func MakeEffectContextStack(effectContexts ...EffectContext) EffectContext {
	return &effectContextStack{
		effectContexts: effectContexts,
	}
}

func (ctxStack *effectContextStack) BeginEffectInterpreter() EffectInterpreter {
	cachedSlice := ctxStack.effectInterpreterStackCache
	for _, ctx := range ctxStack.effectContexts {
		cachedSlice = append(cachedSlice, ctx.BeginEffectInterpreter())
	}
	return &effectInterpreterStack{
		effectInterpreters: cachedSlice,
	}
}

func (ctxStack *effectContextStack) Interrupt() {
	for _, ctx := range ctxStack.effectContexts {
		ctx.Interrupt()
	}
}

func (ctxStack *effectContextStack) Cleanup() error {
	var err error
	for _, ctx := range ctxStack.effectContexts {
		err = multierr.Append(err, ctx.Cleanup())
	}
	return err
}

type effectInterpreterStack struct {
	effectInterpreters []EffectInterpreter
}

func (interpStack *effectInterpreterStack) CloneStateFrom(idx, cloneCount int) {
	for _, interp := range interpStack.effectInterpreters {
		interp.CloneStateFrom(idx, cloneCount)
	}
}

func (interpStack *effectInterpreterStack) AttemptProgress(effects []Effect) bool {
	result := false
	for _, interp := range interpStack.effectInterpreters {
		result = result || interp.AttemptProgress(effects)
	}
	return result
}

func (interpStack *effectInterpreterStack) Cleanup(effects []Effect) bool {
	result := false
	for _, interp := range interpStack.effectInterpreters {
		result = result || interp.Cleanup(effects)
	}
	return result
}
