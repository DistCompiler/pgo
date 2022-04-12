package util

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"reflect"
)

type AsyncEffect struct {
	selectCase    reflect.SelectCase
	shouldDefault func() bool
	doneFn        func(value interface{})
}

func (asyncEffect AsyncEffect) WithShouldDefaultFn(fn func() bool) AsyncEffect {
	asyncEffect.shouldDefault = fn
	return asyncEffect
}

func (asyncEffect AsyncEffect) WithDoneFn(fn func(value tla.TLAValue)) AsyncEffect {
	asyncEffect.doneFn = func(value interface{}) {
		fn(value.(tla.TLAValue))
	}
	return asyncEffect
}

func MakeAsyncReadEffect(channel chan tla.TLAValue) AsyncEffect {
	return AsyncEffect{
		selectCase: reflect.SelectCase{
			Dir:  reflect.SelectRecv,
			Chan: reflect.ValueOf(channel),
		},
		shouldDefault: func() bool {
			return false
		},
		doneFn: func(value interface{}) {},
	}
}

type asyncCtx struct {
	interp      asyncInterpreter
	interruptCh chan struct{}
}

func MakeAsyncCtx() distsys.EffectContext {
	ctx := &asyncCtx{
		interruptCh: make(chan struct{}, 1),
	}
	ctx.interp.ctx = ctx
	return ctx
}

func (ctx *asyncCtx) BeginEffectInterpreter() distsys.EffectInterpreter {
	return &ctx.interp
}

func (ctx *asyncCtx) Interrupt() {
	select {
	case ctx.interruptCh <- struct{}{}: // ok
	default: // also ok
	}
}

func (ctx *asyncCtx) Cleanup() error {
	return nil
}

type asyncInterpreter struct {
	ctx *asyncCtx
}

func (interp *asyncInterpreter) CloneStateFrom(_, _ int) {
	// pass
}

func (interp *asyncInterpreter) AttemptProgress(effects []distsys.Effect) bool {
	type branchInfo struct {
		effectIdx int
		effect    AsyncEffect
	}
	var branches []branchInfo
	hasUnknownEffect := false
	for idx, effect := range effects {
		switch effect := effect.(type) {
		case distsys.AbortEffect, distsys.CommitEffect:
			// pass
		case AsyncEffect:
			if effect.shouldDefault() {
				effects[idx] = distsys.ResumeEffect{Value: tla.TLAValue{}}
				hasUnknownEffect = true
				continue
			}
			branches = append(branches, branchInfo{
				effectIdx: idx,
				effect:    effect,
			})
		default:
			hasUnknownEffect = true
		}
	}
	if len(branches) == 0 {
		return false
	}
	var cases []reflect.SelectCase
	for _, branch := range branches {
		cases = append(cases, branch.effect.selectCase)
	}
	if hasUnknownEffect {
		cases = append(cases, reflect.SelectCase{Dir: reflect.SelectDefault})
	} else {
		cases = append(cases, reflect.SelectCase{Dir: reflect.SelectRecv, Chan: reflect.ValueOf(interp.ctx.interruptCh)})
	}
	chosenIdx, recv, _ := reflect.Select(cases)
	if chosenIdx == len(branches) {
		if hasUnknownEffect {
			return true // we defaulted, nothing to see here... but we did try to do something
		} else {
			return false // we got killed by interrupt
		}
	}
	branch := branches[chosenIdx]
	recvValue := recv.Interface().(tla.TLAValue)
	branch.effect.doneFn(recvValue)
	effects[branch.effectIdx] = distsys.ResumeEffect{Value: tla.TLAValue{}}
	return true
}

func (interp *asyncInterpreter) Cleanup(effects []distsys.Effect) bool {
	return false
}
