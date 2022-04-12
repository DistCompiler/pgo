package channels

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/util"
)

type GoChannelRead struct {
	Target *distsys.Resource
}

type goInChannelContext struct {
	target        *distsys.Resource
	channel       chan tla.TLAValue
	msgsToReceive []tla.TLAValue
}

func MakeGoInChannelContext(target *distsys.Resource, channel chan tla.TLAValue) distsys.EffectContext {
	return &goInChannelContext{
		target:  target,
		channel: channel,
	}
}

func (ctx *goInChannelContext) BeginEffectInterpreter() distsys.EffectInterpreter {
	interp := &goInChannelInterpreter{
		ctx: ctx,
	}
	interp.singlePathAdapter = util.NewSinglePathInterpreterAdapter(&goInChannelInterpSinglePath{
		interp:        interp,
		msgsToReceive: append([]tla.TLAValue(nil), ctx.msgsToReceive...),
	})
	return interp
}

func (ctx *goInChannelContext) Interrupt() {
	// pass
}

func (ctx *goInChannelContext) Cleanup() error {
	return nil
}

type goInChannelInterpreter struct {
	ctx               *goInChannelContext
	done              bool
	singlePathAdapter *util.SinglePathInterpreterAdapter
	receivedMsgs      []tla.TLAValue
}

func (interp *goInChannelInterpreter) CloneStateFrom(idx, cloneCount int) {
	interp.singlePathAdapter.CloneStateFrom(idx, cloneCount)
}

func (interp *goInChannelInterpreter) AttemptProgress(effects []distsys.Effect) bool {
	return interp.singlePathAdapter.AttemptProgress(effects)
}

func (interp *goInChannelInterpreter) Cleanup(effects []distsys.Effect) bool {
	return interp.singlePathAdapter.Cleanup(effects) ||
		util.MatchAllPathsAbort(effects, func() bool {
			if interp.done {
				return false
			}
			interp.ctx.msgsToReceive = append(interp.ctx.msgsToReceive, interp.receivedMsgs...)
			interp.done = true
			return true
		}) ||
		util.MatchUnambiguousCommit(effects, func(idx int) bool {
			if interp.done {
				return false
			}
			interp.ctx.msgsToReceive = interp.singlePathAdapter.GetSinglePathInterpreter(idx).(*goInChannelInterpSinglePath).msgsToReceive
			interp.done = true
			return true
		})
}

type goInChannelInterpSinglePath struct {
	interp        *goInChannelInterpreter
	msgsToReceive []tla.TLAValue
}

func (interp *goInChannelInterpSinglePath) AttemptProgress(effect distsys.Effect) distsys.Effect {
	switch effect := effect.(type) {
	case GoChannelRead:
		if effect.Target != interp.interp.ctx.target {
			return nil
		}
		if len(interp.msgsToReceive) != 0 {
			value := interp.msgsToReceive[0]
			interp.msgsToReceive[0] = tla.TLAValue{}
			interp.msgsToReceive = interp.msgsToReceive[1:]
			return distsys.ResumeEffect{Value: value}
		}
		return distsys.NestedEvalEffect{
			Eval: distsys.EvalEffect(util.MakeAsyncReadEffect(interp.interp.ctx.channel).WithShouldDefaultFn(func() bool {
				return len(interp.msgsToReceive) > 0
			}).WithDoneFn(func(value tla.TLAValue) {
				for idx := 0; idx < interp.interp.singlePathAdapter.CountPaths(); idx++ {
					sibling := interp.interp.singlePathAdapter.GetSinglePathInterpreter(idx).(*goInChannelInterpSinglePath)
					sibling.msgsToReceive = append(sibling.msgsToReceive, value)
				}
			})).FlatMap(func(_ tla.TLAValue) distsys.Eval {
				// ASSUME: read was successful, somehow, and the result was pushed onto our local msgsToReceive queue
				result := interp.msgsToReceive[0]
				interp.msgsToReceive[0] = tla.TLAValue{}
				interp.msgsToReceive = interp.msgsToReceive[1:]
				return distsys.EvalConst(result)
			}),
		}
	}
	return nil
}

func (interp *goInChannelInterpSinglePath) Cleanup(effect distsys.Effect) distsys.Effect {
	return nil
}

func (interp *goInChannelInterpSinglePath) Clone() util.SinglePathInterpreter {
	return &goInChannelInterpSinglePath{
		interp:        interp.interp,
		msgsToReceive: append([]tla.TLAValue(nil), interp.msgsToReceive...),
	}
}
