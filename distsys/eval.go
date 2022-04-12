package distsys

import "github.com/UBC-NSS/pgo/distsys/tla"

type Eval struct {
	Kind           EvalKind
	Effect         Effect
	PrevEval       *Eval
	ContinuationFn func(value tla.TLAValue) Eval
}

type EvalKind int

const (
	evalEffectK EvalKind = iota
	evalFlatMapK
)

type NestedEvalEffect struct {
	Eval Eval
}

func EvalFail(err error) Eval {
	return EvalEffect(FailEffect{Err: err})
}

func EvalConst(value tla.TLAValue) Eval {
	return EvalEffect(ResumeEffect{value})
}

func EvalEffect(effect Effect) Eval {
	return Eval{
		Kind:   evalEffectK,
		Effect: effect,
	}
}

func EvalSplit(evals ...Eval) Eval {
	return EvalEffect(SplitEffect{evals})
}

func (eval Eval) AndThen(nextEval Eval) Eval {
	return eval.FlatMap(func(_ tla.TLAValue) Eval {
		return nextEval
	})
}

func (eval Eval) Map(fn func(value tla.TLAValue) tla.TLAValue) Eval {
	return eval.FlatMap(func(value tla.TLAValue) Eval {
		return EvalConst(fn(value))
	})
}

func (eval Eval) FlatMap(fn func(value tla.TLAValue) Eval) Eval {
	switch eval.Kind {
	case evalEffectK:
		return Eval{
			Kind:           evalFlatMapK,
			PrevEval:       &eval,
			ContinuationFn: fn,
		}
	case evalFlatMapK:
		return Eval{
			Kind:     evalFlatMapK,
			PrevEval: eval.PrevEval,
			ContinuationFn: func(value tla.TLAValue) Eval {
				return eval.ContinuationFn(value).FlatMap(fn)
			},
		}
	default:
		panic("???")
	}
}

func (eval Eval) runOneStep(effectInterpreter EffectInterpreter) bool {
	type Continuation func(value tla.TLAValue) Eval

	effects := []Effect{ResumeEffect{Value: tla.TLAValue{}}}
	continuations := []Continuation{func(_ tla.TLAValue) Eval {
		return eval
	}}

	for {
		madeProgress := false

		for idx := 0; idx < len(effects); idx++ {
			switch effect := effects[idx].(type) {
			case SplitEffect:
				madeProgress = true
				cloneCount := len(effect.Evals) - 1
				effectInterpreter.CloneStateFrom(idx, cloneCount)
				continuationToClone := continuations[idx]
				for evalIdx, innerEval := range effect.Evals {
					effect := NestedEvalEffect{Eval: innerEval}
					if evalIdx == 0 {
						effects[idx] = effect
					} else {
						effects = append(effects, effect)
						continuations = append(continuations, continuationToClone)
					}
				}
				// jump back one element, so we evenly do work on the first element we just introduced
				idx--
			case ResumeEffect, NestedEvalEffect:
				madeProgress = true
				if continuations[idx] == nil {
					panic("???")
				}
				var eval Eval
				switch effect := effect.(type) {
				case ResumeEffect:
					eval = continuations[idx](effect.Value)
				case NestedEvalEffect:
					eval = effect.Eval
				default:
					panic("???")
				}

				var continuation Continuation
			flatMap:
				for {
					switch eval.Kind {
					case evalEffectK:
						effects[idx] = eval.Effect
						continuations[idx] = continuation
						break flatMap
					case evalFlatMapK:
						if continuation == nil {
							continuation = eval.ContinuationFn
						} else {
							outerContinuation := continuation
							innerContinuation := eval.ContinuationFn
							continuation = func(value tla.TLAValue) Eval {
								return innerContinuation(value).FlatMap(outerContinuation)
							}
						}
						eval = *eval.PrevEval
					default:
						panic("???")
					}
				}
			}
		}

		if effectInterpreter.AttemptProgress(effects) {
			madeProgress = true
		}

		if !madeProgress {
			cleanupRemaining := true
			for cleanupRemaining {
				cleanupRemaining = effectInterpreter.Cleanup(effects)
			}
			break
		}
	}

	commitOrDoneCount := 0
	abortCount := 0
	shouldContinue := true

	for _, effect := range effects {
		switch effect := effect.(type) {
		case CommitEffect:
			commitOrDoneCount++
			if effect.Done {
				shouldContinue = false
			}
		case AbortEffect:
			abortCount++
		}
	}

	if commitOrDoneCount+abortCount != len(effects) {
		panic("unhandled effects remain")
	}

	if commitOrDoneCount > 1 {
		panic("tried to commit multiple paths")
	}

	return shouldContinue
}

func (eval Eval) RunWithContext(ctx EffectContext) error {
	for eval.runOneStep(ctx.BeginEffectInterpreter()) {
		// pass
	}
	return ctx.Cleanup()
}
