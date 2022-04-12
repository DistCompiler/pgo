package util

import "github.com/UBC-NSS/pgo/distsys"

type exclusiveWriteInterpreter struct {
	fn              func(effect distsys.Effect) distsys.Effect
	singlePath      *SinglePathInterpreterAdapter
	requiredCommits int
}

func MakeExclusiveWriteInterpreter(fn func(effect distsys.Effect) distsys.Effect) distsys.EffectInterpreter {
	interp := &exclusiveWriteInterpreter{
		fn: fn,
	}
	interp.singlePath = NewSinglePathInterpreterAdapter(&exclusiveWriteInterpreterSingle{
		interp:          interp,
		requiredCommits: 0,
	})
	return interp
}

func (interp *exclusiveWriteInterpreter) CloneStateFrom(idx, cloneCount int) {
	interp.singlePath.CloneStateFrom(idx, cloneCount)
}

func (interp *exclusiveWriteInterpreter) assertRequiredCommits(effects []distsys.Effect) bool {
	badCount := 0
	okCommitCount := 0
	for idx, effect := range effects {
		switch effect.(type) {
		case distsys.AbortEffect:
			single := interp.singlePath.GetSinglePathInterpreter(idx).(*exclusiveWriteInterpreterSingle)
			if single.requiredCommits > 0 {
				badCount++
			}
		case distsys.CommitEffect:
			single := interp.singlePath.GetSinglePathInterpreter(idx).(*exclusiveWriteInterpreterSingle)
			if single.requiredCommits == interp.requiredCommits {
				okCommitCount++
			} else {
				// this is ok, because it is invalid to have more than one commit.
				// we will eventually see which commit "lives", and if it's ok we're good. if not, we'll crash then.
			}
		}
	}
	if badCount > 0 {
		if okCommitCount > 0 {
			// this is ok, we have a commit that captures all necessary I/O ops
			return false
		} else {
			panic("not ok: we have required commits, but all paths from them abort")
		}
	}
	return false
}

func (interp *exclusiveWriteInterpreter) AttemptProgress(effects []distsys.Effect) bool {
	progress := false
	for idx, effect := range effects {
		result := interp.fn(effect)
		if result != nil {
			progress = true
			effects[idx] = result
			if _, ok := result.(distsys.AbortEffect); ok {
				// directly aborting necessarily means this path _was not_ the exclusive write we were looking for
				// so, skip all the exclusivity stuff and keep going
				continue
			}
			single := interp.singlePath.GetSinglePathInterpreter(idx).(*exclusiveWriteInterpreterSingle)
			interp.requiredCommits++
			single.requiredCommits++
			for siblingIdx := range effects {
				if siblingIdx != idx {
					effects[siblingIdx] = distsys.AbortEffect{}
				}
			}
		}
	}
	return interp.assertRequiredCommits(effects) || progress
}

func (interp *exclusiveWriteInterpreter) Cleanup(effects []distsys.Effect) bool {
	return interp.assertRequiredCommits(effects)
}

type exclusiveWriteInterpreterSingle struct {
	interp          *exclusiveWriteInterpreter
	requiredCommits int
}

func (interp *exclusiveWriteInterpreterSingle) AttemptProgress(effect distsys.Effect) distsys.Effect {
	return nil
}

func (interp *exclusiveWriteInterpreterSingle) Cleanup(effect distsys.Effect) distsys.Effect {
	return nil
}

func (interp *exclusiveWriteInterpreterSingle) Clone() SinglePathInterpreter {
	return &exclusiveWriteInterpreterSingle{
		interp:          interp.interp,
		requiredCommits: interp.requiredCommits,
	}
}
