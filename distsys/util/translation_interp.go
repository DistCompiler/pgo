package util

import "github.com/UBC-NSS/pgo/distsys"

type translationInterpreter struct {
	attemptProgress func(effect distsys.Effect) distsys.Effect
	cleanup         func(effect distsys.Effect) distsys.Effect
}

func MakeTranslationInterpreter(attemptProgress func(effect distsys.Effect) distsys.Effect, cleanup func(effect distsys.Effect) distsys.Effect) distsys.EffectInterpreter {
	return NewSinglePathInterpreterAdapter(&translationInterpreter{
		attemptProgress: attemptProgress,
		cleanup:         cleanup,
	})
}

func (interp *translationInterpreter) AttemptProgress(effect distsys.Effect) distsys.Effect {
	return interp.attemptProgress(effect)
}

func (interp *translationInterpreter) Cleanup(effect distsys.Effect) distsys.Effect {
	return interp.cleanup(effect)
}

func (interp *translationInterpreter) Clone() SinglePathInterpreter {
	return interp
}
