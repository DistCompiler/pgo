package distsys

import "github.com/UBC-NSS/pgo/distsys/tla"

type Binding interface {
	Ref(args ...Binding) Eval
}

type valBinding struct {
	value tla.TLAValue
}

func MakeValBinding(value tla.TLAValue) Binding {
	return valBinding{value: value}
}

func (binding valBinding) Ref(args ...Binding) Eval {
	if len(args) != 0 {
		panic("???")
	}
	return EvalConst(binding.value)
}

type fnBinding struct {
	fn func(args ...Binding) Eval
}

func MakeFnBinding(fn func(args ...Binding) Eval) Binding {
	return fnBinding{fn: fn}
}

func (binding fnBinding) Ref(args ...Binding) Eval {
	return binding.fn(args...)
}
