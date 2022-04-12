package constants

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/util"
)

type Constant struct {
	Name  string
	Arity int
}

func NewConstant(name string, arity int) *Constant {
	return &Constant{
		Name:  name,
		Arity: arity,
	}
}

func (c *Constant) Ref(bindings ...distsys.Binding) distsys.Eval {
	return distsys.EvalEffect(ConstantEffect{
		Constant: c,
		Bindings: bindings,
	})
}

func (c *Constant) Bind(binding distsys.Binding) ConstantsConfig {
	return func(ctx *constantsContext) {
		ctx.bindings[c] = binding
	}
}

type ConstantEffect struct {
	Constant *Constant
	Bindings []distsys.Binding
}

type constantsContext struct {
	bindings map[*Constant]distsys.Binding
}

type ConstantsConfig func(ctx *constantsContext)

func MakeConstantsContext(configs ...ConstantsConfig) distsys.EffectContext {
	ctx := &constantsContext{
		bindings: make(map[*Constant]distsys.Binding),
	}
	for _, config := range configs {
		config(ctx)
	}
	return ctx
}

func (ctx *constantsContext) BeginEffectInterpreter() distsys.EffectInterpreter {
	return util.MakeTranslationInterpreter(func(effect distsys.Effect) distsys.Effect {
		switch effect := effect.(type) {
		case ConstantEffect:
			bind, ok := ctx.bindings[effect.Constant]
			if !ok {
				panic("???")
			}
			return bind.Ref(effect.Bindings...)
		}
		return nil
	}, func(effect distsys.Effect) distsys.Effect {
		return nil
	})
}

func (ctx *constantsContext) Interrupt() {
	// pass
}

func (ctx *constantsContext) Cleanup() error {
	return nil
}
