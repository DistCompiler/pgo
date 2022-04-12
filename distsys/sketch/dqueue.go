package sketch

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/constants"
	"github.com/UBC-NSS/pgo/distsys/controlflow"
	"github.com/UBC-NSS/pgo/distsys/dnet"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var (
	self           = constants.NewConstant("self", 0)
	Const_PRODUCER = constants.NewConstant("PRODUCER", 0)
)

var (
	Lbl_AConsumer_c  = controlflow.NewLabel("AConsumer.c")
	Lbl_AConsumer_c1 = controlflow.NewLabel("AConsumer.c1")
	Lbl_AConsumer_c2 = controlflow.NewLabel("AConsumer.c2")
)

type Res_AConsumer_net struct {
	Read  func(indices ...tla.TLAValue) distsys.Eval
	Write func(value tla.TLAValue, indices ...tla.TLAValue) distsys.Eval
}

type Res_AConsumer_proc struct {
	Read  func(indices ...tla.TLAValue) distsys.Eval
	Write func(value tla.TLAValue, indices ...tla.TLAValue) distsys.Eval
}

type Args_AConsumer struct {
	R_net  Res_AConsumer_net
	R_proc Res_AConsumer_proc
}

func Eval_AConsumer(args Args_AConsumer) distsys.Eval {
	return controlflow.JumpTable(
		controlflow.CriticalSection{
			Label: Lbl_AConsumer_c,
			Eval: distsys.EvalConst(tla.TLA_TRUE).FlatMap(func(cond tla.TLAValue) distsys.Eval {
				if cond.AsBool() {
					return Lbl_AConsumer_c1.Goto()
				} else {
					return distsys.EvalEffect(distsys.CommitEffect{Done: true})
				}
			}).AndThen(distsys.EvalEffect(distsys.CommitEffect{Done: true})),
		},
		controlflow.CriticalSection{
			Label: Lbl_AConsumer_c1,
			Eval: Const_PRODUCER.Ref().FlatMap(func(v_PRODUCER tla.TLAValue) distsys.Eval {
				return self.Ref().FlatMap(func(v_self tla.TLAValue) distsys.Eval {
					return args.R_net.Write(v_self, v_PRODUCER).AndThen(Lbl_AConsumer_c2.Goto())
				})
			}).AndThen(distsys.EvalEffect(distsys.CommitEffect{Done: true})),
		},
		controlflow.CriticalSection{
			Label: Lbl_AConsumer_c2,
			Eval: self.Ref().FlatMap(func(v_self tla.TLAValue) distsys.Eval {
				return args.R_net.Read(v_self).FlatMap(func(v_read tla.TLAValue) distsys.Eval {
					return args.R_proc.Write(v_read).AndThen(Lbl_AConsumer_c.Goto())
				})
			}).AndThen(distsys.EvalEffect(distsys.CommitEffect{Done: true})),
		})
}

func test() {
	senderCtx := dnet.NewFIFOSenderContext()
	resListener := distsys.NewResource("net")

	ctx := distsys.MakeEffectContextStack(
		constants.MakeConstantsContext(
			self.Bind(distsys.MakeValBinding(tla.MakeTLANumber(2))),
			Const_PRODUCER.Bind(distsys.MakeValBinding(tla.MakeTLANumber(1)))),
		dnet.MakeFIFOListenerMailboxContext(resListener, "localhost:8000"),
		senderCtx)

	eval := Eval_AConsumer(Args_AConsumer{
		R_net: Res_AConsumer_net{
			Read: func(indices ...tla.TLAValue) distsys.Eval {
				if indices[0].AsNumber() == 1 {
					return distsys.EvalEffect(dnet.FIFOMailboxReadEffect{
						Target: resListener,
					})
				} else {
					return distsys.EvalFail(nil) // FIXME
				}
			},
			Write: func(value tla.TLAValue, indices ...tla.TLAValue) distsys.Eval {
				// TODO
				return senderCtx.Send("???", value)
			},
		},
		R_proc: Res_AConsumer_proc{
			Read: func(indices ...tla.TLAValue) distsys.Eval {
				return distsys.EvalFail(nil) // FIXME
			},
			Write: func(value tla.TLAValue, indices ...tla.TLAValue) distsys.Eval {
				panic("TODO")
			},
		},
	})

	err := eval.RunWithContext(ctx)
	if err != nil {
		panic(err)
	}
}
