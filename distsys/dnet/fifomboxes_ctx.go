package dnet

import (
	"encoding/gob"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/channels"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/util"
	"net"
)

type FIFOMailboxReadEffect struct {
	Target *distsys.Resource
}

type fifoMailboxListenerContext struct {
	target, channelResource *distsys.Resource
	listener                net.Listener
	readChannel             chan tla.TLAValue
	listenAddr              string

	channelSize int
}

func MakeFIFOListenerMailboxContext(target *distsys.Resource, listenAddr string, configs ...FIFOListenerMailboxConfig) distsys.EffectContext {
	ctx := &fifoMailboxListenerContext{
		target:          target,
		channelResource: target.Child("readChannel"),
		listenAddr:      listenAddr,

		channelSize: 100,
	}
	for _, config := range configs {
		config(ctx)
	}
	ctx.readChannel = make(chan tla.TLAValue, ctx.channelSize)

	ctx.listen()

	return distsys.MakeEffectContextStack(
		ctx,
		channels.MakeGoInChannelContext(ctx.channelResource, ctx.readChannel))
}

type FIFOListenerMailboxConfig func(ctx *fifoMailboxListenerContext)

func FIFOListenerMailboxSize(size int) FIFOListenerMailboxConfig {
	return func(ctx *fifoMailboxListenerContext) {
		ctx.channelSize = size
	}
}

func (ctx *fifoMailboxListenerContext) BeginEffectInterpreter() distsys.EffectInterpreter {
	return util.MakeTranslationInterpreter(func(effect distsys.Effect) distsys.Effect {
		switch effect := effect.(type) {
		case FIFOMailboxReadEffect:
			if effect.Target != ctx.target {
				return nil
			}
			return channels.GoChannelRead{Target: ctx.channelResource}
		}
		return nil
	}, func(effect distsys.Effect) distsys.Effect {
		return nil
	})
}

func (ctx *fifoMailboxListenerContext) listen() {
	listener, err := net.Listen("tcp", ctx.listenAddr)
	if err != nil {
		panic("???")
	}
	ctx.listener = listener
	go func() {
		for {
			conn, err := listener.Accept()
			if err != nil {
				panic("???")
			}
			go ctx.handleConn(conn)
		}
	}()
}

func (ctx *fifoMailboxListenerContext) handleConn(conn net.Conn) {
	decoder := gob.NewDecoder(conn)
	for {
		var value tla.TLAValue
		err := decoder.Decode(&value)
		if err != nil {
			panic("???")
		}
		ctx.readChannel <- value
	}
}

func (ctx *fifoMailboxListenerContext) Interrupt() {
	_ = ctx.listener.Close() // TODO
}

func (ctx *fifoMailboxListenerContext) Cleanup() error {
	//TODO implement me
	panic("implement me")
}
