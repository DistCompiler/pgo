package dnet

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/util"
	"log"
	"net"
)

type fifoSenderEffect struct {
	ctx   *FIFOSenderContext
	addr  string
	value []byte
}

type FIFOSenderContext struct {
	connections map[string]net.Conn
}

type FIFOSenderConfig func(ctx *FIFOSenderContext)

var _ distsys.EffectContext = &FIFOSenderContext{}

func NewFIFOSenderContext() *FIFOSenderContext {
	return &FIFOSenderContext{
		connections: make(map[string]net.Conn),
	}
}

func (ctx *FIFOSenderContext) invalidateConn(addr string) {
	if conn, ok := ctx.connections[addr]; ok {
		err := conn.Close()
		if err != nil {
			log.Printf("error closing network connection: %v", err)
		}
		delete(ctx.connections, addr)
	}
}

func (ctx *FIFOSenderContext) getValidConn(addr string) net.Conn {
	if conn, ok := ctx.connections[addr]; ok {
		return conn
	} else {
		conn, err := net.Dial("tcp", addr)
		if err != nil {
			log.Printf("error acquiring connection to %s: %v", addr, err)
			return nil
		}
		return conn
	}
}

func (ctx *FIFOSenderContext) Send(addr string, value []byte) distsys.Eval {
	return distsys.EvalEffect(fifoSenderEffect{
		ctx:   ctx,
		addr:  addr,
		value: value,
	})
}

func (ctx *FIFOSenderContext) BeginEffectInterpreter() distsys.EffectInterpreter {
	return util.MakeExclusiveWriteInterpreter(func(effect distsys.Effect) distsys.Effect {
		switch effect := effect.(type) {
		case fifoSenderEffect:
			if effect.ctx != ctx {
				return nil
			}
			conn := ctx.getValidConn(effect.addr)
			if conn == nil {
				return distsys.AbortEffect{}
			}
			// TODO: try to send effect.value to effect.addr.
			// on failure, return distsys.AbortEffect
		}
		return nil
	})
}

func (ctx *FIFOSenderContext) Interrupt() {
	// TODO: do we need this? depends how we handle blocking...
}

func (ctx *FIFOSenderContext) Cleanup() error {
	// TODO: nuke all connections etc
	return nil
}
