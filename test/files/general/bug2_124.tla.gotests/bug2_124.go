package bug2

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	NUM_NODES   distsys.TLAValue
	BUFFER_SIZE distsys.TLAValue
}

func AEchoServer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		InitLabelTag = iota
		serverLoopLabelTag
		rcvMsgLabelTag
		sndMsgLabelTag
		DoneLabelTag
	)
	programCounter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag)))
	msg := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = msg

	for {
		if err != nil {
			if err == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err = nil
			} else {
				return err
			}
		}
		var labelTag distsys.TLAValue
		labelTag, err = ctx.Read(programCounter, []distsys.TLAValue{})
		if err != nil {
			return err
		}
		switch labelTag.AsNumber() {
		case InitLabelTag:
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(serverLoopLabelTag))
			if err != nil {
				continue
			}
		case serverLoopLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(rcvMsgLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			} else {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
				if err != nil {
					continue
				}
				err = ctx.Commit()
				if err != nil {
					continue
				}
			}
			// no statements
		case rcvMsgLabelTag:
			var exprRead distsys.TLAValue
			exprRead, err = ctx.Read(net, []distsys.TLAValue{distsys.NewTLATuple(self, distsys.NewTLANumber(1))})
			if err != nil {
				continue
			}
			err = ctx.Write(msg, []distsys.TLAValue{}, exprRead)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(sndMsgLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case sndMsgLabelTag:
			var exprRead0 distsys.TLAValue
			exprRead0, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead1 distsys.TLAValue
			exprRead1, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var exprRead2 distsys.TLAValue
			exprRead2, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead distsys.TLAValue
			indexRead, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			var indexRead0 distsys.TLAValue
			indexRead0, err = ctx.Read(msg, []distsys.TLAValue{})
			if err != nil {
				continue
			}
			err = ctx.Write(net, []distsys.TLAValue{distsys.NewTLATuple(indexRead.ApplyFunction(distsys.NewTLAString("from")), indexRead0.ApplyFunction(distsys.NewTLAString("typ")))}, distsys.NewTLARecord([]distsys.TLARecordField{
				{distsys.NewTLAString("from"), self},
				{distsys.NewTLAString("to"), exprRead0.ApplyFunction(distsys.NewTLAString("from"))},
				{distsys.NewTLAString("body"), exprRead1.ApplyFunction(distsys.NewTLAString("body"))},
				{distsys.NewTLAString("typ"), exprRead2.ApplyFunction(distsys.NewTLAString("typ"))},
			}))
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(serverLoopLabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case DoneLabelTag:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag)
		}
	}
}
