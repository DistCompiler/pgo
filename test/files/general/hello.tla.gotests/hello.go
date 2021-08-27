package hello

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
}

func HELLO(constants Constants) distsys.TLAValue {
	return distsys.NewTLAString("hello")
}

func AHello(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, out distsys.ArchetypeResourceHandle) error {
	ctx.ReportEvent(distsys.ArchetypeStarted)
	defer func() {
		ctx.ReportEvent(distsys.ArchetypeFinished)
	}()
	var err error
	// label tags
	const (
		InitLabelTag = iota
		lblLabelTag
		DoneLabelTag
	)
	programCounter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag)))

	for {
		select {
		case <-ctx.Done():
			err = distsys.ErrContextClosed
		default:
		}
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
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(lblLabelTag))
			if err != nil {
				continue
			}
		case lblLabelTag:
			err = ctx.Write(out, []distsys.TLAValue{}, func() distsys.TLAValue {
				return HELLO(constants)
			}())
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag))
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
