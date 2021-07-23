package dqueue

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
)

var _ = new(fmt.Stringer)  // unconditionally prevent go compiler from reporting unused fmt import
var _ = distsys.TLAValue{} // same, for distsys

type Constants struct {
	BUFFER_SIZE   distsys.TLAValue
	NUM_CONSUMERS distsys.TLAValue
	PRODUCER      distsys.TLAValue
}

func NUM_NODES(constants Constants) distsys.TLAValue {
	return distsys.TLA_PlusSymbol(constants.NUM_CONSUMERS, distsys.NewTLANumber(1))
}

func AConsumer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net distsys.ArchetypeResourceHandle, proc distsys.ArchetypeResourceHandle) error {
	var err error
	// label tags
	const (
		InitLabelTag = iota
		cLabelTag
		c1LabelTag
		c2LabelTag
		DoneLabelTag
	)
	programCounter := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag)))

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
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(cLabelTag))
			if err != nil {
				continue
			}
		case cLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(c1LabelTag))
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
		case c1LabelTag:
			err = ctx.Write(net, []distsys.TLAValue{constants.PRODUCER}, self)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(c2LabelTag))
			if err != nil {
				continue
			}
			err = ctx.Commit()
			if err != nil {
				continue
			}
		case c2LabelTag:
			var exprRead distsys.TLAValue
			exprRead, err = ctx.Read(net, []distsys.TLAValue{self})
			if err != nil {
				continue
			}
			err = ctx.Write(proc, []distsys.TLAValue{}, exprRead)
			if err != nil {
				continue
			}
			err = ctx.Write(programCounter, []distsys.TLAValue{}, distsys.NewTLANumber(cLabelTag))
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

func AProducer(ctx *distsys.MPCalContext, self distsys.TLAValue, constants Constants, net0 distsys.ArchetypeResourceHandle, s distsys.ArchetypeResourceHandle) error {
	var err0 error
	// label tags
	const (
		InitLabelTag0 = iota
		pLabelTag
		p1LabelTag
		p2LabelTag
		DoneLabelTag0
	)
	programCounter0 := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.NewTLANumber(InitLabelTag0)))
	requester := ctx.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker(distsys.TLAValue{}))
	_ = requester

	for {
		if err0 != nil {
			if err0 == distsys.ErrCriticalSectionAborted {
				ctx.Abort()
				err0 = nil
			} else {
				return err0
			}
		}
		var labelTag0 distsys.TLAValue
		labelTag0, err0 = ctx.Read(programCounter0, []distsys.TLAValue{})
		if err0 != nil {
			return err0
		}
		switch labelTag0.AsNumber() {
		case InitLabelTag0:
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(pLabelTag))
			if err0 != nil {
				continue
			}
		case pLabelTag:
			if distsys.TLA_TRUE.AsBool() {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(p1LabelTag))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			} else {
				err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(DoneLabelTag0))
				if err0 != nil {
					continue
				}
				err0 = ctx.Commit()
				if err0 != nil {
					continue
				}
			}
			// no statements
		case p1LabelTag:
			var exprRead0 distsys.TLAValue
			exprRead0, err0 = ctx.Read(net0, []distsys.TLAValue{self})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(requester, []distsys.TLAValue{}, exprRead0)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(p2LabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case p2LabelTag:
			var exprRead1 distsys.TLAValue
			exprRead1, err0 = ctx.Read(s, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			var indexRead distsys.TLAValue
			indexRead, err0 = ctx.Read(requester, []distsys.TLAValue{})
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(net0, []distsys.TLAValue{indexRead}, exprRead1)
			if err0 != nil {
				continue
			}
			err0 = ctx.Write(programCounter0, []distsys.TLAValue{}, distsys.NewTLANumber(pLabelTag))
			if err0 != nil {
				continue
			}
			err0 = ctx.Commit()
			if err0 != nil {
				continue
			}
		case DoneLabelTag0:
			return nil
		default:
			return fmt.Errorf("invalid program counter %v", labelTag0)
		}
	}
}
