package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/trace"
)

type DummyOption func(d *Dummy)

func WithDummyValue(v tla.Value) DummyOption {
	return func(d *Dummy) {
		d.value = v
	}
}

func NewDummy(opts ...DummyOption) *Dummy {
	d := &Dummy{}
	for _, opt := range opts {
		opt(d)
	}
	return d
}

type Dummy struct {
	value tla.Value
}

func (res *Dummy) Abort() chan struct{} {
	return nil
}

func (res *Dummy) PreCommit() chan error {
	return nil
}

func (res *Dummy) Commit() chan struct{} {
	return nil
}

func (res *Dummy) ReadValue() (tla.Value, error) {
	return res.value, nil
}

func (res *Dummy) WriteValue(value tla.Value) error {
	return nil
}

func (res *Dummy) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	return res, nil
}

func (res *Dummy) Close() error {
	return nil
}

func (res *Dummy) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}
