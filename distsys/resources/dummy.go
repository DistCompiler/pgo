package resources

import (
	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
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

func (res *Dummy) Abort(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *Dummy) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *Dummy) Commit(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *Dummy) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	return res.value, nil
}

func (res *Dummy) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	return nil
}

func (res *Dummy) Index(iface distsys.ArchetypeInterface, index tla.Value) (distsys.ArchetypeResource, error) {
	return res, nil
}

func (res *Dummy) Close() error {
	return nil
}
