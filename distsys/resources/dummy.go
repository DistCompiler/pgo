package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func DummyResourceMaker() distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &Dummy{}
	})
}

type Dummy struct{}

func (res *Dummy) Abort() chan struct{} {
	return nil
}

func (res *Dummy) PreCommit() chan error {
	return nil
}

func (res *Dummy) Commit() chan struct{} {
	return nil
}

func (res *Dummy) ReadValue() (tla.TLAValue, error) {
	return tla.TLAValue{}, nil
}

func (res *Dummy) WriteValue(value tla.TLAValue) error {
	return nil
}

func (res *Dummy) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	return res, nil
}

func (res *Dummy) Close() error {
	return nil
}

func (res *Dummy) ForkState() (distsys.ArchetypeResource, error) {
	//TODO implement me
	panic("implement me")
}
