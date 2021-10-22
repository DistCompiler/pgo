package pbkvs

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// TODO

type LeaderElection struct {
	distsys.ArchetypeResourceLeafMixin
}

func LeaderElectionMaker() distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &LeaderElection{}
	})
}

func (res *LeaderElection) Abort() chan struct{} {
	return nil
}

func (res *LeaderElection) PreCommit() chan error {
	return nil
}

func (res *LeaderElection) Commit() chan struct{} {
	return nil
}

func (res *LeaderElection) ReadValue() (tla.TLAValue, error) {
	return tla.MakeTLANumber(1), nil
}

func (res *LeaderElection) WriteValue(value tla.TLAValue) error {
	panic("no write allowed")
}

func (res *LeaderElection) Close() error {
	return nil
}
