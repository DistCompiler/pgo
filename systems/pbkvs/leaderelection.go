package pbkvs

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// TODO

type LeaderElection struct {
	distsys.ArchetypeResourceLeafMixin
}

func NewLeaderElection() *LeaderElection {
	return &LeaderElection{}
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

func (res *LeaderElection) ReadValue() (tla.Value, error) {
	return tla.MakeNumber(1), nil
}

func (res *LeaderElection) WriteValue(value tla.Value) error {
	panic("no write allowed")
}

func (res *LeaderElection) Close() error {
	return nil
}
