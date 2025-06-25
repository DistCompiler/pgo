package pbkvs

import (
	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

// TODO

type LeaderElection struct {
	distsys.ArchetypeResourceLeafMixin
}

var _ distsys.ArchetypeResource = &LeaderElection{}

func NewLeaderElection() *LeaderElection {
	return &LeaderElection{}
}

func (res *LeaderElection) Abort(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *LeaderElection) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *LeaderElection) Commit(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *LeaderElection) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	return tla.MakeNumber(1), nil
}

func (res *LeaderElection) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	panic("no write allowed")
}

func (res *LeaderElection) Close() error {
	return nil
}
