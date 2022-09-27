package raftkvs

import (
	"math/rand"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func TimerResourceMaker() distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &TimerResource{}
	})
}

func getTimeout() time.Duration {
	n := rand.Intn(150) + 150
	return time.Duration(n) * time.Millisecond
}

// TimerResource is used to implement randomized timeout in the Raft leader
// election. It measures the time since the last call to Read and if it's
// greater than some random timeout, then it returns true; otherwise, returns
// false.
type TimerResource struct {
	distsys.ArchetypeResourceLeafMixin
	timer *time.Timer
}

func (res *TimerResource) Abort() chan struct{} {
	return nil
}

func (res *TimerResource) PreCommit() chan error {
	return nil
}

func (res *TimerResource) Commit() chan struct{} {
	return nil
}

func (res *TimerResource) ReadValue() (tla.TLAValue, error) {
	if res.timer == nil {
		res.timer = time.NewTimer(getTimeout())
		return tla.TLA_FALSE, nil
	}
	select {
	case <-res.timer.C:
		res.timer.Reset(getTimeout())
		return tla.TLA_TRUE, nil
	default:
		return tla.TLA_FALSE, nil
	}
}

func (res *TimerResource) WriteValue(value tla.TLAValue) error {
	panic("write to timer resource is not allowed")
}

func (res *TimerResource) Close() error {
	return nil
}
