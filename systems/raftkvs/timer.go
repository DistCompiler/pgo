package raftkvs

import (
	"math/rand"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func TimerResourceMaker(timeout time.Duration, offset time.Duration) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &TimerResource{
			timeout:       timeout,
			timeoutOffset: offset,
		}
	})
}

func getTimeout(duration, offset time.Duration) time.Duration {
	n := rand.Int63n(int64(duration)) + int64(offset)
	return time.Duration(n)
}

// TimerResource is used to implement randomized timeout in the Raft leader
// election. It measures the time since the last call to Read and if it's
// greater than some random timeout, then it returns true; otherwise, returns
// false.
type TimerResource struct {
	distsys.ArchetypeResourceLeafMixin
	timer         *time.Timer
	timeout       time.Duration
	timeoutOffset time.Duration
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
		res.timer = time.NewTimer(getTimeout(res.timeout, res.timeoutOffset))
		return tla.TLA_FALSE, nil
	}
	select {
	case <-res.timer.C:
		res.timer.Reset(getTimeout(res.timeout, res.timeoutOffset))
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
