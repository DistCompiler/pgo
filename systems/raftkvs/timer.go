package raftkvs

import (
	"math/rand"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var LeaderTimeoutConstantDefs = distsys.EnsureMPCalContextConfigs(
	distsys.DefineConstantValue("LeaderTimeoutReset", tla.MakeTLABool(true)),
)

func NewTimerResource(timeout time.Duration, offset time.Duration) distsys.ArchetypeResource {
	return &TimerResource{
		timeout:       timeout,
		timeoutOffset: offset,
	}
}

func getTimeout(duration, offset time.Duration) time.Duration {
	n := rand.Int63n(int64(duration)) + int64(offset)
	return time.Duration(n)
}

// TimerResource is used to implement randomized timeout in the Raft leader
// election. It measures the time since the last call to Read and if it's
// greater than some random timeout, then it returns true; otherwise, returns
// false. Also, it supports timer reset through write calls.
type TimerResource struct {
	distsys.ArchetypeResourceLeafMixin

	lock          sync.Mutex
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
	res.lock.Lock()
	defer res.lock.Unlock()

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
	res.lock.Lock()
	defer res.lock.Unlock()

	if res.timer != nil {
		res.timer.Reset(getTimeout(res.timeout, res.timeoutOffset))
	}
	return nil
}

func (res *TimerResource) Close() error {
	return nil
}
