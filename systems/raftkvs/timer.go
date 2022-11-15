package raftkvs

import (
	"math/rand"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var LeaderTimeoutConstantDefs = distsys.EnsureMPCalContextConfigs(
	distsys.DefineConstantValue("LeaderTimeoutReset", tla.MakeBool(true)),
)

func NewTimerResource(timeout time.Duration, offset time.Duration) distsys.ArchetypeResource {
	return &TimerResource{
		closeCh:       make(chan struct{}, 1),
		resetCh:       make(chan struct{}, 1),
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

	closeCh       chan struct{}
	resetCh       chan struct{}
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

func (res *TimerResource) ReadValue() (tla.Value, error) {
	if res.timer == nil {
		res.timer = time.NewTimer(getTimeout(res.timeout, res.timeoutOffset))
	}
	for {
		select {
		case <-res.closeCh:
			return tla.ModuleFALSE, nil
		case <-res.resetCh:
			if !res.timer.Stop() {
				<-res.timer.C
			}
			res.timer.Reset(getTimeout(res.timeout, res.timeoutOffset))
		case <-res.timer.C:
			res.timer.Reset(getTimeout(res.timeout, res.timeoutOffset))
			return tla.ModuleTRUE, nil
		}
	}
}

func (res *TimerResource) WriteValue(value tla.Value) error {
	select {
	case res.resetCh <- struct{}{}:
	default:
	}
	return nil
}

func (res *TimerResource) Close() error {
	select {
	case res.closeCh <- struct{}{}:
	default:
	}
	return nil
}
