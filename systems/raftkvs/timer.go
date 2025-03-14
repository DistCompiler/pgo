package raftkvs

import (
	"math/rand"
	"sync"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

var LeaderTimeoutConstantDefs = distsys.EnsureMPCalContextConfigs(
	distsys.DefineConstantValue("LeaderTimeoutReset", tla.MakeBool(true)),
)

func NewTimerResource(timeout time.Duration, offset time.Duration) distsys.ArchetypeResource {
	return &TimerResource{
		closeCh:       make(chan struct{}),
		resetCh:       make(chan struct{}),
		timeout:       timeout,
		timeoutOffset: offset,
	}
}

func getTimeout(duration, offset time.Duration) time.Duration {
	n := int64(duration) + rand.Int63n(int64(offset))
	return time.Duration(n)
}

// TimerResource is used to implement randomized timeout in the Raft leader
// election. It measures the time since the last call to Read and if it's
// greater than some random timeout, then it returns true; otherwise, returns
// false. Also, it supports timer reset through write calls.
type TimerResource struct {
	distsys.ArchetypeResourceLeafMixin

	lock          sync.Mutex
	closeCh       chan struct{}
	resetCh       chan struct{}
	timeout       time.Duration
	timeoutOffset time.Duration
}

func (res *TimerResource) getCloseCh() chan struct{} {
	res.lock.Lock()
	defer res.lock.Unlock()
	return res.closeCh
}

func (res *TimerResource) Abort(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *TimerResource) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *TimerResource) Commit(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *TimerResource) ReadValue(iface distsys.ArchetypeInterface) (tla.Value, error) {
	timeout := getTimeout(res.timeout, res.timeoutOffset)
	select {
	case <-res.getCloseCh():
		return tla.ModuleFALSE, nil
	case <-res.resetCh:
		return tla.ModuleFALSE, nil
	case <-time.After(timeout):
		return tla.ModuleTRUE, nil
	}
}

func (res *TimerResource) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	select {
	case res.resetCh <- struct{}{}:
	default:
	}
	return nil
}

func (res *TimerResource) Close() error {
	res.lock.Lock()
	defer res.lock.Unlock()
	if res.closeCh != nil {
		close(res.closeCh)
		res.closeCh = nil
	}
	return nil
}
