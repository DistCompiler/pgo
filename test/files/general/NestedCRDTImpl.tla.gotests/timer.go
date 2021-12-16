package nestedcrdtimpl

import (
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func TimerResourceMaker(d time.Duration) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &TimerResource{duration: d}
	})
}

type TimerResource struct {
	distsys.ArchetypeResourceLeafMixin
	timer *time.Timer

	duration time.Duration
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
		res.timer = time.NewTimer(res.duration)
		return tla.TLA_FALSE, nil
	}
	select {
	case <-res.timer.C:
		res.timer.Reset(res.duration)
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
