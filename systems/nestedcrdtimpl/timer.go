package nestedcrdtimpl

import (
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

func NewTimer(d time.Duration) distsys.ArchetypeResource {
	return &TimerResource{duration: d}
}

type TimerResource struct {
	distsys.ArchetypeResourceLeafMixin
	timer *time.Timer

	duration time.Duration
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

func (res *TimerResource) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	if res.timer == nil {
		res.timer = time.NewTimer(res.duration)
		return tla.ModuleFALSE, nil
	}
	select {
	case <-res.timer.C:
		res.timer.Reset(res.duration)
		return tla.ModuleTRUE, nil
	default:
		return tla.ModuleFALSE, nil
	}
}

func (res *TimerResource) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	panic("write to timer resource is not allowed")
}

func (res *TimerResource) Close() error {
	return nil
}
