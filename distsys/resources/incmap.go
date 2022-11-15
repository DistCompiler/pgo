package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"go.uber.org/multierr"
)

// FillFn maps from an index of a given map resource into a distsys.ArchetypeResource for the resource
// intended at that location.
type FillFn func(index tla.Value) distsys.ArchetypeResource

// IncMap is a generic incremental map resource, with hooks to programmatically
// realize child resources during execution.
type IncMap struct {
	distsys.ArchetypeResourceMapMixin
	realizedMap  *hashmap.HashMap[distsys.ArchetypeResource]
	fillFunction FillFn
	dirtyElems   *hashmap.HashMap[distsys.ArchetypeResource]
}

var _ distsys.ArchetypeResource = &IncMap{}

func NewIncMap(fillFunction FillFn) *IncMap {
	return &IncMap{
		realizedMap:  hashmap.New[distsys.ArchetypeResource](),
		dirtyElems:   hashmap.New[distsys.ArchetypeResource](),
		fillFunction: fillFunction,
	}
}

func (res *IncMap) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	if subRes, ok := res.realizedMap.Get(index); ok {
		res.dirtyElems.Set(index, subRes)
		return subRes, nil
	}

	subRes := res.fillFunction(index)
	res.realizedMap.Set(index, subRes)
	res.dirtyElems.Set(index, subRes)
	return subRes, nil
}

func (res *IncMap) PreCommit() chan error {
	var nonTrivialOps []chan error
	for _, idx := range res.dirtyElems.Keys() {
		r, _ := res.dirtyElems.Get(idx)
		ch := r.PreCommit()
		if ch != nil {
			nonTrivialOps = append(nonTrivialOps, ch)
		}
	}

	if len(nonTrivialOps) != 0 {
		doneCh := make(chan error)
		go func() {
			var err error
			for _, ch := range nonTrivialOps {
				err = <-ch
				if err != nil {
					break
				}
			}
			doneCh <- err
		}()
		return doneCh
	}

	return nil
}

func (res *IncMap) Commit() chan struct{} {
	defer func() {
		res.dirtyElems.Clear()
	}()

	var nonTrivialOps []chan struct{}
	for _, idx := range res.dirtyElems.Keys() {
		r, _ := res.dirtyElems.Get(idx)
		ch := r.Commit()
		if ch != nil {
			nonTrivialOps = append(nonTrivialOps, ch)
		}
	}

	if len(nonTrivialOps) != 0 {
		doneCh := make(chan struct{})
		go func() {
			for _, ch := range nonTrivialOps {
				<-ch
			}
			doneCh <- struct{}{}
		}()
		return doneCh
	}

	return nil
}

func (res *IncMap) Abort() chan struct{} {
	defer func() {
		res.dirtyElems.Clear()
	}()

	var nonTrivialOps []chan struct{}
	for _, idx := range res.dirtyElems.Keys() {
		r, _ := res.dirtyElems.Get(idx)
		ch := r.Abort()
		if ch != nil {
			nonTrivialOps = append(nonTrivialOps, ch)
		}
	}

	if len(nonTrivialOps) != 0 {
		doneCh := make(chan struct{})
		go func() {
			for _, ch := range nonTrivialOps {
				<-ch
			}
			doneCh <- struct{}{}
		}()
		return doneCh
	}

	return nil
}

func (res *IncMap) VClockHint(vclock trace.VClock) trace.VClock {
	for _, idx := range res.dirtyElems.Keys() {
		subRes, _ := res.dirtyElems.Get(idx)
		vclock = vclock.Merge(subRes.VClockHint(vclock))
	}
	return vclock
}

func (res *IncMap) Close() error {
	var err error
	// Note that we should close all the realized elements, not just the dirty
	// ones.
	for _, idx := range res.realizedMap.Keys() {
		r, _ := res.realizedMap.Get(idx)
		cerr := r.Close()
		err = multierr.Append(err, cerr)
	}
	return err
}
