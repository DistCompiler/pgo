package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"github.com/benbjohnson/immutable"
	"go.uber.org/multierr"
)

// FillFn maps from an index of a given map resource into a distsys.ArchetypeResource for the resource
// intended at that location.
type FillFn func(index tla.TLAValue) distsys.ArchetypeResource

// IncMap is a generic incremental map resource, with hooks to programmatically
// realize child resources during execution.
type IncMap struct {
	distsys.ArchetypeResourceMapMixin
	realizedMap  *immutable.Map
	fillFunction FillFn
	dirtyElems   *immutable.Map
}

var _ distsys.ArchetypeResource = &IncMap{}

func NewIncMap(fillFunction FillFn) *IncMap {
	return &IncMap{
		realizedMap:  immutable.NewMap(tla.TLAValueHasher{}),
		dirtyElems:   immutable.NewMap(tla.TLAValueHasher{}),
		fillFunction: fillFunction,
	}
}

func (res *IncMap) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	if subRes, ok := res.realizedMap.Get(index); ok {
		res.dirtyElems = res.dirtyElems.Set(index, subRes)
		return subRes.(distsys.ArchetypeResource), nil
	}

	subRes := res.fillFunction(index)
	res.realizedMap = res.realizedMap.Set(index, subRes)
	res.dirtyElems = res.dirtyElems.Set(index, subRes)
	return subRes, nil
}

func (res *IncMap) PreCommit() chan error {
	var nonTrivialOps []chan error
	it := res.dirtyElems.Iterator()
	for !it.Done() {
		_, r := it.Next()
		ch := r.(distsys.ArchetypeResource).PreCommit()
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
		res.dirtyElems = immutable.NewMap(tla.TLAValueHasher{})
	}()

	var nonTrivialOps []chan struct{}
	it := res.dirtyElems.Iterator()
	for !it.Done() {
		_, r := it.Next()
		ch := r.(distsys.ArchetypeResource).Commit()
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
		res.dirtyElems = immutable.NewMap(tla.TLAValueHasher{})
	}()

	var nonTrivialOps []chan struct{}
	it := res.dirtyElems.Iterator()
	for !it.Done() {
		_, r := it.Next()
		ch := r.(distsys.ArchetypeResource).Abort()
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
	it := res.dirtyElems.Iterator()
	for !it.Done() {
		_, subRes := it.Next()
		vclock = vclock.Merge(subRes.(distsys.ArchetypeResource).VClockHint(vclock))
	}
	return vclock
}

func (res *IncMap) Close() error {
	var err error
	// Note that we should close all the realized elements, not just the dirty
	// ones.
	it := res.realizedMap.Iterator()
	for !it.Done() {
		_, r := it.Next()
		cerr := r.(distsys.ArchetypeResource).Close()
		err = multierr.Append(err, cerr)
	}
	return err
}
