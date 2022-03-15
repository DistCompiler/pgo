package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"go.uber.org/multierr"
)

// FillFn maps from an index of a given map resource into a distsys.ArchetypeResourceMaker for the resource
// intended at that location. It is assumed that this mapping is stable, in that, for the same index, a maker for
// a resource with the same behaviour will be returned, no matter when the function is called.
type FillFn func(index tla.TLAValue) distsys.ArchetypeResourceMaker

// IncrementalMap is a generic map resource, with hooks to programmatically
// realize child resources during execution.
type IncrementalMap struct {
	distsys.ArchetypeResourceMapMixin
	realizedMap  *immutable.Map
	fillFunction FillFn
	dirtyElems   *immutable.Map
}

var _ distsys.ArchetypeResource = &IncrementalMap{}

func IncrementalMapMaker(fillFunction FillFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &IncrementalMap{
				realizedMap: immutable.NewMap(tla.TLAValueHasher{}),
				dirtyElems:  immutable.NewMap(tla.TLAValueHasher{}),
			}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*IncrementalMap)
			r.fillFunction = fillFunction
		},
	}
}

func (res *IncrementalMap) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	maker := res.fillFunction(index)
	if subRes, ok := res.realizedMap.Get(index); ok {
		r := subRes.(distsys.ArchetypeResource)
		maker.Configure(r)
		res.dirtyElems = res.dirtyElems.Set(index, subRes)
		return subRes.(distsys.ArchetypeResource), nil
	}

	subRes := maker.Make()
	maker.Configure(subRes)
	res.realizedMap = res.realizedMap.Set(index, subRes)
	res.dirtyElems = res.dirtyElems.Set(index, subRes)
	return subRes, nil
}

func (res *IncrementalMap) PreCommit() chan error {
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

func (res *IncrementalMap) Commit() chan struct{} {
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

func (res *IncrementalMap) Abort() chan struct{} {
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

func (res *IncrementalMap) Close() error {
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

func (res *IncrementalMap) ForkState() (distsys.ArchetypeResource, error) {
	//TODO implement me
	panic("implement me")
}

func (res *IncrementalMap) LinkState() error {
	//TODO implement me
	panic("implement me")
}
