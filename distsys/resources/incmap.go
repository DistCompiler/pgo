package resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/benbjohnson/immutable"
	"log"
)

// A generic map resource, with hooks to programmatically realize child resources during execution
// ----------------------------------------------------------------------------------------------------------------

// FillFn maps from an index of a given map resource into a distsys.ArchetypeResourceMaker for the resource
// intended at that location. It is assumed that this mapping is stable, in that, for the same index, a maker for
// a resource with the same behaviour will be returned, no matter when the function is called.
type FillFn func(index distsys.TLAValue) distsys.ArchetypeResourceMaker

type IncrementalArchetypeMapResource struct {
	distsys.ArchetypeResourceMapMixin
	realizedMap  *immutable.Map
	fillFunction FillFn
}

var _ distsys.ArchetypeResource = &IncrementalArchetypeMapResource{}

func IncrementalArchetypeMapResourceMaker(fillFunction FillFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &IncrementalArchetypeMapResource{
				realizedMap: immutable.NewMap(distsys.TLAValueHasher{}),
			}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*IncrementalArchetypeMapResource)
			r.fillFunction = fillFunction
		},
	}
}

func (res *IncrementalArchetypeMapResource) Index(index distsys.TLAValue) (distsys.ArchetypeResource, error) {
	maker := res.fillFunction(index)
	if subRes, ok := res.realizedMap.Get(index); ok {
		r := subRes.(distsys.ArchetypeResource)
		maker.Configure(r)
		return subRes.(distsys.ArchetypeResource), nil
	}

	subRes := maker.Make()
	maker.Configure(subRes)
	res.realizedMap = res.realizedMap.Set(index, subRes)
	return subRes, nil
}

func (res *IncrementalArchetypeMapResource) PreCommit() chan error {
	var nonTrivialOps []chan error
	it := res.realizedMap.Iterator()
	for !it.Done() {
		idx, r := it.Next()
		ch := r.(distsys.ArchetypeResource).PreCommit()
		if ch != nil {
			log.Println("non-trivial incmap pre-commit from index", idx.(distsys.TLAValue))
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

func (res *IncrementalArchetypeMapResource) Commit() chan struct{} {
	var nonTrivialOps []chan struct{}
	it := res.realizedMap.Iterator()
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

func (res *IncrementalArchetypeMapResource) Abort() chan struct{} {
	var nonTrivialOps []chan struct{}
	it := res.realizedMap.Iterator()
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
