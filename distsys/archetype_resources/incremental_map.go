package archetype_resources

import (
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/benbjohnson/immutable"
)

// A generic map resource, with hooks to programmatically realize child resources during execution
// ----------------------------------------------------------------------------------------------------------------

type IncrementalArchetypeMapResource struct {
	distsys.ArchetypeResourceMapMixin
	realizedMap  *immutable.Map
	fillFunction func(index distsys.TLAValue) distsys.ArchetypeResourceMaker
}

var _ distsys.ArchetypeResource = &IncrementalArchetypeMapResource{}

func IncrementalArchetypeMapResourceMaker(fillFunction func(index distsys.TLAValue) distsys.ArchetypeResourceMaker) distsys.ArchetypeResourceMaker {
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
