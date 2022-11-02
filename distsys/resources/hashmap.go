package resources

import (
	"fmt"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"go.uber.org/multierr"
)

type HashMap struct {
	distsys.ArchetypeResourceMapMixin
	resourceMap *hashmap.HashMap[distsys.ArchetypeResource]
	dirtyElems  *hashmap.HashMap[distsys.ArchetypeResource]
}

func NewHashMap(resourceMap *hashmap.HashMap[distsys.ArchetypeResource]) *HashMap {
	return &HashMap{
		resourceMap: resourceMap,
		dirtyElems:  hashmap.New[distsys.ArchetypeResource](),
	}
}

func (res *HashMap) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	subRes, ok := res.resourceMap.Get(index)
	if !ok {
		panic(fmt.Sprintf("index %v doesn't exist in resource map", index))
	}
	res.dirtyElems.Set(index, subRes)
	return subRes, nil
}

func (res *HashMap) PreCommit() chan error {
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

func (res *HashMap) Commit() chan struct{} {
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

func (res *HashMap) Abort() chan struct{} {
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

func (res *HashMap) Close() error {
	var err error
	for _, idx := range res.resourceMap.Keys() {
		r, _ := res.resourceMap.Get(idx)
		cerr := r.Close()
		err = multierr.Append(err, cerr)
	}
	return err
}
