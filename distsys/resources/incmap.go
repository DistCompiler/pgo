package resources

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"go.uber.org/multierr"
	"sync"
)

// FillFn maps from an index of a given map resource into a distsys.ArchetypeResourceMaker for the resource
// intended at that location. It is assumed that this mapping is stable, in that, for the same index, a maker for
// a resource with the same behaviour will be returned, no matter when the function is called.
type FillFn func(index tla.TLAValue) distsys.ArchetypeResourceMaker

// IncrementalMap is a generic map resource, with hooks to programmatically
// realize child resources during execution.
type IncrementalMap struct {
	lock         sync.Mutex // lock is needed for when we lazily fill realizedMap, potentially from multiple goroutines
	realizedMap  *immutable.Map
	fillFunction FillFn
}

var _ distsys.ArchetypeResource = &IncrementalMap{}

func IncrementalMapMaker(fillFunction FillFn) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &IncrementalMap{
				realizedMap: immutable.NewMap(tla.TLAValueHasher{}),
			}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*IncrementalMap)
			r.fillFunction = fillFunction
		},
	}
}

func (res *IncrementalMap) FreshState() distsys.ArchetypeResourceState {
	return &incrementalMapState{
		parent: res,
		states: immutable.NewMap(tla.TLAValueHasher{}),
	}
}

func (res *IncrementalMap) Close() error {
	it := res.realizedMap.Iterator()
	var err error
	for !it.Done() {
		_, subResource := it.Next()
		err = multierr.Append(err, subResource.(distsys.ArchetypeResource).Close())
	}
	return err
}

type incrementalMapState struct {
	distsys.ArchetypeResourceMapMixin
	parent *IncrementalMap
	states *immutable.Map // mapping from tla.TLAValue to distsys.ArchetypeResourceState
}

func (state *incrementalMapState) Abort() []chan struct{} {
	var aborts []chan struct{}
	it := state.states.Iterator()
	for !it.Done() {
		_, subState := it.Next()
		aborts = append(aborts, subState.(distsys.ArchetypeResourceState).Abort()...)
	}
	return aborts
}

func (state *incrementalMapState) PreCommit() []chan error {
	var preCommits []chan error
	it := state.states.Iterator()
	for !it.Done() {
		_, subState := it.Next()
		preCommits = append(preCommits, subState.(distsys.ArchetypeResourceState).PreCommit()...)
	}
	return preCommits
}

func (state *incrementalMapState) Commit() []chan struct{} {
	var commits []chan struct{}
	it := state.states.Iterator()
	for !it.Done() {
		_, subState := it.Next()
		commits = append(commits, subState.(distsys.ArchetypeResourceState).Commit()...)
	}
	return commits
}

func (state *incrementalMapState) Index(index tla.TLAValue) (distsys.ArchetypeResourceComponent, error) {
	if _, ok := state.states.Get(index); !ok {
		// lock here, not inside the else case, because the check and update might interfere with each other otherwise
		state.parent.lock.Lock()
		defer state.parent.lock.Unlock()
		var resource distsys.ArchetypeResource
		if resourceI, ok := state.parent.realizedMap.Get(index); ok {
			resource = resourceI.(distsys.ArchetypeResource)
		} else {
			// lazy fill the realizedMap on demand
			maker := state.parent.fillFunction(index)
			resource = maker.Make()
			maker.Configure(resource)
			state.parent.realizedMap = state.parent.realizedMap.Set(index, resource)
		}
		state.states = state.states.Set(index, resource.FreshState())
	}
	return &incrementalMapComponent{
		state: state,
		index: index,
	}, nil
}

func (state *incrementalMapState) ForkState() distsys.ArchetypeResourceState {
	forkedStatesBuilder := immutable.NewMapBuilder(tla.TLAValueHasher{})
	it := state.states.Iterator()
	for !it.Done() {
		index, subState := it.Next()
		forkedStatesBuilder.Set(index, subState.(distsys.ArchetypeResourceState).ForkState())
	}
	return &incrementalMapState{
		parent: state.parent,
		states: forkedStatesBuilder.Map(),
	}
}

type incrementalMapComponent struct {
	state *incrementalMapState
	index tla.TLAValue
}

func (comp *incrementalMapComponent) getState() distsys.ArchetypeResourceState {
	state, ok := comp.state.states.Get(comp.index)
	if !ok {
		panic(fmt.Errorf("resource not found at index %v, should be unreachable", comp.index))
	}
	return state.(distsys.ArchetypeResourceState)
}

func (comp *incrementalMapComponent) Index(index tla.TLAValue) (distsys.ArchetypeResourceComponent, error) {
	return comp.getState().Index(index)
}

func (comp *incrementalMapComponent) ReadValue(iface *distsys.ArchetypeInterface) (tla.TLAValue, error) {
	return comp.getState().ReadValue(iface)
}

func (comp *incrementalMapComponent) WriteValue(iface *distsys.ArchetypeInterface, value tla.TLAValue) error {
	return comp.getState().WriteValue(iface, value)
}
