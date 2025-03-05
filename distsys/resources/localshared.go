package resources

import (
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

const lockAcquireTimeout = 50 * time.Millisecond

type LocalSharedManagerOption func(*LocalSharedManager)

func WithLocalSharedResourceTimeout(t time.Duration) LocalSharedManagerOption {
	return func(res *LocalSharedManager) {
		res.timeout = t
	}
}

// LocalSharedManager contains the shared resources and its lock.
type LocalSharedManager struct {
	res     *distsys.LocalArchetypeResource
	lockCh  chan struct{} // see https://stackoverflow.com/a/54488475
	timeout time.Duration
}

func NewLocalSharedManager(value tla.Value, opts ...LocalSharedManagerOption) *LocalSharedManager {
	res := &LocalSharedManager{
		res:     distsys.NewLocalArchetypeResource(value),
		lockCh:  make(chan struct{}, 1),
		timeout: lockAcquireTimeout,
	}
	for _, opt := range opts {
		opt(res)
	}
	return res
}

func (sv *LocalSharedManager) acquireWithTimeout(iface distsys.ArchetypeInterface) bool {
	select {
	case sv.lockCh <- struct{}{}:
		sv.res.SetIFace(iface)
		return true
	case <-time.After(sv.timeout):
		return false
	}
}

func (sv *LocalSharedManager) acquire(iface distsys.ArchetypeInterface) {
	sv.lockCh <- struct{}{}
	sv.res.SetIFace(iface)
}

func (sv *LocalSharedManager) release() {
	sv.res.SetIFace(distsys.ArchetypeInterface{})
	<-sv.lockCh
}

// MakeLocalShared is method that creates a localShared resources. To share a resource
// between different archetypes, you should use this method to build one ArchetypeResource
// per archetype with which you want to share the underlying resource.
func (sv *LocalSharedManager) MakeLocalShared() Persistable {
	return &localShared{
		sharedRes: sv,
	}
}

// localShared is a resource that represents the shared resource in an
// archetype. Each archetype has access to a different instance of localShared
// resource but all localShared instances have the same sharedRes pointer.
type localShared struct {
	// sharedRes is a pointer to the resource that is being shared.
	sharedRes *LocalSharedManager
	hasLock   bool

	iface distsys.ArchetypeInterface
}

func assumeNil(ch chan struct{}) {
	if ch != nil {
		panic("channel was not nil")
	}
}

func (res *localShared) Abort() chan struct{} {
	if res.hasLock {
		res.hasLock = false
		resCh := res.sharedRes.res.Abort()
		assumeNil(resCh)
		res.sharedRes.release()
	}
	return nil
}

func (res *localShared) PreCommit() chan error {
	return nil
}

func (res *localShared) Commit() chan struct{} {
	if res.hasLock {
		res.hasLock = false
		resCh := res.sharedRes.res.Commit()
		assumeNil(resCh)
		res.sharedRes.release()
	}
	return nil
}

func (res *localShared) tryEnsureLock() error {
	if !res.hasLock {
		if !res.sharedRes.acquireWithTimeout(res.iface) {
			return distsys.ErrCriticalSectionAborted
		}
		res.hasLock = true
	}
	return nil
}

func (res *localShared) ReadValue() (tla.Value, error) {
	if err := res.tryEnsureLock(); err != nil {
		return tla.Value{}, err
	}
	return res.sharedRes.res.ReadValue()
}

func (res *localShared) WriteValue(value tla.Value) error {
	if err := res.tryEnsureLock(); err != nil {
		return err
	}
	return res.sharedRes.res.WriteValue(value)
}

func (res *localShared) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	if err := res.tryEnsureLock(); err != nil {
		return nil, err
	}
	out, err := res.sharedRes.res.Index(index)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func (res *localShared) SetIFace(iface distsys.ArchetypeInterface) {
	res.iface = iface
}

func (res *localShared) Close() error {
	return nil
}

func (res *localShared) GetState() ([]byte, error) {
	if !res.hasLock {
		res.sharedRes.acquire(res.iface)
		defer res.sharedRes.release()
	}
	return res.sharedRes.res.GetState()
}
