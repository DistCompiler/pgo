package resources

import (
	"context"
	"time"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"golang.org/x/sync/semaphore"
)

const maxSemSize = 10000
const lockAcquireTimeout = 50 * time.Millisecond

type LocalSharedManagerOption func(*LocalSharedManager)

func WithLocalSharedResourceTimeout(t time.Duration) LocalSharedManagerOption {
	return func(res *LocalSharedManager) {
		res.timeout = t
	}
}

// LocalSharedManager contains the shared resources and its lock.
type LocalSharedManager struct {
	res *distsys.LocalArchetypeResource
	// sem acts as a read-write lock with timeout support. Also, it supports
	// upgrading a read-lock to a write-lock.
	sem     *semaphore.Weighted
	timeout time.Duration

	// TODO: add vector clock
}

func NewLocalSharedManager(value tla.Value, opts ...LocalSharedManagerOption) *LocalSharedManager {
	res := &LocalSharedManager{
		res:     distsys.NewLocalArchetypeResource(value),
		sem:     semaphore.NewWeighted(maxSemSize),
		timeout: lockAcquireTimeout,
	}
	for _, opt := range opts {
		opt(res)
	}
	return res
}

func (sv *LocalSharedManager) acquireWithTimeout(n int64) error {
	ctx, cancel := context.WithTimeout(context.Background(), sv.timeout)
	defer cancel() // release resources if Acquire finishes before timeout
	return sv.sem.Acquire(ctx, n)
}

func (sv *LocalSharedManager) acquire(n int64) error {
	return sv.sem.Acquire(context.Background(), n)
}

func (sv *LocalSharedManager) release(n int64) {
	sv.sem.Release(n)
}

// MakeLocalShared is method that creates a localShared resources. To share a resource
// between different archetypes, you should use this method to build one ArchetypeResource
// per archetype with which you want to share the underlying resource.
func (sv *LocalSharedManager) MakeLocalShared() Persistable {
	return &localShared{
		sharedRes: sv,
		acquired:  0,
	}
}

// localShared is a resource that represents the shared resource in an
// archetype. Each archetype has access to a different instance of localShared
// resource but all localShared instances have the same sharedRes pointer.
type localShared struct {
	// sharedRes is a pointer to the resource that is being shared.
	sharedRes *LocalSharedManager
	// acquired is value that this resource has acquired from sharedRes's
	// semaphore.
	// acquired = 0 means no access.
	// 0 < acquired < maxSemSize means read access.
	// acquired = maxSemSize means write access.
	// Sum of the acquired values in all localShared instances that point to
	// the same sharedRes is always less than or equal to maxSemSize.
	acquired int64
}

func (res *localShared) Abort() chan struct{} {
	if res.acquired == maxSemSize {
		resCh := res.sharedRes.res.Abort()
		if resCh != nil {
			<-resCh
		}
	}
	if res.acquired > 0 {
		res.sharedRes.release(res.acquired)
		res.acquired = 0
	}
	return nil
}

func (res *localShared) PreCommit() chan error {
	return nil
}

func (res *localShared) Commit() chan struct{} {
	if res.acquired == maxSemSize {
		resCh := res.sharedRes.res.Commit()
		if resCh != nil {
			<-resCh
		}
	}
	if res.acquired > 0 {
		res.sharedRes.release(res.acquired)
		res.acquired = 0
	}
	return nil
}

func (res *localShared) ReadValue() (tla.Value, error) {
	if res.acquired == 0 {
		err := res.sharedRes.acquireWithTimeout(1)
		if err != nil {
			return tla.Value{}, distsys.ErrCriticalSectionAborted
		}
		res.acquired = 1
	}
	return res.sharedRes.res.ReadValue()
}

func (res *localShared) WriteValue(value tla.Value) error {
	if res.acquired < maxSemSize {
		err := res.sharedRes.acquireWithTimeout(maxSemSize - res.acquired)
		if err != nil {
			return distsys.ErrCriticalSectionAborted
		}
		res.acquired = maxSemSize
	}
	return res.sharedRes.res.WriteValue(value)
}

func (res *localShared) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	return res.sharedRes.res.Index(index)
}

func (res *localShared) Close() error {
	return nil
}

func (res *localShared) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}

func (res *localShared) GetState() ([]byte, error) {
	if res.acquired == 0 {
		err := res.sharedRes.acquire(1)
		if err != nil {
			return nil, err
		}
		res.acquired = 1
	}
	return res.sharedRes.res.GetState()
}
