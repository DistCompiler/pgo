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

// sharedResource contains the shared resources and its lock.
type sharedResource struct {
	res *distsys.LocalArchetypeResource
	// sem acts as a read-write lock with timeout support. Also, it supports
	// upgrading a read-lock to a write-lock.
	sem     *semaphore.Weighted
	timeout time.Duration

	// TODO: add vector clock
}

func (sv *sharedResource) acquireWithTimeout(n int64) error {
	ctx, cancel := context.WithTimeout(context.Background(), sv.timeout)
	defer cancel() // release resources if Acquire finishes before timeout
	return sv.sem.Acquire(ctx, n)
}

func (sv *sharedResource) acquire(n int64) error {
	return sv.sem.Acquire(context.Background(), n)
}

func (sv *sharedResource) release(n int64) {
	sv.sem.Release(n)
}

type LocalSharedOption func(*LocalShared)

func WithLocalSharedTimeout(t time.Duration) LocalSharedOption {
	return func(res *LocalShared) {
		res.sharedRes.timeout = t
	}
}

// LocalSharedMaker is function that creates a LocalShared resources.
type LocalSharedMaker func() *LocalShared

// NewLocalSharedMaker creates a new LocalSharedMaker. To share a resource
// between different archetypes, you should make a LocalSharedMaker and use that
// LocalSharedMaker instance to create the shared resource in each archetype.
func NewLocalSharedMaker(value tla.TLAValue, opts ...LocalSharedOption) LocalSharedMaker {
	localRes := distsys.NewLocalArchetypeResource(value)
	sharedRes := &sharedResource{
		res:     localRes,
		sem:     semaphore.NewWeighted(maxSemSize),
		timeout: lockAcquireTimeout,
	}
	return func() *LocalShared {
		res := &LocalShared{
			sharedRes: sharedRes,
			acquired:  0,
		}
		for _, opt := range opts {
			opt(res)
		}
		return res
	}
}

// LocalShared is a resource that represents the shared resource in an
// archetype. Each archetype has access to a different instance of LocalShared
// resource but all LocalShared instances have the same sharedRes pointer.
type LocalShared struct {
	// sharedRes is a pointer to the resource that is being shared.
	sharedRes *sharedResource
	// acquired is value that this resource has acquired from sharedRes's
	// semaphore.
	// acquired = 0 means no access.
	// 0 < acquired < maxSemSize means read access.
	// acquired = maxSemSize means write access.
	// Sum of the acquired values in all LocalShared instances that point to
	// the same sharedRes is always less than or equal to maxSemSize.
	acquired int64
}

func (res *LocalShared) Abort() chan struct{} {
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

func (res *LocalShared) PreCommit() chan error {
	return nil
}

func (res *LocalShared) Commit() chan struct{} {
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

func (res *LocalShared) ReadValue() (tla.TLAValue, error) {
	if res.acquired == 0 {
		err := res.sharedRes.acquireWithTimeout(1)
		if err != nil {
			return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
		}
		res.acquired = 1
	}
	return res.sharedRes.res.ReadValue()
}

func (res *LocalShared) WriteValue(value tla.TLAValue) error {
	if res.acquired < maxSemSize {
		err := res.sharedRes.acquireWithTimeout(maxSemSize - res.acquired)
		if err != nil {
			return distsys.ErrCriticalSectionAborted
		}
		res.acquired = maxSemSize
	}
	return res.sharedRes.res.WriteValue(value)
}

func (res *LocalShared) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	return res.sharedRes.res.Index(index)
}

func (res *LocalShared) Close() error {
	return nil
}

func (res *LocalShared) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}

func (res *LocalShared) GetState() ([]byte, error) {
	if res.acquired == 0 {
		err := res.sharedRes.acquire(1)
		if err != nil {
			return nil, err
		}
		res.acquired = 1
	}
	return res.sharedRes.res.GetState()
}
