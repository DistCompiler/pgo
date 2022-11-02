package resources

import (
	"errors"
	"fmt"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"go.uber.org/multierr"
)

// ErrNestedArchetypeProtocol signifies that a nested archetype misbehaved while we were trying to use it as an archetype implementation
var ErrNestedArchetypeProtocol = errors.New("error during interaction with nested archetype")

// ErrNestedArchetypeSanity signifies that some internal sanity check failed regarding buffer / channel state. intended for use during panic
var ErrNestedArchetypeSanity = errors.New("internal sanity check failed")

// ErrNestedArchetypeStopped signifies that an archetype contained within a nestedArchetype has stopped, so the resource operation can no longer safely proceed
var ErrNestedArchetypeStopped = errors.New("a nested archetype has stopped, preventing this resource API request from being serviced")

const (
	// nestedArchetypeTimeout is how long a nested archetype will wait on an operation before giving up
	// this is arbitrary and hardcoded, and should be made configurable later.
	nestedArchetypeTimeout = 100 * time.Millisecond
)

var nestedArchetypeReadReq = tla.MakeString("read_req")
var nestedArchetypeWriteReq = tla.MakeString("write_req")
var nestedArchetypePreCommitReq = tla.MakeString("precommit_req")
var nestedArchetypeAbortReq = tla.MakeString("abort_req")
var nestedArchetypeCommitReq = tla.MakeString("commit_req")

var nestedArchetypeReadAck = tla.MakeString("read_ack")
var nestedArchetypeWriteAck = tla.MakeString("write_ack")
var nestedArchetypePreCommitAck = tla.MakeString("precommit_ack")
var nestedArchetypeAbortAck = tla.MakeString("abort_ack")
var nestedArchetypeCommitAck = tla.MakeString("commit_ack")

var nestedArchetypeAborted = tla.MakeString("aborted")

// NestedArchetypeConstantDefs provides a quick way to include correct definitions for all the boilerplate constants
// a resource implementation will always require.
//
// These definitions would satisfy roughly the following TLA+, binding each constant to its own name:
//
//   CONSTANTS READ_REQ, WRITE_REQ, ABORT_REQ, PRECOMMIT_REQ, COMMIT_REQ
//   CONSTANTS READ_ACK, WRITE_ACK, ABORT_ACK, PRECOMMIT_ACK, COMMIT_ACK
//
var NestedArchetypeConstantDefs = distsys.EnsureMPCalContextConfigs(
	// req tpe
	distsys.DefineConstantValue("READ_REQ", nestedArchetypeReadReq),
	distsys.DefineConstantValue("WRITE_REQ", nestedArchetypeWriteReq),
	distsys.DefineConstantValue("ABORT_REQ", nestedArchetypeAbortReq),
	distsys.DefineConstantValue("PRECOMMIT_REQ", nestedArchetypePreCommitReq),
	distsys.DefineConstantValue("COMMIT_REQ", nestedArchetypeCommitReq),
	// ack tpe
	distsys.DefineConstantValue("READ_ACK", nestedArchetypeReadAck),
	distsys.DefineConstantValue("WRITE_ACK", nestedArchetypeWriteAck),
	distsys.DefineConstantValue("ABORT_ACK", nestedArchetypeAbortAck),
	distsys.DefineConstantValue("PRECOMMIT_ACK", nestedArchetypePreCommitAck),
	distsys.DefineConstantValue("COMMIT_ACK", nestedArchetypeCommitAck),
	// aborted notification tpe
	distsys.DefineConstantValue("ABORTED", nestedArchetypeAborted),
)

type nestedArchetypeConstantsT struct {
	tpe   tla.Value
	value tla.Value
}

var nestedArchetypeConstants = nestedArchetypeConstantsT{
	tpe:   tla.MakeString("tpe"),
	value: tla.MakeString("value"),
}

type nestedArchetype struct {
	distsys.ArchetypeResourceLeafMixin

	// nestedCtxs holds all nested archetypes managed by this resource. see API docs for rationale notes
	nestedCtxs []*distsys.MPCalContext
	// ctxErrCh will receive the return values of ctx.Run, for all ctx in nestedCtxs.
	ctxErrCh chan error
	// ctxHasStopped will be closed if any non-nil error has been returned by the Run function of any nested context
	// ctxHasStoppedLock manages concurrent closing of ctxHasStopped from multiple nested context goroutines
	ctxHasStoppedLock sync.Mutex
	ctxHasStopped     chan struct{}

	// sendCh and receiveCh are the inputs to and outputs from the nested MPCal system, respectively
	sendCh    chan tla.Value
	receiveCh chan tla.Value

	// apiErrCh and apiStructCh are pre-allocated channels which will be returned by the resource API functions
	apiErrCh    chan error
	apiStructCh chan struct{}

	// requestTimer performs timeouts for requests to the nested archetype system, and is cached here to avoid
	// recreating a timer on every request
	requestTimer *time.Timer
}

var _ distsys.ArchetypeResource = new(nestedArchetype)

// NewNested adapts a specific form of MPCal archetype to the resource interface, allowing resources to be
// implemented and model checked in MPCal themselves.
//
// The argument fn should map a pair of input and output channels to the inputs and outputs of one or more nested archetype
// instances, which, aside from these channels, should be configured just as free-standing archetypes would be.
// This resource will then take over those contexts' lifecycles, calling Run on then, forwarding errors to the
// containing context's execution, and ensuring that all nested resources are cleaned up and/or stopped on exit.
//
// Design note: it is important to allow multiple concurrent archetypes here, because, like in Go, many natural MPCal
//              implementations involve multiple communicating processes. The builder fn gives the user the opportunity
//              to freely set up a complete, functioning subsystem, just like a free-standing configuration would allow.
func NewNested(fn func(sendCh chan<- tla.Value, receiveCh <-chan tla.Value) []*distsys.MPCalContext) distsys.ArchetypeResource {
	sendCh := make(chan tla.Value)
	receiveCh := make(chan tla.Value, 1)
	nestedCtxs := fn(receiveCh, sendCh) // these are flipped, because, from the archetype's POV, they work the opposite way

	res := &nestedArchetype{
		nestedCtxs:    nestedCtxs,
		ctxErrCh:      make(chan error, len(nestedCtxs)),
		ctxHasStopped: make(chan struct{}),

		sendCh:    sendCh,
		receiveCh: receiveCh,

		apiErrCh:    make(chan error, 1),
		apiStructCh: make(chan struct{}, 1),
	}

	for _, nestedCtx := range nestedCtxs {
		nestedCtx := nestedCtx
		go func() {
			var err error
			// to avoid res.Close() deadlocking if it's called from a defer after a nextedCtx.Run() has panicked and crashed the whole program,
			// we make 100% sure that the err value, nil or not, goes in the ctxErrCh, to keep the property
			// that the channel will yield exactly len(nestedCtxs) error values.
			defer func() {
				res.ctxErrCh <- err
			}()

			// note that panics are leaked on purpose here; the archetype crashing should be visible, and should
			// get a proper stacktrace... which may be doable with a sophisticated enough error value, but another time maybe
			err = nestedCtx.Run()
			if err != nil {
				err = fmt.Errorf("error in nested archetype %s(%v): %w", nestedCtx.Archetype().Name, nestedCtx.IFace().Self(), err)
			}

			// signal that any nested context has stopped (and maybe crashed). we assume that all nested contexts must be running
			// for resource API requests to be serviced. complicated lock + select structure is to make sure only one
			// goroutine actually tries to close the ctxHasStopped channel
			res.ctxHasStoppedLock.Lock()
			defer res.ctxHasStoppedLock.Unlock()
			select {
			case <-res.ctxHasStopped: // skip, someone closed it already
			default:
				close(res.ctxHasStopped)
			}
		}()
	}

	return res
}

// assertSanity asserts that all the channels a nestedArchetype holds are empty
// this assumption should be valid at the start of any resource API call, because every exchange should have leave channels drained
// (except for ctxErrCh, which may be filled asynchronously by the archetype failing or shutting down, and that's someone else's problem)
//
// recvMustBeEmpty toggles whether we care about in-flight requests. aborts may be sent before the nested archetype
// has had time to do anything, and so will set that to false. all other cases should not feature any concurrency of that kind.
func (res *nestedArchetype) assertSanity(recvMustBeEmpty bool) {
	if recvMustBeEmpty {
		select {
		case badVal := <-res.receiveCh:
			panic(fmt.Errorf("%w: stale value %v found in archetype output", ErrNestedArchetypeSanity, badVal))
		default:
			// that's fine, we're just making sure nothing unnecessary is left in the channels
		}
	}
	select {
	case badErr := <-res.apiErrCh:
		panic(fmt.Errorf("%w: stale error found in resource API channel: %v", ErrNestedArchetypeSanity, badErr))
	case <-res.apiStructCh:
		panic(fmt.Errorf("%w: stale struct{} found in resource API channel", ErrNestedArchetypeSanity))
	default:
		// that's fine, we're just making sure nothing unnecessary is left in the channels
	}
}

func (res *nestedArchetype) ensureTimer(d time.Duration) <-chan time.Time {
	if res.requestTimer == nil {
		res.requestTimer = time.NewTimer(d)
	} else {
		if !res.requestTimer.Stop() {
			// it's possible for C to already be empty, so we either instantly drain it, or we just skip the operation.
			select {
			case <-res.requestTimer.C:
			default:
			}
		}
		res.requestTimer.Reset(d)
	}
	return res.requestTimer.C
}

func (res *nestedArchetype) performRequest(reqTpe tla.Value, fields ...tla.RecordField) (tla.Value, error) {
	req := tla.MakeRecord(append(fields, tla.RecordField{
		Key:   nestedArchetypeConstants.tpe,
		Value: reqTpe,
	}))
	select {
	case res.sendCh <- req:
		// go to next select
	case <-res.ctxHasStopped:
		return tla.Value{}, ErrNestedArchetypeStopped
	}

	select {
	case resp := <-res.receiveCh:
		return resp, nil
	case <-res.ctxHasStopped:
		return tla.Value{}, ErrNestedArchetypeStopped
	}
}

func (res *nestedArchetype) catchTLATypeErrors(err *error) {
	if p := recover(); p != nil {
		if e, ok := p.(error); ok {
			*err = fmt.Errorf("%w: %v", ErrNestedArchetypeProtocol, e)
		} else {
			panic(p)
		}
	}
}

func (res *nestedArchetype) performRequestOrAbort(reqTpe tla.Value, fields ...tla.RecordField) (tla.Value, error) {
	req := tla.MakeRecord(append(fields, tla.RecordField{
		Key:   nestedArchetypeConstants.tpe,
		Value: reqTpe,
	}))
	select {
	case res.sendCh <- req:
		// go to next select
	case <-res.ctxHasStopped:
		return tla.Value{}, ErrNestedArchetypeStopped
	case <-res.ensureTimer(nestedArchetypeTimeout):
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	}

	select {
	case resp := <-res.receiveCh:
		return resp, nil
	case <-res.ctxHasStopped:
		return tla.Value{}, ErrNestedArchetypeStopped
	case <-res.ensureTimer(nestedArchetypeTimeout):
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *nestedArchetype) handleResponseValue(value tla.Value, allowAborted bool, expectedTpes ...tla.Value) (err error) {
	defer res.catchTLATypeErrors(&err)

	tpe := value.ApplyFunction(nestedArchetypeConstants.tpe)
	// map "aborted" over to a critical section abort. we'll still stop what we're doing, but we'll report the
	// non-fatal error, which, according to allowAborted, is what we mean.
	if allowAborted && tpe.Equal(nestedArchetypeAborted) {
		return distsys.ErrCriticalSectionAborted
	}

	for _, expectedTpe := range expectedTpes {
		if tpe.Equal(expectedTpe) {
			return nil
		}
	}
	return fmt.Errorf("%w: archetype response had unexpected tag %v, expected %v", ErrNestedArchetypeProtocol, tpe, expectedTpes)
}

func (res *nestedArchetype) Abort() chan struct{} {
	res.assertSanity(false)
	go func() {
		staleAcksReceived := 0

	retryReq:
		select {
		case res.sendCh <- tla.MakeRecord([]tla.RecordField{
			{nestedArchetypeConstants.tpe, nestedArchetypeAbortReq},
		}):
			// go to next select, we successfully sent the abort request
		case resp := <-res.receiveCh:
			// This case is because, uniquely, Abort might be sent before the nested archetype(s) finish processing a
			// request, due to a timeout waiting for a response to a request that has already reached the underlying system.
			// In that case, we should read and discard the response without complaining, because we did legitimately
			// ask for it from the nested system's POV (it must have been a read, write or precommit), then send the
			// abort request and wait as long as we need for the abort to be serviced.

			// The extra counting logic is because we should tolerate _exactly one_ extra ack, because we can't have
			// more than one in-flight request at once. Two responses means something broke in the underlying system,
			// and we should crash immediately.
			err := res.handleResponseValue(resp, false, nestedArchetypeReadAck, nestedArchetypeWriteAck, nestedArchetypePreCommitAck)
			if err != nil {
				panic(err)
			}
			if staleAcksReceived != 0 {
				panic(fmt.Errorf("received a second stale read/write/precommit ack while trying to perform abort: %v", resp))
			}
			staleAcksReceived++
			goto retryReq
		case <-res.ctxHasStopped:
			panic(fmt.Errorf("encountered error while trying to abort critical section: %w", ErrNestedArchetypeStopped))
		}

		select {
		case resp := <-res.receiveCh:
			err := res.handleResponseValue(resp, false, nestedArchetypeAbortAck)
			if err != nil {
				panic(err)
			}
		case <-res.ctxHasStopped:
			panic(fmt.Errorf("encountered error while trying to abort critical section: %w", ErrNestedArchetypeStopped))
		}

		res.apiStructCh <- struct{}{}
	}()
	return res.apiStructCh
}

func (res *nestedArchetype) PreCommit() chan error {
	res.assertSanity(true)
	go func() {
		resp, err := res.performRequestOrAbort(nestedArchetypePreCommitReq)
		if err != nil {
			res.apiErrCh <- err
			return
		}
		res.apiErrCh <- res.handleResponseValue(resp, true, nestedArchetypePreCommitAck)
	}()
	return res.apiErrCh
}

func (res *nestedArchetype) Commit() chan struct{} {
	res.assertSanity(true)
	go func() {
		resp, err := res.performRequest(nestedArchetypeCommitReq)
		if err != nil {
			panic(err)
		}
		err = res.handleResponseValue(resp, false, nestedArchetypeCommitAck)
		if err != nil {
			panic(err)
		}
		res.apiStructCh <- struct{}{}
	}()
	return res.apiStructCh
}

func (res *nestedArchetype) ReadValue() (_ tla.Value, err error) {
	res.assertSanity(true)
	defer res.catchTLATypeErrors(&err)

	resp, err := res.performRequestOrAbort(nestedArchetypeReadReq)
	if err != nil {
		return tla.Value{}, err
	}
	err = res.handleResponseValue(resp, true, nestedArchetypeReadAck)
	if err != nil {
		return tla.Value{}, err
	}
	return resp.ApplyFunction(nestedArchetypeConstants.value), nil
}

func (res *nestedArchetype) WriteValue(value tla.Value) (err error) {
	res.assertSanity(true)
	defer res.catchTLATypeErrors(&err)

	resp, err := res.performRequestOrAbort(nestedArchetypeWriteReq,
		tla.RecordField{Key: nestedArchetypeConstants.value, Value: value})
	if err != nil {
		return err
	}
	return res.handleResponseValue(resp, true, nestedArchetypeWriteAck)
}

func (res *nestedArchetype) Close() (err error) {
	// asynchronously terminate all nested contexts
	for _, nestedCtx := range res.nestedCtxs {
		go nestedCtx.Stop()
	}

	// because every goroutine calling Run() will unconditionally write to res.ctxErrCh on exit, we can use that to
	// collect error values and wait for termination at the same time.
	for range res.nestedCtxs {
		err = multierr.Append(err, <-res.ctxErrCh)
	}
	close(res.ctxErrCh)
	return
}
