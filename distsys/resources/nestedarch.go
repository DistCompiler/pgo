package resources

import (
	"errors"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"go.uber.org/multierr"
	"time"
)

// ErrNestedArchetypeProtocol signifies that a nested archetype misbehaved while we were trying to use it as an archetype implementation
var ErrNestedArchetypeProtocol = errors.New("error during interaction with nested archetype")
// ErrNestedArchetypeSanity signifies that some internal sanity check failed regarding buffer / channel state. intended for use during panic
var ErrNestedArchetypeSanity = errors.New("internal sanity check failed")

const (
	// nestedArchetypeTimeout is how long a nested archetype will wait on an operation before giving up
	// this is arbitrary and hardcoded, and should be made configurable later.
	nestedArchetypeTimeout = 100 * time.Millisecond
)

var nestedArchetypeReadReq = tla.MakeTLAString("read_req")
var nestedArchetypeWriteReq = tla.MakeTLAString("write_req")
var nestedArchetypePreCommitReq = tla.MakeTLAString("precommit_req")
var nestedArchetypeAbortReq = tla.MakeTLAString("abort_req")
var nestedArchetypeCommitReq = tla.MakeTLAString("commit_req")

var nestedArchetypeReadAck = tla.MakeTLAString("read_ack")
var nestedArchetypeWriteAck = tla.MakeTLAString("write_ack")
var nestedArchetypePreCommitAck = tla.MakeTLAString("precommit_ack")
var nestedArchetypeAbortAck = tla.MakeTLAString("abort_ack")
var nestedArchetypeCommitAck = tla.MakeTLAString("commit_ack")

var nestedArchetypeAborted = tla.MakeTLAString("aborted")

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
	tpe tla.TLAValue
	value tla.TLAValue
}

var nestedArchetypeConstants = nestedArchetypeConstantsT {
	tpe: tla.MakeTLAString("tpe"),
	value: tla.MakeTLAString("value"),
}

type nestedArchetype struct {
	distsys.ArchetypeResourceLeafMixin
	nestedCtxs []*distsys.MPCalContext
	ctxErrCh chan error

	sendCh chan tla.TLAValue
	receiveCh chan tla.TLAValue

	cachedErrCh chan error
	cachedStructCh chan struct{}

	cachedTimer *time.Timer
}

var _ distsys.ArchetypeResource = new(nestedArchetype)

// NestedArchetypeMaker adapts a specific form of MPCal archetype to the resource interface, allowing resources to be
// implemented and model checked in MPCal themselves.
//
// The argument fn should map a pair of input and output channels to the inputs and outputs of one or more nested archetype
// instances, which, aside from these channels, should be configured just as free-standing archetypes would be.
// This resource will then take over those contexts' lifecycles, falling Run on then, forwarding errors to the
// containing context's execution, and ensuring that all nested resources are cleaned up on exit.
func NestedArchetypeMaker(fn func (sendCh chan<- tla.TLAValue, receiveCh <-chan tla.TLAValue) []*distsys.MPCalContext) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		sendCh := make(chan tla.TLAValue)
		receiveCh := make(chan tla.TLAValue, 1)
		nestedCtxs := fn(receiveCh, sendCh) // these are flipped, because, from the archetype's POV, they work the opposite way

		ctxErrCh := make(chan error, len(nestedCtxs))
		for _, nestedCtx := range nestedCtxs {
			nestedCtx := nestedCtx
			go func() {
				// note that panics are leaked on purpose here; the archetype crashing should be visible, and should
				// get a proper stacktrace... which may be doable with a sophisticated enough error value, but another time maybe
				err := nestedCtx.RunDiscardingExits()
				if err != nil {
					err = fmt.Errorf("error in nested archetype %s(%v): %w", nestedCtx.Archetype().Name, nestedCtx.IFace().Self(), err)
				}
				ctxErrCh <- err
			}()
		}

		return &nestedArchetype{
			nestedCtxs: nestedCtxs,
			ctxErrCh: ctxErrCh,

			sendCh: sendCh,
			receiveCh: receiveCh,

			cachedErrCh: make(chan error, 1),
			cachedStructCh: make(chan struct{}, 1),
		}
	})
}

// assertSanity asserts that all the channels a nestedArchetype holds are empty
// this assumption should be valid at the start of any resource API call, because every exchange should have leave channels drained
// (except for nestedCtxErr, which may be filled asynchronously by the archetype failing or shutting down, and that's someone else's problem)
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
	case badErr := <-res.cachedErrCh:
		panic(fmt.Errorf("%w: stale error found in resource API channel: %v", ErrNestedArchetypeSanity, badErr))
	case <-res.cachedStructCh:
		panic(fmt.Errorf("%w: stale struct{} found in resource API channel", ErrNestedArchetypeSanity))
	default:
		// that's fine, we're just making sure nothing unnecessary is left in the channels
	}
}

func (res *nestedArchetype) ensureTimer(d time.Duration) <-chan time.Time {
	if res.cachedTimer == nil {
		res.cachedTimer = time.NewTimer(d)
	} else {
		if !res.cachedTimer.Stop() {
			// it's possible for C to already be empty, so we either instantly drain it, or we just skip the operation.
			select {
			case <-res.cachedTimer.C:
			default:
			}
		}
		res.cachedTimer.Reset(d)
	}
	return res.cachedTimer.C
}

func (res *nestedArchetype) performRequest(reqTpe tla.TLAValue, fields... tla.TLARecordField) (tla.TLAValue, error) {
	select {
	case res.sendCh <-tla.MakeTLARecord(append(fields, tla.TLARecordField{
		Key: nestedArchetypeConstants.tpe,
		Value: reqTpe,
	})):
		// go to next select
	case err := <-res.ctxErrCh:
		return tla.TLAValue{}, fmt.Errorf("encountered nested archetype error: %w", err)
	}

	select {
	case resp := <-res.receiveCh:
		return resp, nil
	case err := <-res.ctxErrCh:
		return tla.TLAValue{}, fmt.Errorf("encountered nested archetype error: %w", err)
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

func (res *nestedArchetype) performRequestOrAbort(reqTpe tla.TLAValue, fields... tla.TLARecordField) (tla.TLAValue, error) {
	select {
	case res.sendCh <- tla.MakeTLARecord(append(fields, tla.TLARecordField{
		Key: nestedArchetypeConstants.tpe,
		Value: reqTpe,
	})):
		// go to next select
	case err := <-res.ctxErrCh:
		return tla.TLAValue{}, fmt.Errorf("encountered nested archetype error: %w", err)
	case <-res.ensureTimer(nestedArchetypeTimeout):
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}

	select {
	case resp := <-res.receiveCh:
		return resp, nil
	case err := <-res.ctxErrCh:
		return tla.TLAValue{}, fmt.Errorf("encountered nested archetype error: %w", err)
	case <-res.ensureTimer(nestedArchetypeTimeout):
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *nestedArchetype) handleResponseValue(value tla.TLAValue, allowAborted bool, expectedTpes... tla.TLAValue) (err error){
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
		case res.sendCh <-tla.MakeTLARecord([]tla.TLARecordField{
			{nestedArchetypeConstants.tpe, nestedArchetypeAbortReq },
		}):
			// go to next select, we successfully sent the abort request
		case resp := <-res.receiveCh:
			err := res.handleResponseValue(resp, false, nestedArchetypeReadAck, nestedArchetypeWriteAck)
			if err != nil {
				panic(err)
			}
			if staleAcksReceived != 0 {
				panic(fmt.Errorf("received a second stale read/write ack while trying to perform abort: %v", resp))
			}
			staleAcksReceived++
			goto retryReq
		case err := <-res.ctxErrCh:
			panic(fmt.Errorf("encountered error while trying to abort critical section: %w", err))
		}

		select {
		case resp := <-res.receiveCh:
			err := res.handleResponseValue(resp, false, nestedArchetypeAbortAck)
			if err != nil {
				panic(err)
			}
		case err := <-res.ctxErrCh:
			panic(fmt.Errorf("encountered error while trying to abort critical section: %w", err))
		}

		res.cachedStructCh <- struct{}{}
	}()
	return res.cachedStructCh
}

func (res *nestedArchetype) PreCommit() chan error {
	res.assertSanity(true)
	go func() {
		resp, err := res.performRequestOrAbort(nestedArchetypePreCommitReq)
		if err != nil {
			res.cachedErrCh <- err
			return
		}
		res.cachedErrCh <- res.handleResponseValue(resp, true, nestedArchetypePreCommitAck)
	}()
	return res.cachedErrCh
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
		res.cachedStructCh <- struct{}{}
	}()
	return res.cachedStructCh
}

func (res *nestedArchetype) ReadValue() (_ tla.TLAValue, err error) {
	res.assertSanity(true)
	defer res.catchTLATypeErrors(&err)

	resp, err := res.performRequestOrAbort(nestedArchetypeReadReq)
	if err != nil {
		return tla.TLAValue{}, err
	}
	err = res.handleResponseValue(resp, true, nestedArchetypeReadAck)
	if err != nil {
		return tla.TLAValue{}, err
	}
	return resp.ApplyFunction(nestedArchetypeConstants.value), nil
}

func (res *nestedArchetype) WriteValue(value tla.TLAValue) (err error) {
	res.assertSanity(true)
	defer res.catchTLATypeErrors(&err)

	resp, err := res.performRequestOrAbort(nestedArchetypeWriteReq,
		tla.TLARecordField{Key: nestedArchetypeConstants.value, Value: value})
	if err != nil {
		return err
	}
	return res.handleResponseValue(resp, true, nestedArchetypeWriteAck)
}

func (res *nestedArchetype) Close() (err error) {
	for _, nestedCtx := range res.nestedCtxs {
		nestedCtx.RequestExit()
	}
	for range res.nestedCtxs {
		err = multierr.Append(err, <-res.ctxErrCh)
	}
	close(res.ctxErrCh)
	return
}
