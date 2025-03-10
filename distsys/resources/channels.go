package resources

import (
	"fmt"
	"time"

	"github.com/DistCompiler/pgo/distsys/tla"

	"github.com/DistCompiler/pgo/distsys"
)

const inputChanReadTimout = 20 * time.Millisecond

// InputChan wraps a native Go channel, such that an MPCal model might read what is written
// to the channel.
type InputChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel               <-chan tla.Value
	buffer, backlogBuffer []tla.Value
	timeout               time.Duration
}

var _ distsys.ArchetypeResource = &InputChan{}

type InputChanOption func(*InputChan)

func WithInputChanReadTimeout(t time.Duration) InputChanOption {
	return func(res *InputChan) {
		res.timeout = t
	}
}

func NewInputChan(ch <-chan tla.Value, opts ...InputChanOption) *InputChan {
	res := &InputChan{
		timeout: inputChanReadTimout,
		channel: ch,
	}
	for _, opt := range opts {
		opt(res)
	}
	return res
}

func (res *InputChan) Abort(distsys.ArchetypeInterface) chan struct{} {
	res.buffer = append(res.backlogBuffer, res.buffer...)
	res.backlogBuffer = nil
	return nil
}

func (res *InputChan) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *InputChan) Commit(distsys.ArchetypeInterface) chan struct{} {
	res.backlogBuffer = nil
	return nil
}

func (res *InputChan) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	if len(res.buffer) > 0 {
		value := res.buffer[0]
		res.buffer = res.buffer[1:]
		res.backlogBuffer = append(res.backlogBuffer, value)
		return value, nil
	}

	select {
	case value := <-res.channel:
		res.backlogBuffer = append(res.backlogBuffer, value)
		return value, nil
	case <-time.After(res.timeout):
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *InputChan) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *InputChan) Close() error {
	return nil
}

// OutputChan wraps a native Go channel, such that an MPCal model may write to that channel.
type OutputChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- tla.Value
	buffer  []tla.Value
}

var _ distsys.ArchetypeResource = &OutputChan{}

func NewOutputChan(ch chan<- tla.Value) *OutputChan {
	return &OutputChan{channel: ch}
}

func (res *OutputChan) Abort(distsys.ArchetypeInterface) chan struct{} {
	res.buffer = nil
	return nil
}

func (res *OutputChan) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *OutputChan) Commit(iface distsys.ArchetypeInterface) chan struct{} {
	ch := make(chan struct{})
	go func() {
		for _, value := range res.buffer {
			res.channel <- tla.WrapCausal(value.StripVClock(), iface.GetVClockSink().GetVClock())
		}
		res.buffer = nil
		ch <- struct{}{}
	}()
	return ch
}

func (res *OutputChan) ReadValue(iface distsys.ArchetypeInterface) (tla.Value, error) {
	panic(fmt.Errorf("attempted to read from an output channel resource"))
}

func (res *OutputChan) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	res.buffer = append(res.buffer, value)
	return nil
}

func (res *OutputChan) Close() error {
	return nil
}

const singleOutputChanWriteTimeout = 20 * time.Millisecond

type SingleOutputChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- tla.Value
}

var _ distsys.ArchetypeResource = &SingleOutputChan{}

func NewSingleOutputChan(ch chan<- tla.Value) *SingleOutputChan {
	return &SingleOutputChan{
		channel: ch,
	}
}

func (res *SingleOutputChan) Abort(distsys.ArchetypeInterface) chan struct{} {
	panic("can't abort SingleOutputChan")
}

func (res *SingleOutputChan) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *SingleOutputChan) Commit(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *SingleOutputChan) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	panic("can't read from SingleOutputChan")
}

func (res *SingleOutputChan) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	select {
	case res.channel <- value:
		return nil
	case <-time.After(singleOutputChanWriteTimeout):
		return distsys.ErrCriticalSectionAborted
	}
}

func (res *SingleOutputChan) Close() error {
	return nil
}
