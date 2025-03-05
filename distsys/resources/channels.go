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
	iface                 distsys.ArchetypeInterface
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

func (res *InputChan) Abort() chan struct{} {
	res.buffer = append(res.backlogBuffer, res.buffer...)
	res.backlogBuffer = nil
	return nil
}

func (res *InputChan) PreCommit() chan error {
	return nil
}

func (res *InputChan) Commit() chan struct{} {
	res.backlogBuffer = nil
	return nil
}

func (res *InputChan) ReadValue() (tla.Value, error) {
	if len(res.buffer) > 0 {
		value := res.buffer[0]
		res.buffer = res.buffer[1:]
		res.backlogBuffer = append(res.backlogBuffer, value)
		if value.GetVClock() != nil {
			res.iface.GetVClockSink().WitnessVClock(*value.GetVClock())
		}
		return value, nil
	}

	select {
	case value := <-res.channel:
		res.backlogBuffer = append(res.backlogBuffer, value)
		if value.GetVClock() != nil {
			res.iface.GetVClockSink().WitnessVClock(*value.GetVClock())
		}
		return value, nil
	case <-time.After(res.timeout):
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *InputChan) WriteValue(value tla.Value) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *InputChan) Close() error {
	return nil
}

func (res *InputChan) SetIFace(iface distsys.ArchetypeInterface) {
	res.iface = iface
}

// OutputChan wraps a native Go channel, such that an MPCal model may write to that channel.
type OutputChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- tla.Value
	buffer  []tla.Value
	iface   distsys.ArchetypeInterface
}

var _ distsys.ArchetypeResource = &OutputChan{}

func NewOutputChan(ch chan<- tla.Value) *OutputChan {
	return &OutputChan{channel: ch}
}

func (res *OutputChan) Abort() chan struct{} {
	res.buffer = nil
	return nil
}

func (res *OutputChan) PreCommit() chan error {
	return nil
}

func (res *OutputChan) Commit() chan struct{} {
	ch := make(chan struct{})
	go func() {
		for _, value := range res.buffer {
			res.channel <- tla.WrapCausal(value.StripVClock(), res.iface.GetVClockSink().GetVClock())
		}
		res.buffer = nil
		ch <- struct{}{}
	}()
	return ch
}

func (res *OutputChan) ReadValue() (tla.Value, error) {
	panic(fmt.Errorf("attempted to read from an output channel resource"))
}

func (res *OutputChan) WriteValue(value tla.Value) error {
	res.buffer = append(res.buffer, value)
	return nil
}

func (res *OutputChan) Close() error {
	return nil
}

func (res *OutputChan) SetIFace(iface distsys.ArchetypeInterface) {
	res.iface = iface
}

const singleOutputChanWriteTimeout = 20 * time.Millisecond

type SingleOutputChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- tla.Value
	iface   distsys.ArchetypeInterface
}

var _ distsys.ArchetypeResource = &SingleOutputChan{}

func NewSingleOutputChan(ch chan<- tla.Value) *SingleOutputChan {
	return &SingleOutputChan{
		channel: ch,
	}
}

func (res *SingleOutputChan) Abort() chan struct{} {
	panic("can't abort SingleOutputChan")
}

func (res *SingleOutputChan) PreCommit() chan error {
	return nil
}

func (res *SingleOutputChan) Commit() chan struct{} {
	return nil
}

func (res *SingleOutputChan) ReadValue() (tla.Value, error) {
	panic("can't read from SingleOutputChan")
}

func (res *SingleOutputChan) WriteValue(value tla.Value) error {
	wrappedValue := tla.WrapCausal(value.StripVClock(), res.iface.GetVClockSink().GetVClock())
	select {
	case res.channel <- wrappedValue:
		return nil
	case <-time.After(singleOutputChanWriteTimeout):
		return distsys.ErrCriticalSectionAborted
	}
}

func (res *SingleOutputChan) Close() error {
	return nil
}

func (res *SingleOutputChan) SetIFace(iface distsys.ArchetypeInterface) {
	res.iface = iface
}
