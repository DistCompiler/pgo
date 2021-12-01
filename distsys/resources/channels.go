package resources

import (
	"fmt"
	"time"

	"github.com/UBC-NSS/pgo/distsys/tla"

	"github.com/UBC-NSS/pgo/distsys"
)

const inputChannelReadTimout = 20 * time.Millisecond

// InputChannel wraps a native Go channel, such that an MPCal model might read what is written
// to the channel.
type InputChannel struct {
	distsys.ArchetypeResourceLeafMixin
	channel               <-chan tla.TLAValue
	buffer, backlogBuffer []tla.TLAValue
}

var _ distsys.ArchetypeResource = &InputChannel{}

func InputChannelMaker(channel <-chan tla.TLAValue) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &InputChannel{}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*InputChannel)
			r.channel = channel
		},
	}
}

func (res *InputChannel) Abort() chan struct{} {
	res.buffer = append(res.backlogBuffer, res.buffer...)
	res.backlogBuffer = nil
	return nil
}

func (res *InputChannel) PreCommit() chan error {
	return nil
}

func (res *InputChannel) Commit() chan struct{} {
	res.backlogBuffer = nil
	return nil
}

func (res *InputChannel) ReadValue() (tla.TLAValue, error) {
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
	case <-time.After(inputChannelReadTimout):
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *InputChannel) WriteValue(value tla.TLAValue) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *InputChannel) Close() error {
	return nil
}

// OutputChannel wraps a native Go channel, such that an MPCal model may write to that channel.
type OutputChannel struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- tla.TLAValue
	buffer  []tla.TLAValue
}

var _ distsys.ArchetypeResource = &OutputChannel{}

func OutputChannelMaker(channel chan<- tla.TLAValue) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &OutputChannel{}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*OutputChannel)
			r.channel = channel
		},
	}
}

func (res *OutputChannel) Abort() chan struct{} {
	res.buffer = nil
	return nil
}

func (res *OutputChannel) PreCommit() chan error {
	return nil
}

func (res *OutputChannel) Commit() chan struct{} {
	ch := make(chan struct{})
	go func() {
		for _, value := range res.buffer {
			res.channel <- value
		}
		res.buffer = nil
		ch <- struct{}{}
	}()
	return ch
}

func (res *OutputChannel) ReadValue() (tla.TLAValue, error) {
	panic(fmt.Errorf("attempted to read from an output channel resource"))
}

func (res *OutputChannel) WriteValue(value tla.TLAValue) error {
	res.buffer = append(res.buffer, value)
	return nil
}

func (res *OutputChannel) Close() error {
	return nil
}
