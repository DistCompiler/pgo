package resources

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
)

const inputChannelResourceReadTimout = 20 * time.Millisecond

// InputChannelResource wraps a native Go channel, such that an MPCal model might read what is written
// to the channel.
type InputChannelResource struct {
	distsys.ArchetypeResourceLeafMixin
	channel               <-chan tla.TLAValue
	buffer, backlogBuffer []tla.TLAValue
}

var _ distsys.ArchetypeResource = &InputChannelResource{}

func InputChannelResourceMaker(channel <-chan tla.TLAValue) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &InputChannelResource{}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*InputChannelResource)
			r.channel = channel
		},
	}
}

func (res *InputChannelResource) Abort() chan struct{} {
	res.buffer = append(res.backlogBuffer, res.buffer...)
	return nil
}

func (res *InputChannelResource) PreCommit() chan error {
	return nil
}

func (res *InputChannelResource) Commit() chan struct{} {
	res.backlogBuffer = nil
	return nil
}

func (res *InputChannelResource) ReadValue() (tla.TLAValue, error) {
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
	case <-time.After(inputChannelResourceReadTimout):
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *InputChannelResource) WriteValue(value tla.TLAValue) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *InputChannelResource) Close() error {
	return nil
}

// OutputChannelResource wraps a native Go channel, such that an MPCal model may write to that channel.
type OutputChannelResource struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- tla.TLAValue
	buffer  []tla.TLAValue
}

var _ distsys.ArchetypeResource = &OutputChannelResource{}

func OutputChannelResourceMaker(channel chan<- tla.TLAValue) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &OutputChannelResource{}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*OutputChannelResource)
			r.channel = channel
		},
	}
}

func (res *OutputChannelResource) Abort() chan struct{} {
	res.buffer = nil
	return nil
}

func (res *OutputChannelResource) PreCommit() chan error {
	return nil
}

func (res *OutputChannelResource) Commit() chan struct{} {
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

func (res *OutputChannelResource) ReadValue() (tla.TLAValue, error) {
	panic(fmt.Errorf("attempted to read from an output channel resource"))
}

func (res *OutputChannelResource) WriteValue(value tla.TLAValue) error {
	res.buffer = append(res.buffer, value)
	return nil
}

func (res *OutputChannelResource) Close() error {
	return nil
}
