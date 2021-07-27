package resources

import (
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"time"
)

// InputChannelResource wraps a native Go channel, such that an MPCal model might read what is written
// to the channel.
type InputChannelResource struct {
	distsys.ArchetypeResourceLeafMixin
	channel               <-chan distsys.TLAValue
	buffer, backlogBuffer []distsys.TLAValue
}

var _ distsys.ArchetypeResource = &InputChannelResource{}

func InputChannelResourceMaker(channel <-chan distsys.TLAValue) distsys.ArchetypeResourceMaker {
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

func (res *InputChannelResource) ReadValue() (distsys.TLAValue, error) {
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
	case <-time.After(time.Millisecond * 20):
		return distsys.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *InputChannelResource) WriteValue(value distsys.TLAValue) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

// OutputChannelResource wraps a native Go channel, such that an MPCal model may write to that channel.
type OutputChannelResource struct {
	distsys.ArchetypeResourceLeafMixin
	channel chan<- distsys.TLAValue
	buffer  []distsys.TLAValue
}

var _ distsys.ArchetypeResource = &OutputChannelResource{}

func OutputChannelResourceMaker(channel chan<- distsys.TLAValue) distsys.ArchetypeResourceMaker {
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

func (res *OutputChannelResource) ReadValue() (distsys.TLAValue, error) {
	panic(fmt.Errorf("attempted to read from an output channel resource"))
}

func (res *OutputChannelResource) WriteValue(value distsys.TLAValue) error {
	res.buffer = append(res.buffer, value)
	return nil
}
