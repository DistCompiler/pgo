package raftkvs

import (
	"fmt"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

const readTimeout = 1 * time.Millisecond

// CustomInChan is similar resources.InputChannel, however, after a timeout it
// returns a default value instead of aborting the critical section. It used in
// implementing periodic sending of AppendEntries request. In some cases, the
// request should be sent immediately, for example, when the server just becomes
// a leader. In this case, the input channel signals.
type CustomInChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel               <-chan tla.TLAValue
	buffer, backlogBuffer []tla.TLAValue
}

var _ distsys.ArchetypeResource = &CustomInChan{}

func CustomInChanMaker(channel <-chan tla.TLAValue) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerStruct{
		MakeFn: func() distsys.ArchetypeResource {
			return &CustomInChan{}
		},
		ConfigureFn: func(res distsys.ArchetypeResource) {
			r := res.(*CustomInChan)
			r.channel = channel
		},
	}
}

func (res *CustomInChan) Abort() chan struct{} {
	res.buffer = append(res.backlogBuffer, res.buffer...)
	res.backlogBuffer = nil
	return nil
}

func (res *CustomInChan) PreCommit() chan error {
	return nil
}

func (res *CustomInChan) Commit() chan struct{} {
	res.backlogBuffer = nil
	return nil
}

func (res *CustomInChan) ReadValue() (tla.TLAValue, error) {
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
	case <-time.After(readTimeout):
		return tla.TLA_TRUE, nil
	}
}

func (res *CustomInChan) WriteValue(value tla.TLAValue) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *CustomInChan) Close() error {
	return nil
}
