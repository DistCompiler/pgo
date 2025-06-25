package raftkvs

import (
	"fmt"
	"time"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
)

// CustomInChan is similar resources.InputChannel, however, after a timeout it
// returns a default value instead of aborting the critical section. It used in
// implementing periodic sending of AppendEntries request. In some cases, the
// request should be sent immediately, for example, when the server just becomes
// a leader. In this case, the input channel signals.
type CustomInChan struct {
	distsys.ArchetypeResourceLeafMixin
	channel               <-chan tla.Value
	buffer, backlogBuffer []tla.Value
	timeout               time.Duration
}

var _ distsys.ArchetypeResource = &CustomInChan{}

func NewCustomInChan(ch <-chan tla.Value, timeout time.Duration) distsys.ArchetypeResource {
	return &CustomInChan{
		channel: ch,
		timeout: timeout,
	}
}

func (res *CustomInChan) Abort(distsys.ArchetypeInterface) chan struct{} {
	res.buffer = append(res.backlogBuffer, res.buffer...)
	res.backlogBuffer = nil
	return nil
}

func (res *CustomInChan) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *CustomInChan) Commit(distsys.ArchetypeInterface) chan struct{} {
	res.backlogBuffer = nil
	return nil
}

func (res *CustomInChan) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
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
		return tla.ModuleTRUE, nil
	}
}

func (res *CustomInChan) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	panic(fmt.Errorf("attempted to write %v to an input channel resource", value))
}

func (res *CustomInChan) Close() error {
	return nil
}
