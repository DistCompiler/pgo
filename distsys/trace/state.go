package trace

import (
	"strings"

	"github.com/DistCompiler/pgo/distsys/tla"
)

type EventState struct {
	Recorder      Recorder
	ArchetypeName string
	ArchetypeSelf tla.Value
	elements      []Element
}

func (acc *EventState) HasRecorder() bool {
	return acc.Recorder != nil
}

func (acc *EventState) clearElements() {
	// clear slice to GC old elements
	for idx := range acc.elements {
		acc.elements[idx] = nil
	}
	acc.elements = acc.elements[:0]
}

func (acc *EventState) BeginEvent() {
	if acc.Recorder == nil {
		return
	}
	if len(acc.elements) != 0 {
		panic("trace accumulator corrupted")
	}
}

func (acc *EventState) DropEvent() {
	if acc.Recorder == nil {
		return
	}
	acc.clearElements()
}

func (acc *EventState) CommitEvent(clock tla.VClock) {
	if acc.Recorder == nil {
		return
	}
	acc.Recorder.RecordEvent(Event{
		ArchetypeName: acc.ArchetypeName,
		Self:          acc.ArchetypeSelf,
		Elements:      acc.elements,
		Clock:         clock,
	})
	acc.clearElements()
}

func (acc *EventState) CrashEvent(err error, clock tla.VClock) {
	if acc.Recorder == nil {
		return
	}
	// TODO: actually do something with the crash info
	acc.CommitEvent(clock)
}

func (acc *EventState) RecordRead(name string, indices []tla.Value, value tla.Value) {
	if acc.Recorder == nil {
		return
	}
	if len(name) == 0 {
		panic("read with empty name")
	}
	var prefix string
	if name[0] != '.' {
		splits := strings.Split(name, ".")
		prefix, name = splits[0], splits[1]
	}
	acc.elements = append(acc.elements, ReadElement{
		Prefix:  prefix,
		Name:    name,
		Indices: indices,
		Value:   value,
	})
}

func (acc *EventState) RecordWrite(name string, indices []tla.Value, oldValueHint *tla.Value, value tla.Value) {
	if acc.Recorder == nil {
		return
	}
	if len(name) == 0 {
		panic("read with empty name")
	}
	var prefix string
	if name[0] != '.' {
		splits := strings.Split(name, ".")
		prefix, name = splits[0], splits[1]
	}
	acc.elements = append(acc.elements, WriteElement{
		Prefix:       prefix,
		Name:         name,
		Indices:      indices,
		OldValueHint: oldValueHint,
		Value:        value,
	})
}
