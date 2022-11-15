package trace

import (
	"strings"

	"github.com/UBC-NSS/pgo/distsys/tla"
)

type EventState struct {
	Recorder      Recorder
	ArchetypeName string
	ArchetypeSelf tla.Value
	elements      []Element
	clock         VClock
	oldClock      VClock
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

func (acc *EventState) UpdateVClock(clock VClock) {
	if acc.Recorder == nil {
		return
	}
	acc.clock = acc.clock.Merge(clock)
}

func (acc *EventState) VClock() VClock {
	return acc.clock
}

func (acc *EventState) BeginEvent() {
	if acc.Recorder == nil {
		return
	}
	if len(acc.elements) != 0 {
		panic("trace accumulator corrupted")
	}
	acc.oldClock = acc.clock
	acc.clock = acc.clock.Inc(acc.ArchetypeName, acc.ArchetypeSelf)
}

func (acc *EventState) DropEvent() {
	if acc.Recorder == nil {
		return
	}
	acc.clearElements()
	acc.clock = acc.oldClock
	acc.oldClock = VClock{}
}

func (acc *EventState) CommitEvent() {
	if acc.Recorder == nil {
		return
	}
	acc.Recorder.RecordEvent(Event{
		ArchetypeName: acc.ArchetypeName,
		Self:          acc.ArchetypeSelf,
		Elements:      acc.elements,
		Clock:         acc.clock,
	})
	for idx := range acc.elements {
		acc.elements[idx] = nil
	}
	acc.clearElements()
	acc.oldClock = VClock{}
}

func (acc *EventState) CrashEvent(err error) {
	if acc.Recorder == nil {
		return
	}
	// TODO: actually do something with the crash info
	acc.CommitEvent()
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

func (acc *EventState) RecordWrite(name string, indices []tla.Value, value tla.Value) {
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
		Prefix:  prefix,
		Name:    name,
		Indices: indices,
		Value:   value,
	})
}
