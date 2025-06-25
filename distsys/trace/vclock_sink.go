package trace

import (
	"sync"

	"github.com/DistCompiler/pgo/distsys/tla"
)

type VClockSink struct {
	clock   tla.VClock
	lock    sync.RWMutex
	enabled bool
}

func (sink *VClockSink) Enabled() bool {
	return sink.enabled
}

func (sink *VClockSink) SetEnabled(enabled bool) {
	sink.enabled = enabled
}

func (sink *VClockSink) InitCriticalSection(name string, self tla.Value) {
	if !sink.enabled {
		return
	}
	sink.lock.Lock()
	defer sink.lock.Unlock()
	sink.clock = sink.clock.Inc(name, self)
}

func (sink *VClockSink) WitnessVClock(vclock tla.VClock) {
	if !sink.enabled {
		return
	}
	sink.lock.Lock()
	defer sink.lock.Unlock()
	sink.clock = sink.clock.Merge(vclock)
}

func (sink *VClockSink) GetVClock() tla.VClock {
	if !sink.enabled {
		return tla.VClock{}
	}
	sink.lock.RLock()
	defer sink.lock.RUnlock()
	return sink.clock
}
