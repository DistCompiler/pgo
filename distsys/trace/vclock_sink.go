package trace

import (
	"sync"

	"github.com/DistCompiler/pgo/distsys/tla"
)

type VClockSink struct {
	clock tla.VClock
	lock  sync.RWMutex
}

func (sink *VClockSink) InitCriticalSection(name string, self tla.Value) {
	sink.lock.Lock()
	defer sink.lock.Unlock()
	sink.clock = sink.clock.Inc(name, self)
}

func (sink *VClockSink) WitnessVClock(vclock tla.VClock) {
	sink.lock.Lock()
	defer sink.lock.Unlock()
	sink.clock = sink.clock.Merge(vclock)
}

func (sink *VClockSink) GetVClock() tla.VClock {
	sink.lock.RLock()
	defer sink.lock.RUnlock()
	return sink.clock
}
