package distsys

// This implements the process initialization protocol of PlusCal processes.
// When a PlusCal specification is compiled to TLA+, the TLC model checker
// starts every "process" defined in PlusCal at the same time.
//
// Process initialization as implemented here makes sure that a process will
// only start its algorithm execution once all other processes are online.
// This is particularly useful for specifications that use (or require) fair
// scheduling.

import (
	"sync/atomic"
	"time"
)

const (
	RPC_ID = "PlusCalProcess"
)

// ProcessInitialization provides an initialization protocol that allows PlusCal
// processes to coordinate their start.
type ProcessInitializationState struct {
	Peers          []string     // the list of peers (PlusCal processes)
	Self           string       // the identification of the current process (IP:port)
	Coordinator    string       // which host is the coordinator (IP:port)
	processesReady int32        // how many processes are ready currently (used only by the coordinator)
	readyChan      chan bool    // underlying channel used to coordinate start
	connections    *Connections // connections to other peers
}

type ProcessInitialization struct {
	*ProcessInitializationState
}

func NewProcessInitialization(peers []string, self, coordinator string) *ProcessInitialization {
	state := &ProcessInitializationState{
		Peers:          peers,
		Self:           self,
		Coordinator:    coordinator,
		processesReady: 0,
		readyChan:      make(chan bool, 1),
		connections:    NewConnections(self),
	}

	return &ProcessInitialization{state}
}

func (init *ProcessInitialization) isCoordinator() bool {
	return init.Self == init.Coordinator
}

func (self *ProcessInitialization) Init() error {
	if err := self.connections.ExposeImplementation(RPC_ID, self.ProcessInitializationState); err != nil {
		return err
	}

	// the process itself is ready. Incremented when other processes indicate they are
	// ready via the `ProcessReady` RPC call
	self.processesReady = 1

	if !self.isCoordinator() {
		self.helloCoordinator()
	}

	return nil
}

func (init *ProcessInitialization) helloCoordinator() {
	// try to reach the coordinator until it finally succeeds.
	// Connection errors are interpreted to mean the coordinator is not up yet,
	// so we wait (indefinitely) for it to be.
	for {
		if err := init.connections.ConnectTo(init.Coordinator); err != nil {
			time.Sleep(1 * time.Second)
			continue
		}

		client := init.connections.GetConnection(init.Coordinator)
		var ok bool
		if err := client.Call(RPC_ID+".ProcessReady", init.Self, &ok); err != nil {
			continue
		}

		return
	}
}

// PlusCal processes invoke this RPC method on the coordinator to indicate they are ready
// to run. The coordinator keeps a counter of how many processes are ready, and when the
// counter is equal to the (static) number of peers, it means all processes are up and
// ready to run. Send a message to each of them indicating that they may start running
// their algorithms
func (self *ProcessInitializationState) ProcessReady(id string, ok *bool) error {
	atomic.AddInt32(&self.processesReady, 1)
	*ok = true

	if int(atomic.LoadInt32(&self.processesReady)) == len(self.Peers) {
		for _, id := range self.Peers {
			if id == self.Self {
				continue
			}

			if err := self.connections.ConnectTo(id); err != nil {
				return err
			}

			client := self.connections.GetConnection(id)
			var ok bool
			if err := client.Call(RPC_ID+".Start", 0, &ok); err != nil {
				return err
			}
		}

		self.readyChan <- true
	}

	return nil
}

// Coordinator sends this message to every process when it detects that every
// process is ready
func (init *ProcessInitializationState) Start(_ int, ok *bool) error {
	init.readyChan <- true
	*ok = true

	return nil
}

// Waits for all PlusCall processes to be up and ready to run
func (init *ProcessInitialization) WaitPeers() {
	<-init.readyChan
}
