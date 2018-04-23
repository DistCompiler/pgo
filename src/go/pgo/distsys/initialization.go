package distsys

import (
	"net"
	"net/rpc"
	"time"
)

const (
	RPC_ID = "PlusCalProcess"
)

// This implements the process initialization protocol of PlusCal processes.
// When a PlusCal specification is compiled to TLA+, the TLC model checker
// starts every "process" defined in PlusCal at the same time.
//
// Process initialization as implemented here makes sure that a process will
// only start its algorithm execution once all other processes are online.
// This is particularly useful for specifications that use (or require) fair
// scheduling.

type ProcessInitialization struct {
	Peers          []string               // the list of peers (PlusCal processes)
	Self           string                 // the identification of the current process (IP:port)
	Coordinator    string                 // which host is the coordinator (IP:port)
	Network        map[string]*rpc.Client // maps connections from peers
	readyChan      chan bool              // underlying channel used to coordinate start
	processesReady int                    // how many processes are ready currently (used only by the coordinator)
}

func NewProcessInitialization(peers []string, self, coordinator string) *ProcessInitialization {
	pi := ProcessInitialization{
		Peers:       peers,
		Self:        self,
		Coordinator: coordinator,
		Network:     map[string]*rpc.Client{},
	}

	// if node is the coordinator, create a buffered channel; otherwise, a
	// synchronous channel is sufficient
	if self == coordinator {
		pi.readyChan = make(chan bool, 1)
	} else {
		pi.readyChan = make(chan bool)
	}

	return &pi
}

func (init *ProcessInitialization) isCoordinator() bool {
	return init.Self == init.Coordinator
}

func (self *ProcessInitialization) Init() error {
	// bind to this node's own address
	listener, err := net.Listen("tcp", self.Self)
	if err != nil {
		return err
	}

	rpcConn := rpc.NewServer()
	if err := rpcConn.RegisterName(RPC_ID, self); err != nil {
		return err
	}

	go rpcConn.Accept(listener)
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
		client, err := rpc.Dial("tcp", init.Coordinator)
		if err != nil {
			time.Sleep(1)
			continue
		}

		defer client.Close()

		var ok bool
		if err := client.Call(RPC_ID+".ProcessReady", init.Self, &ok); err != nil {
			continue
		}

		// call succeeded -- finish
		init.Network[init.Coordinator] = client
		return
	}
}

// PlusCal processes invoke this RPC method on the coordinator to indicate they are ready
// to run. The coordinator keeps a counter of how many processes are ready, and when the
// counter is equal to the (static) number of peers, it means all processes are up and
// ready to run. Send a message to each of them indicating that they may start running
// their algorithms
func (self *ProcessInitialization) ProcessReady(id []string, ok *bool) error {
	self.processesReady += 1
	*ok = true

	if self.processesReady == len(self.Peers) {
		for _, id := range self.Peers {
			if id == self.Self {
				continue
			}

			client, err := rpc.Dial("tcp", id)
			if err != nil {
				return err
			}

			var ok bool
			if err := client.Call(RPC_ID+".Start", self.Self, &ok); err != nil {
				return err
			}

			self.Network[id] = client
		}
	}

	return nil
}

// Coordinator sends this message to every process when it detects that every
// process is ready
func (init *ProcessInitialization) Start(_ int, ok *bool) error {
	init.readyChan <- true
	*ok = true

	return nil
}

// Waits for all PlusCall processes to be up and ready to run
func (init *ProcessInitialization) WaitPeers() {
	<-init.readyChan
}
