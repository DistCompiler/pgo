package distsys

type ProcessInitialization struct {
	Peers       []string
	Self        string
	Coordinator string
	startChan   chan bool // buffered channel of size 1 (for coordinator only!)
}

func NewProcessInitialization(Peers, Self, Coordinator) {
	// if I am the coordinator
	// startChan == buffered channel size of make(chan bool, 1)
	// else
	// startChan == unbuffered channel
}

func (init *ProcessInitialization) Init() {
	// 1. Bind to my own address (Self)
	// 2. start a listener on that address on a separate Goroutine
	// 3. if I am the coordinator
	// else if I am not the coordinator
	//	send "hello" message to coordinator
	//	if it fails, keep retrying
}

// Non coordinator:
// func Start() -> { startChan <- true }j

func (init *ProcessInitialization) WaitPeers() {
	// <- startChan
}
