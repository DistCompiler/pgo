package distsys

import (
	"fmt"
	"net/rpc"
	"sort"
	"strings"
)

// ResourceAccess indicates what type of access the a caller is requesting.
type ResourceAccess int

const (
	READ_ACCESS = iota + 1
	WRITE_ACCESS
)

// ArchetypeResource defines the interface that parameters passed to functions
// derived from Modular PlusCal's archetypes must implement.
type ArchetypeResource interface {
	// Acquire attempts to get access to a resource with read and/or write
	// permissions. Returns a boolean indicating whether it was successful.
	Acquire(access ResourceAccess) error

	// Read returns the current value associated with a resource.
	// Resource needs to have been acquired first.
	Read() (interface{}, error)

	// Write receives a new value that the underlying resource is
	// supposed to be set to.
	Write(value interface{}) error

	// Release causes the calling process to cease having access to the
	// shared resource. Any written changes to the underlying values
	// are committed.
	Release() error

	// Abort indicates an error situation. Access must be released,
	// and any state changed while the resource was accquired is
	// rolled back to its previous value, before acquisition
	Abort() error

	// Less compares one archetype resource with another. Ordering
	// archetype resources is needed when acquiring access to
	// resources that are sensitive to ordering (for instance, global
	// variables).
	Less(other ArchetypeResource) bool
}

// SortableArchetypeResource represents a collection of archetype
// resources.  This type implements the functions necessary to enable
// a collection of archetype resources to be sorted using Go's
// `sort.Sort` utility.
type SortableArchetypeResource []ArchetypeResource

func (s SortableArchetypeResource) Len() int {
	return len(s)
}

// Sorting occurs in-place.
func (s SortableArchetypeResource) Swap(i, j int) {
	s[i], s[j] = s[j], s[i]
}

func (s SortableArchetypeResource) Less(i, j int) bool {
	return s[i].Less(s[j])
}

// AcquireResources acquires a series of resources (concrete
// implementations of the `ArchetypeResource` interface) and returns
// an error in case one of the resources cannot be acquired. This
// function makes sure that resources are acquired in proper order
// (i.e., according to the resource's implementation of `Less`).
func AcquireResources(access ResourceAccess, resources ...ArchetypeResource) error {
	// sort the resources to be acquired according to their
	// implementation of `Less`
	sort.Sort(SortableArchetypeResource(resources))

	// resources are now ordered
	for _, r := range resources {
		err := r.Acquire(access)
		if err != nil {
			return err
		}
	}

	return nil
}

// ReleaseResources releases a collection of archetype resources
// simultaneously. If the values associated with these archetypes were
// updated (via Write calls on the archetypes), this will make the
// changes visible (committed). It makes sure that resources are
// released according to the order defined by the resource's
// implementation of `Less`.
func ReleaseResources(resources ...ArchetypeResource) error {
	sort.Sort(SortableArchetypeResource(resources))

	for _, r := range resources {
		if err := r.Release(); err != nil {
			return err
		}
	}

	return nil
}

// AbortResources releases (without modification) a collection of
// archetype resources simulaneously. It makes sure that resources are
// released according to the order defined by the resource's
// implementation of `Less`.
func AbortResources(resources ...ArchetypeResource) error {
	sort.Sort(SortableArchetypeResource(resources))

	for _, r := range resources {
		if err := r.Abort(); err != nil {
			return err
		}
	}

	return nil
}

/////////////////////////////////////////////////////////////////////////
////          GLOBAL STATE AS ARCHETYPE RESOURCES                   ////
///////////////////////////////////////////////////////////////////////

// Global variable is one type of archetype resource. It is backed by the
// StateServer implementation in this package.
type GlobalVariable struct {
	name         string
	stateServer  *StateServer
	refs         VarReferences
	writtenValue interface{}
}

// Variable is a convenience function to create a GlobalVariable struct from
// a previously configured StateServer. The returned GlobalVariable can be
// passed to archetypes, and the state represented by this variable will be
// managed by all peers in the system.
func (ss *StateServer) Variable(name string) *GlobalVariable {
	return &GlobalVariable{
		name:         name,
		stateServer:  ss,
		refs:         nil,
		writtenValue: nil,
	}
}

// Acquire wraps the underlying StateServer struct, creating a proper BorrowSpec
// and attempting to borrow the value from this node's peers in the network.
func (v *GlobalVariable) Acquire(access ResourceAccess) error {
	if v.refs != nil {
		return fmt.Errorf("variable %s already acquired", v.name)
	}

	var spec BorrowSpec

	if access&READ_ACCESS != 0 {
		spec.ReadNames = []string{v.name}
	}

	if access&WRITE_ACCESS != 0 {
		spec.WriteNames = []string{v.name}
	}

	refs, err := v.stateServer.Acquire(&spec)
	if err != nil {
		return err
	}

	v.refs = refs
	return nil
}

// Read returns the value associated with a global variable. It *must*
// have been acquired before.
func (v *GlobalVariable) Read() (interface{}, error) {
	return v.refs.Get(v.name), nil
}

// Write updates previously obtained references (via `Acquire`) to
// the value passed to this function.
func (v *GlobalVariable) Write(value interface{}) error {
	v.writtenValue = value
	return nil
}

// Release makes changes made while the variable was acquired visible
// to other processes.
func (v *GlobalVariable) Release() error {
	if v.writtenValue != nil {
		v.refs.Set(v.name, v.writtenValue)
	}

	err := v.stateServer.Release(v.refs)
	v.refs = nil

	return err
}

// Abort releases access (previously obtained via `Acquire`) without modifying
// the underlying value of a variable.
func (v *GlobalVariable) Abort() error {
	err := v.stateServer.Release(v.refs)
	v.refs = nil

	return err
}

// Less implements the ordering strategy for global variables. Global
// variables need to be acquired in lexicographical order to avoid
// deadlocks in the resulting system. This necessity is reflect in the
// implementation of `Less` which returns the result of a string
// comparison with `other` when it is also a global variable. In case
// the other archetype resource is not a global variable, Less always
// returns `false`, since the resources are not comparable.
func (v *GlobalVariable) Less(other ArchetypeResource) bool {
	// Go's `strings.Compare` returns an integer < 0 when the first
	// argument is < the second argument.
	if gv, ok := other.(*GlobalVariable); ok {
		return strings.Compare(v.name, gv.name) < 0
	}

	// the resources are not comparable -- do not change
	// their order in the archetype resources collection.
	return false
}

/////////////////////////////////////////////////////////////////////////
////          TCP CHANNELS AS ARCHETYPE RESOURCES                   ////
///////////////////////////////////////////////////////////////////////

// Receiver represents the interface exposed by TCP channels. When data
// is received by the other end of the channel, the data is sent across
// the underlying Go channel and can be read on calls to 'Acquire'.
type Receiver struct {
	ch chan interface{}
}

// Ready is invoked once when a new channel is established in order to
// indicate that one end of the channels is ready to receive data.
func (r *Receiver) Ready(_ *interface{}, ok *bool) error {
	*ok = true
	return nil
}

// Receive receives data from the other end of the channel.
func (r *Receiver) Receive(val *interface{}, ok *bool) error {
	r.ch <- *val
	*ok = true

	return nil
}

// TCPChannel is an implementation of ArchetypeResource that makes use
// of 'channel' semantics on top of the TCP protocol. Since nodes in a
// system generated by PGo already makes use of an IP:port combination
// for communication via Go RPC, this TCP channel implementation also
// runs on top of Go's RPC implementation.
type TCPChannel struct {
	service   string           // channels have a unique name
	conn      *rpc.Client      // RPC connection to the other end of the channel
	writeBuf  []interface{}    // messages waiting to be sent when the channel is released
	readChan  chan interface{} // reads are buffered through Go channels
	writeChan chan interface{} // writes are buffered through Go channels
}

func (tcpChannel *TCPChannel) call(name string, args interface{}, ok *bool) error {
	fName := tcpChannel.service + "." + name
	return tcpChannel.conn.Call(fName, &args, ok)
}

// SendMessages will wait indefinitely for data coming from `writeChan` and
// actually send the data over to the network.
func (tcpChannel *TCPChannel) SendMessages() {
	var ok bool

	for msg := range tcpChannel.writeChan {
		tcpChannel.call("Receive", msg, &ok)
	}
}

func (tcpChannel *TCPChannel) sync() {
	var ok bool
	for {
		if err := tcpChannel.call("Ready", 0, &ok); err == nil {
			break
		}
	}
}

// NewTCPChannel creates a TCP channel that can be used to provide direct, point-to-point
// communication across two nodes in the distributed system (PlusCal processes).
//
// The `name` given must be the same for both ends of the channel for communication to happen.
// `to` is the name of the *PlusCal process* that is to be contacted.
//
// Read and write operations are buffered (through the underlying Go channel), and the size
// of the buffer is given as `bufferSize`.
func NewTCPChannel(name string, to string, conns *Connections, bufferSize uint) (*TCPChannel, error) {
	readChan := make(chan interface{}, bufferSize)
	writeChan := make(chan interface{}, bufferSize)

	receiver := &Receiver{readChan}

	service := "TCPChannel_" + name
	if err := conns.ExposeImplementation(service, receiver); err != nil {
		return nil, err
	}

	tcpChannel := &TCPChannel{
		service:   service,
		conn:      conns.network[conns.processMap[to]],
		writeBuf:  []interface{}{},
		readChan:  readChan,
		writeChan: writeChan,
	}

	// wait for the other side of the channel to be ready to receive
	// data as well.
	tcpChannel.sync()

	// set up a Goroutine to handle sending of committed data over
	// the network
	go tcpChannel.SendMessages()

	return tcpChannel, nil
}

// Acquire is a no-op for TCP channels
func (tcpChannel *TCPChannel) Acquire(access ResourceAccess) error {
	return nil

}

// Read blocks until the next message is received through the channel,
// and returns it.
func (tcpChannel *TCPChannel) Read() (interface{}, error) {
	return <-tcpChannel.readChan, nil
}

// Write saves a message with the value given in a buffer to be sent
// later, when the channel is released.
func (tcpChannel *TCPChannel) Write(value interface{}) error {
	tcpChannel.writeBuf = append(tcpChannel.writeBuf, value)
	return nil
}

// Release sends each message given to Write() over the channel to the
// process listening on the receiving end.
func (tcpChannel *TCPChannel) Release() error {
	for _, msg := range tcpChannel.writeBuf {
		tcpChannel.writeChan <- msg
	}

	return nil
}

// Abort erases messages passed using Write and returns.
func (tcpChannel *TCPChannel) Abort() error {
	tcpChannel.writeBuf = []interface{}{}
	return nil
}

// Less implements ordering for channels. TCP channels are agnostic to
// ordering, and therefore always return `false`, not modifying their
// position in the collection of archetype resources.
func (ch *TCPChannel) Less(_ ArchetypeResource) bool {
	return false
}
