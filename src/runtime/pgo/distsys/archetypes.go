package distsys

import (
	"fmt"
	"io/ioutil"
	"os"
	"path"
	"sort"
	"strings"
	"sync"
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
	Read() interface{}

	// Write receives a new value that the underlying resource is
	// supposed to be set to.
	Write(value interface{})

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

// ArchetypeResourceCollection represents archetype resources that are
// mapped via function calls in Modular PlusCal. Instead of using
// regular indexing operations, the Get allows implementations to
// provide custom archetype resources that depend on the value being
// indexed.
type ArchetypeResourceCollection interface {
	// Get receives as input the value being indexed on, and returns
	// the corresponding archetype resource. Note that different
	// implementations have specific requirements for the type of
	// `value`.
	//
	// Note that the resource returned by Get() must either be
	// stateless *or* Get() must return the same resource when called
	// with the same `value` argument
	Get(value interface{}) ArchetypeResource
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

////////////////////////////////////////////////
////         ARCHETYPE RESOURCES            ////
////////////////////////////////////////////////

// Global State as Archetype Resource
// ----------------------------------

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
func (v *GlobalVariable) Read() interface{} {
	return v.refs.Get(v.name)
}

// Write updates previously obtained references (via `Acquire`) to
// the value passed to this function.
func (v *GlobalVariable) Write(value interface{}) {
	v.writtenValue = value
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

// Mailboxes as Archetype Resource
// -------------------------------

// Receiver represents the interface exposed by mailboxes. When data
// is received by a process, the data is sent across the underlying Go
// channel and can be read on calls to 'Read'.
type Receiver struct {
	ch chan interface{}
}

// Receive receives data from the other end of the channel.
func (r *Receiver) Receive(val *interface{}, ok *bool) error {
	r.ch <- *val
	*ok = true

	return nil
}

// Mailbox is an implementation of `ArchetypeResource` that provides
// an abstraction of a queue of messages that are waiting to be
// processed by some process. Other processes compiled by PGo are able
// to communicate with the running process by means of sending
// messages (Write() calls); processes may then read the next message
// available in their queues.
type Mailbox struct {
	name          string            // internal name exposed via RPC
	selfName      string            // identifier of the process that created the reference
	configuration map[string]string // configuration of the system (PlusCal process -> IP address)
	conns         *Connections      // the set of connections to nodes within the system
	writeBuf      []interface{}     // messages waiting to be sent when the channel is released
	readChan      chan interface{}  // reads are buffered through Go channels
	writeChan     chan interface{}  // writes are buffered through Go channels
}

// service returns the name of the RPC service associated with this
// mailbox.
func (mbox *Mailbox) service() string {
	return "Mailbox_" + mbox.name
}

func (mbox *Mailbox) call(function string, args interface{}, ok *bool) error {
	fName := mbox.service() + "." + function
	addr := mbox.configuration[mbox.name]
	return mbox.conns.GetConnection(addr).Call(fName, &args, ok)
}

// SendMessages will wait indefinitely for data coming from `writeChan` and
// actually send the data over to the network.
func (mbox *Mailbox) SendMessages() {
	var ok bool

	for msg := range mbox.writeChan {
		if err := mbox.call("Receive", msg, &ok); err != nil {
			fmt.Printf("Error! %v\n", err)
		}
	}
}

// MailboxRef represents a reference to some mailbox. It can be local
// (if the process 'id' is the same as the mailbox being referenced),
// or remote (if they are different).
//
// Processes can send messages to other processes by appending to
// their message queues.
//
// The message queue (mailbox) contains at most 'bufferSize'
// elements. Sending a message to a process with a full queue causes
// the requester to block until sufficient space in the queue is
// available.
func MailboxRef(name string, conns *Connections, configuration map[string]string, id string, bufferSize uint) (*Mailbox, error) {
	mbox := &Mailbox{
		name:          name,
		selfName:      id,
		configuration: configuration,
		conns:         conns,
		writeBuf:      []interface{}{},
		writeChan:     make(chan interface{}, bufferSize),
	}

	// if the reference is for the mailbox of the current process,
	// expose RPC calls that allow other processes to send messages to
	// it.
	if name == id {
		readChan := make(chan interface{}, bufferSize)
		receiver := &Receiver{readChan}
		mbox.readChan = readChan

		if err := conns.ExposeImplementation(mbox.service(), receiver); err != nil {
			return nil, err
		}
	}

	// set up a Goroutine to handle sending of committed data over
	// the network
	go mbox.SendMessages()

	return mbox, nil
}

// Acquire is a no-op for mailboxes
func (_ *Mailbox) Acquire(_ ResourceAccess) error {
	return nil
}

// Read blocks until there is at least one message in the message
// queue, and returns it. It is enforced that processes can only read
// messages from their own mailboxes.
func (mbox *Mailbox) Read() interface{} {
	if mbox.name != mbox.selfName {
		panic(fmt.Sprintf("Tried to read non-local mailbox %s (attempted by %s)", mbox.name, mbox.selfName))
	}

	return <-mbox.readChan
}

// Write saves a message with the value given in a buffer to be sent
// later, when the channel is released.
func (mbox *Mailbox) Write(value interface{}) {
	if mbox.name == mbox.selfName {
		panic(fmt.Sprintf("Tried to send message to local mailbox (attempted by %s)", mbox.selfName))
	}

	mbox.writeBuf = append(mbox.writeBuf, value)
}

// Release sends each message given to Write() to the destination
// mailbox.
func (mbox *Mailbox) Release() error {
	for _, msg := range mbox.writeBuf {
		mbox.writeChan <- msg
	}

	mbox.writeBuf = []interface{}{}
	return nil
}

// Abort erases messages passed using Write and returns.
func (mbox *Mailbox) Abort() error {
	mbox.writeBuf = []interface{}{}
	return nil
}

// Less implements ordering for channels. TCP channels are agnostic to
// ordering, and therefore always return `false`, not modifying their
// position in the collection of archetype resources.
func (_ *Mailbox) Less(_ ArchetypeResource) bool {
	return false
}

// Local Channels as Archetype Resource
// ------------------------------------

// LocalChannelResource represents an archetype resource backed by a
// regular Go channel. The main use-case for channels as resources is
// being able to control the execution of long-running archetypes.
// Parameters can be sent via channels and the result of the
// computation performed can also be transmitted via channels.
type LocalChannelResource struct {
	ch       chan interface{} // the underlying Go channel
	lock     sync.Mutex       // guarantees access to the underlying channel is exclusive
	readBuf  []interface{}    // keeps track of read values
	writeBuf []interface{}    // values written to the channel; sent when the resource is released
}

// NewLocalChannel creates a LocalChannelResource. The caller does not
// need to know about the underlying Go channel.
func NewLocalChannel() *LocalChannelResource {
	return &LocalChannelResource{
		ch:       make(chan interface{}),
		readBuf:  []interface{}{},
		writeBuf: []interface{}{},
	}
}

// Acquire is a no-op for local channels.
func (localCh *LocalChannelResource) Acquire(access ResourceAccess) error {
	localCh.lock.Lock()
	return nil
}

// Read waits for data to be available in the underlying Go channel.
func (localCh *LocalChannelResource) Read() interface{} {
	val := <-localCh.ch
	localCh.readBuf = append(localCh.readBuf, val)

	return val
}

// Write sends a value over the channel.
func (localCh *LocalChannelResource) Write(value interface{}) {
	localCh.writeBuf = append(localCh.writeBuf, value)
}

// Release writes values written to the channel while the resource was
// acquired.
func (localCh *LocalChannelResource) Release() error {
	// send written values over the channel
	for _, val := range localCh.writeBuf {
		localCh.ch <- val
	}

	// erase read and written values
	localCh.readBuf = []interface{}{}
	localCh.writeBuf = []interface{}{}

	// release access to the channel
	localCh.lock.Unlock()
	return nil
}

// Abort undoes any read performed while the channel was acquired
func (localCh *LocalChannelResource) Abort() error {
	// reverse read values
	for i := len(localCh.readBuf)/2 - 1; i >= 0; i-- {
		opp := len(localCh.readBuf) - 1 - i
		localCh.readBuf[i], localCh.readBuf[opp] = localCh.readBuf[opp], localCh.readBuf[i]
	}

	// send the read values back
	for _, val := range localCh.readBuf {
		localCh.ch <- val
	}

	// erase read and written values
	localCh.readBuf = []interface{}{}
	localCh.writeBuf = []interface{}{}

	// release access to the channel
	localCh.lock.Unlock()
	return nil
}

// Less implements ordering. Local channels are agnostic to ordering.
func (localCh *LocalChannelResource) Less(_ ArchetypeResource) bool {
	return false
}

// Send writes data to the channel so that the receiving end can see
// it (on a Read call). This is supposed to be called by code outside
// archetypes.
func (localCh *LocalChannelResource) Send(value interface{}) {
	localCh.ch <- value
}

// Receive reads data from the channel so that results can be
// collected. This is supposed to be called by code outside
// archetypes.
func (localCh *LocalChannelResource) Receive() interface{} {
	return <-localCh.ch
}

// Files as Archetype Resource
// ---------------------------

// FileResource implements files in the system as archetype resources.
type FileResource struct {
	path     string   // absolute path to the file
	fd       *os.File // the underlying file descriptor.
	contents []byte   // if the file has been previously read or written, hold contents in buffer
	dirty    bool     // whether the file has been written
}

// NewFileResource creates a FileResource for the file under `path`.
func NewFileResource(path string) *FileResource {
	return &FileResource{
		path:     path,
		contents: nil,
		dirty:    false,
	}
}

// Acquire attempts to open the underlying file with appropriate
// permissions.  Returns an error if it cannot be done.
func (file *FileResource) Acquire(access ResourceAccess) error {
	perms := os.O_RDONLY
	if access&WRITE_ACCESS != 0 {
		perms = os.O_RDWR
	}

	fd, err := os.OpenFile(file.path, perms|os.O_CREATE, 0644)
	if err != nil {
		return err
	}

	file.fd = fd
	return nil
}

// Read returns a buffer with all the contents of the underlying file.
// Panics if reading there is a an error reading the file.
func (file *FileResource) Read() interface{} {
	if file.contents == nil {
		data, err := ioutil.ReadAll(file.fd)
		if err != nil {
			panic(err)
		}

		file.contents = data
	}

	return file.contents
}

// Write saves the value to be written in an internal
// buffer. Subsequent Read() calls will return the newly written
// value. Note that `value` *must* be []byte.
func (file *FileResource) Write(value interface{}) {
	file.contents = value.([]byte)
	file.dirty = true
}

// Release writes any previously written contents to the underlying
// file, and closes it.
func (file *FileResource) Release() error {
	if file.fd != nil {
		if file.dirty {
			_, err := file.fd.Write(file.contents)

			if err != nil {
				return err
			}
		}

		return file.fd.Close()
	}

	return nil
}

// Abort closes the underlying file
func (file *FileResource) Abort() error {
	return file.fd.Close()
}

// Less implements ordering. File resources are agnostic to ordering.
func (file *FileResource) Less(_ ArchetypeResource) bool {
	return false
}

// Locally Shared Variables as Archetype Resources
// -----------------------------------------------

// LocallySharedResource represents some value that is shared only locally,
// i.e., within the same Go process.
type LocallySharedResource struct {
	val        interface{} // the value being shared
	writtenBuf interface{} // buffer of previous writes
	lock       sync.Mutex  // mutex to guarantee exclusive access
}

// NewLocallySharedResource creates a new shared resource that can be
// used as a resource archetype
func NewLocallySharedResource(val interface{}) *LocallySharedResource {
	return &LocallySharedResource{
		val:        val,
		writtenBuf: nil,
	}
}

// Acquire locks the resource for exclusive access
func (resource *LocallySharedResource) Acquire(_ ResourceAccess) error {
	resource.lock.Lock()
	return nil
}

// Read returns the current value of the resource
func (resource *LocallySharedResource) Read() interface{} {
	if resource.writtenBuf != nil {
		return resource.writtenBuf
	}

	return resource.val
}

// Write updates the value of the underlying shared resource
func (resource *LocallySharedResource) Write(value interface{}) {
	resource.writtenBuf = value
}

// Release writes any written value to the underlying shared value and
// returns
func (resource *LocallySharedResource) Release() error {
	if resource.writtenBuf != nil {
		resource.val = resource.writtenBuf
	}

	resource.lock.Unlock()
	return nil
}

// Abort erases any values passed using Write and returns.
func (resource *LocallySharedResource) Abort() error {
	resource.writtenBuf = nil
	resource.lock.Unlock()

	return nil
}

// Less is a no-op. Locally shared resources are agnostic to ordering.
func (_ *LocallySharedResource) Less(_ ArchetypeResource) bool {
	return false
}

/////////////////////////////////////////////////////////////////////////
////            ARCHETYPE RESOURCE COLLECTIONS                      ////
///////////////////////////////////////////////////////////////////////

// Slices as Archetype Resource Collections
// ----------------------------------------

// ArchetypeResourceSlice implements implements an
// ArchetypeResourceCollection by mapping Get calls as straightforward
// indexing operations on the underlying slice.
type ArchetypeResourceSlice []ArchetypeResource

// Get returns the archetype resource at a given index. The `value`
// passed must be an integer.
func (slice ArchetypeResourceSlice) Get(value interface{}) ArchetypeResource {
	index := value.(int)
	return slice[index]
}

// File System Directories as Archetype Resource Collections
// ---------------------------------------------------------

// FileSystemDirectory represents an archetype resource that makes the
// files in a certain directory available, implementing the
// ArchetypeResourceCollection interface
type FileSystemDirectory struct {
	root      string                   // path to the directory under which files will be accessed
	resources map[string]*FileResource // maps previously retrieved files
}

// NewFileSystemDirectory returns an implementation of
// ArchetypeResourceCollection for accessing files under a root
// directory.
func NewFileSystemDirectory(root string) *FileSystemDirectory {
	return &FileSystemDirectory{
		root:      root,
		resources: map[string]*FileResource{},
	}
}

// Get returns the archetype resource file corresponding to the path
// (relative to the root) given as argument. The `value` given must be
// a string.
func (dir *FileSystemDirectory) Get(value interface{}) ArchetypeResource {
	relativePath := value.(string)

	if _, ok := dir.resources[relativePath]; !ok {
		absolutePath := path.Join(string(dir.root), relativePath)
		dir.resources[relativePath] = NewFileResource(absolutePath)
	}

	return dir.resources[relativePath]
}
