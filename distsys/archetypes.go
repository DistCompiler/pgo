package distsys

import (
	"container/list"
	"encoding/gob"
	"errors"
	"io"
	"net"
	"time"
)

var Aborted = errors.New("MPCal critical section aborted")

type ArchetypeResource interface {
	Abort()
	PreCommit() error
	Commit()
	ReadValue() (TLAValue, error)
	WriteValue(value TLAValue) error
	Index(index TLAValue) (ArchetypeResource, error)
}

type ArchetypeResourceLeafMixin struct{}

var ArchetypeResourceLeafIndexedError = errors.New("internal error: attempted to index a leaf archetype resource")

func (ArchetypeResourceLeafMixin) Index(TLAValue) (ArchetypeResource, error) {
	return nil, ArchetypeResourceLeafIndexedError
}

type ArchetypeResourceMapMixin struct{}

var ArchetypeResourceMapReadWriteError = errors.New("internal error: attempted to read/write a map archetype resource")

func (ArchetypeResourceMapMixin) ReadValue() (TLAValue, error) {
	return TLAValue{}, ArchetypeResourceMapReadWriteError
}

func (ArchetypeResourceMapMixin) WriteValue(TLAValue) error {
	return ArchetypeResourceMapReadWriteError
}

////////////////////////////////////////////////
////         ARCHETYPE RESOURCES            ////
////////////////////////////////////////////////

// A bare-bones resource: just holds and buffers a TLAValue
// --------------------------------------------------------

type LocalArchetypeResource struct {
	ArchetypeResourceLeafMixin
	hasOldValue bool
	value, oldValue TLAValue
}

func NewLocalArchetypeResource(value TLAValue) *LocalArchetypeResource {
	return &LocalArchetypeResource{
		hasOldValue: false,
		value: value,
	}
}

func (res *LocalArchetypeResource) Abort() {
	if res.hasOldValue {
		res.value = res.oldValue
		res.hasOldValue = false
		res.oldValue = TLAValue{}
	}
}

func (res *LocalArchetypeResource) PreCommit() error {
	return nil
}

func (res *LocalArchetypeResource) Commit() {
	res.hasOldValue = false
	res.oldValue = TLAValue{}
}

func (res *LocalArchetypeResource) ReadValue() (TLAValue, error) {
	return res.value, nil
}

func (res *LocalArchetypeResource) WriteValue(value TLAValue) error {
	if !res.hasOldValue {
		res.oldValue = res.value
		res.hasOldValue = true
	}
	res.value = value
	return nil
}

// Global State as Archetype Resource
// ----------------------------------

// TODO: recreate

// Mailboxes as Archetype Resource
// -------------------------------

type TCPMailboxesArchetypeResource struct {
	ArchetypeResourceMapMixin
	Listener net.Listener
	inputChannel chan TLAValue
	buffer *list.List
	elementsRead []TLAValue
}

var _ ArchetypeResource = &TCPMailboxesArchetypeResource{}

const (
	tcpNetworkBegin = iota
	tcpNetworkValue
	tcpNetworkPreCommit
	tcpNetworkPreCommitAck
	tcpNetworkCommit
)

type tcpNetworkMsg struct {
	Tag int
	Value TLAValue
}

func NewTCPMailboxesArchetypeResource(address string) (res *TCPMailboxesArchetypeResource, err error) {
	listener, err := net.Listen("tcp", address)
	if err != nil {
		return
	}
	inputChannel := make(chan TLAValue, 100)
	go func() {
		for {
			conn, err := listener.Accept()
			if err != nil {
				break
			}
			go func() {
				decoder := gob.NewDecoder(conn)
				encoder := gob.NewEncoder(conn)
				var msgBuffer []TLAValue
				for {
					var msg tcpNetworkMsg
					err := decoder.Decode(&msg)
					if err != nil {
						if errors.Is(err, io.EOF) || errors.Is(err, io.ErrUnexpectedEOF) {
							return
						}
						panic(err) // TODO: actually handle this
					}
					switch msg.Tag {
					case tcpNetworkBegin:
						msgBuffer = nil
					case tcpNetworkValue:
						msgBuffer = append(msgBuffer, msg.Value)
					case tcpNetworkPreCommit:
						err = encoder.Encode(&tcpNetworkMsg{Tag: tcpNetworkPreCommitAck})
						if err != nil {
							panic(err)
						}
					case tcpNetworkCommit:
						for _, msg := range msgBuffer {
							inputChannel <- msg
						}
						msgBuffer = nil
					default:
						panic("???")
					}
				}
			}()
		}
	}()
	return &TCPMailboxesArchetypeResource{
		Listener: listener,
		inputChannel: inputChannel,
		buffer: list.New(),
	}, nil
}

func (res *TCPMailboxesArchetypeResource) pumpNetwork() error {
	if res.buffer.Len() == 0 {
		select {
		case nextElem := <-res.inputChannel:
			res.buffer.PushBack(nextElem)
			return nil
		case <-time.After(20 * time.Millisecond):
			return Aborted
		}
	} else {
		return nil
	}
}

func (res *TCPMailboxesArchetypeResource) Index(index TLAValue) (ArchetypeResource, error) {
	panic("???")
}

func (res *TCPMailboxesArchetypeResource) Abort() {
	for _, elem := range res.elementsRead {
		res.buffer.PushFront(elem)
	}
	res.elementsRead = nil
}

func (res *TCPMailboxesArchetypeResource) PreCommit() error {
	return nil
}

func (res *TCPMailboxesArchetypeResource) Commit() {
	res.elementsRead = nil
}

type TCPMailboxRemoteArchetypeResource struct {
	ArchetypeResourceLeafMixin
	hasBegun bool
	remoteAddress string
	conn net.Conn
	encoder gob.Encoder
	decoder gob.Decoder
}

var _ ArchetypeResource = &TCPMailboxRemoteArchetypeResource{}

func (res *TCPMailboxRemoteArchetypeResource) ReadValue() (TLAValue, error) {
	return TLAValue{}, errors.New("tried to read from non-local TCP mailbox")
}

func (res *TCPMailboxRemoteArchetypeResource) WriteValue(value TLAValue) (err error) {
	if !res.hasBegun {
		if res.conn == nil {
			res.conn, err = net.Dial("tcp", res.remoteAddress)
			if err != nil {
				return err
			}
		}
		err = res.encoder.Encode(tcpNetworkMsg{Tag: tcpNetworkBegin})
		if err != nil {
			return err
		}
	}
	return res.encoder.Encode(tcpNetworkMsg{Tag: tcpNetworkValue, Value: value})
}

func (res *TCPMailboxRemoteArchetypeResource) Abort() {
	res.hasBegun = false
}

func (res *TCPMailboxRemoteArchetypeResource) PreCommit() error {
	err := res.encoder.Encode(tcpNetworkMsg{Tag: tcpNetworkPreCommit})
	if err != nil {
		res.conn = nil
		return Aborted
	}
	var msg tcpNetworkMsg
	err = res.decoder.Decode(&msg)
	if msg.Tag != tcpNetworkPreCommitAck {
		panic("???")
	}
	return nil
}

func (res *TCPMailboxRemoteArchetypeResource) Commit() {
	res.hasBegun = false
	err := res.encoder.Encode(tcpNetworkMsg{Tag: tcpNetworkCommit})
	if err != nil {
		panic(err) // can't support this failure...
	}
}

type TCPMailboxLocalArchetypeResource struct {
	ArchetypeResourceLeafMixin
}
