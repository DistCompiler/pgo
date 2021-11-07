package resources

import (
	"encoding/gob"
	"fmt"
	"io"
	"log"
	"net"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func RelaxedMailboxesMaker(addressMappingFn TCPMailboxesAddressMappingFn) distsys.ArchetypeResourceMaker {
	return IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
		typ, addr := addressMappingFn(index)
		switch typ {
		case TCPMailboxesLocal:
			return relaxedMailboxesLocalMaker(addr)
		case TCPMailboxesRemote:
			return relaxedMailboxesRemoteMaker(addr)
		default:
			panic(fmt.Errorf("invalid TCP mailbox type %d for address %s: expected local or remote, which are %d or %d", typ, addr, TCPMailboxesLocal, TCPMailboxesRemote))
		}
	})
}

type relaxedMailboxesLocal struct {
	distsys.ArchetypeResourceLeafMixin
	listenAddr string
	msgChannel chan tla.TLAValue
	listener   net.Listener

	readBacklog     []tla.TLAValue
	readsInProgress []tla.TLAValue

	done chan struct{}
}

var _ distsys.ArchetypeResource = &relaxedMailboxesLocal{}

func relaxedMailboxesLocalMaker(listenAddr string) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		msgChannel := make(chan tla.TLAValue, tcpMailboxesReceiveChannelSize)
		listener, err := net.Listen("tcp", listenAddr)
		if err != nil {
			panic(fmt.Errorf("could not listen on address %s: %w", listenAddr, err))
		}
		log.Printf("started listening on: %s", listenAddr)
		res := &relaxedMailboxesLocal{
			listenAddr: listenAddr,
			msgChannel: msgChannel,
			listener:   listener,
			done:       make(chan struct{}),
		}
		go res.listen()

		return res
	})
}

func (res *relaxedMailboxesLocal) listen() {
	for {
		conn, err := res.listener.Accept()
		if err != nil {
			select {
			case <-res.done:
				return
			default:
				panic(fmt.Errorf("error listening on %s: %w", res.listenAddr, err))
			}
		}
		go res.handleConn(conn)
	}
}

func (res *relaxedMailboxesLocal) handleConn(conn net.Conn) {
	defer func() {
		err := conn.Close()
		if err != nil {
			log.Printf("error closing connection: %v", err)
		}
	}()

	var err error
	decoder := gob.NewDecoder(conn)
	for {
		if err != nil {
			select {
			case <-res.done:
			default:
				if err != io.EOF {
					log.Printf("network error during handleConn, dropping connection: %s", err)
				}
			}
			return
		}
		var value tla.TLAValue
		errCh := make(chan error)
		go func() {
			errCh <- decoder.Decode(&value)
		}()
		select {
		case err = <-errCh:
		case <-res.done:
			return
		}
		if err != nil {
			continue
		}

		res.msgChannel <- value
	}
}

func (res *relaxedMailboxesLocal) Abort() chan struct{} {
	res.readBacklog = append(res.readsInProgress, res.readBacklog...)
	res.readsInProgress = nil
	return nil
}

func (res *relaxedMailboxesLocal) PreCommit() chan error {
	return nil
}

func (res *relaxedMailboxesLocal) Commit() chan struct{} {
	res.readsInProgress = nil
	return nil
}

func (res *relaxedMailboxesLocal) ReadValue() (tla.TLAValue, error) {
	// if a critical section previously aborted, already-read values will be here
	if len(res.readBacklog) > 0 {
		value := res.readBacklog[0]
		res.readBacklog[0] = tla.TLAValue{} // ensure this TLAValue is null, otherwise it will dangle and prevent potential GC
		res.readBacklog = res.readBacklog[1:]
		res.readsInProgress = append(res.readsInProgress, value)
		return value, nil
	}

	// otherwise, either pull a notification + atomically read a value from the buffer, or time out
	select {
	case msg := <-res.msgChannel:
		res.readsInProgress = append(res.readsInProgress, msg)
		return msg, nil
	case <-time.After(tcpMailboxesReadTimeout):
		return tla.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *relaxedMailboxesLocal) WriteValue(value tla.TLAValue) error {
	panic(fmt.Errorf("attempted to write value %v to a local mailbox archetype resource", value))
}

func (res *relaxedMailboxesLocal) Close() error {
	// signal to close the listener and active connections
	close(res.done)

	var err error
	if res.listener != nil {
		err = res.listener.Close()
	}
	return err
}

type relaxedMailboxesRemote struct {
	distsys.ArchetypeResourceLeafMixin
	dialAddr string

	conn        net.Conn
	connEncoder *gob.Encoder
	connDecoder *gob.Decoder
	hasSent     bool
}

var _ distsys.ArchetypeResource = &tcpMailboxesRemote{}

func relaxedMailboxesRemoteMaker(dialAddr string) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &relaxedMailboxesRemote{
			dialAddr: dialAddr,
		}
	})
}

func (res *relaxedMailboxesRemote) ensureConnection() error {
	if res.conn == nil {
		var err error
		res.conn, err = net.DialTimeout("tcp", res.dialAddr, tcpMailboxesTCPTimeout)
		if err != nil {
			res.conn, res.connEncoder, res.connDecoder = nil, nil, nil
			log.Printf("failed to dial %s, aborting after %v: %v", res.dialAddr, tcpMailboxesConnectionDroppedRetryDelay, err)
			time.Sleep(tcpMailboxesConnectionDroppedRetryDelay)
			return distsys.ErrCriticalSectionAborted
		}
		// res.conn is wrapped; don't try to use it directly, or you might miss resetting the deadline!
		wrappedReaderWriter := makeReadWriterConnTimeout(res.conn, tcpMailboxesTCPTimeout)
		res.connEncoder = gob.NewEncoder(wrappedReaderWriter)
		res.connDecoder = gob.NewDecoder(wrappedReaderWriter)
	}
	return nil
}

func (res *relaxedMailboxesRemote) Abort() chan struct{} {
	if res.hasSent {
		panic("relaxedMailboxesRemote: cannot abort a critical section with a sent message.")
	}
	return nil
}

func (res *relaxedMailboxesRemote) PreCommit() chan error {
	return nil
}

func (res *relaxedMailboxesRemote) Commit() chan struct{} {
	return nil
}

func (res *relaxedMailboxesRemote) ReadValue() (tla.TLAValue, error) {
	panic(fmt.Errorf("attempted to read from a remote mailbox archetype resource"))
}

func (res *relaxedMailboxesRemote) WriteValue(value tla.TLAValue) error {
	var err error
	handleError := func() error {
		log.Printf("network error during remote value write, aborting: %v", err)
		// close the connection to close the allocated file descriptors
		if err := res.conn.Close(); err != nil {
			log.Printf("error in closing conn: %s", err)
		}
		res.conn = nil
		return distsys.ErrCriticalSectionAborted
	}

	err = res.ensureConnection()
	if err != nil {
		return err
	}
	err = res.connEncoder.Encode(&value)
	if err != nil {
		return handleError()
	}
	res.hasSent = true
	return nil
}

func (res *relaxedMailboxesRemote) Close() error {
	var err error
	if res.conn != nil {
		err = res.conn.Close()
	}
	return err
}
