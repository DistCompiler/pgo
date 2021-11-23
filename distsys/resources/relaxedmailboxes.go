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

// RelaxedMailboxesMaker produces a distsys.ArchetypeResourceMaker for a
// collection of TCP mailboxes. It has the same guaranttees as tcp mailboxes,
// however, relaxed mailboxes don't follow 2PC semantics strictly same
// as TCP mailboxes. The main difference is that when a critical section
// successfully sends a message using relaxed remotes mailboxes (res.Write
// returns with no error), it will be not possible to abort that critical
// section anymore. Therefore, it's not always safe to use relaxed mailboxes
// instead of TCP mailboxes. It's only safe to use them in a critical section
// when there is at most one network send operation in the it and all
// succeeding operations in the critical section are guaranteed to commit
// successfully. Also with relaxed mailboxes, it's not safe have an await
// statement after a network send in a critical section.
// Note that we only the remove rollback support in the relaxed mailboxes and
// don't remove the timeout support. Reading from a relaxed local mailbox might
// timeout and it's OK. Also writing to a relaxed remote mailbox might timeout
// and it's fine too.
// With these restrictions, it is still possible to use a limited form of either
// statement, as long as await comes before the network write, and timing out on
// a network write is sequentially the last reason the either branch might fail.
func RelaxedMailboxesMaker(addressMappingFn MailboxesAddressMappingFn) distsys.ArchetypeResourceMaker {
	return IncrementalMapMaker(func(index tla.TLAValue) distsys.ArchetypeResourceMaker {
		typ, addr := addressMappingFn(index)
		switch typ {
		case MailboxesLocal:
			return relaxedMailboxesLocalMaker(addr)
		case MailboxesRemote:
			return relaxedMailboxesRemoteMaker(addr)
		default:
			panic(fmt.Errorf("invalid mailbox type %d for address %s: expected local or remote, which are %d or %d", typ, addr, MailboxesLocal, MailboxesRemote))
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
		msgChannel := make(chan tla.TLAValue, mailboxesReceiveChannelSize)
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
		// Reading in a separate goroutine to handle close semantics when
		// blocking on a connection read. Note that closing the listner does
		// not cause the connections to automatically return from a blocking
		// operations.
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
	case <-time.After(mailboxesReadTimeout):
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

func (res *relaxedMailboxesLocal) length() int {
	return len(res.readBacklog) + len(res.msgChannel)
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
		res.conn, err = net.DialTimeout("tcp", res.dialAddr, mailboxesDialTimeout)
		if err != nil {
			res.conn, res.connEncoder, res.connDecoder = nil, nil, nil
			log.Printf("failed to dial %s, aborting after %v: %v", res.dialAddr, mailboxesConnectionDroppedRetryDelay, err)
			time.Sleep(mailboxesConnectionDroppedRetryDelay)
			return distsys.ErrCriticalSectionAborted
		}
		// res.conn is wrapped; don't try to use it directly, or you might miss resetting the deadline!
		wrappedReaderWriter := makeReadWriterConnTimeout(res.conn, mailboxesDialTimeout)
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
