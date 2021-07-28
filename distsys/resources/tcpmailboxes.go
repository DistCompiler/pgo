package resources

import (
	"encoding/gob"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"io"
	"net"
	"time"
)

// Mailboxes as Archetype Resource
// -------------------------------

const (
	tcpNetworkBegin = iota
	tcpNetworkValue
	tcpNetworkPreCommit
	tcpNetworkCommit
)

type TCPMailboxKind int

const (
	TCPMailboxesLocal = iota
	TCPMailboxesRemote
)

const (
	tcpMailboxesReceiveChannelSize          = 100                   // TODO: this should be a configuration option
	tcpMailboxesTCPTimeout                  = 1 * time.Second       // TODO: same as above
	tcpMailboxesReadTimeout                 = 20 * time.Millisecond // TODO: same
	tcpMailboxesConnectionDroppedRetryDelay = 50 * time.Millisecond // TODO: same
)

// AddressMappingFn is responsible for translating the index, as in network[index] from distsys.TLAValue to a pair of
// TCPMailboxKind and address string, where the address string would be appropriate to pass to net.Listen("tcp", ...)
// or net.Dial("tcp", ...). It should return TCPMailboxesLocal if this node is to be the only listener, and it should
// return TCPMailboxesRemote if the mailbox is remote and should be dialed. This could potentially allow unusual setups
// where a single process "owns" more than one mailbox.
type AddressMappingFn func(distsys.TLAValue) (TCPMailboxKind, string)

// TCPMailboxesArchetypeResourceMaker produces a distsys.ArchetypeResourceMaker for a collection of TCP mailboxes.
// Each individual mailbox will match the following mapping macro, assuming exactly one process "reads" from it:
//
//     mapping macro TCPChannel {
//       read {
//           await Len($variable) > 0;
//           with (msg = Head($variable)) {
//               $variable := Tail($variable);
//               yield msg;
//           };
//       }
//
//       write {
//           await Len($variable) < BUFFER_SIZE;
//           yield Append($variable, $value);
//       }
//     }
//
// As is shown above, each mailbox should be a fully reliable FIFO channel, which these resources approximated
// via a lightweight TCP-based protocol optimised for optimistic data transmission. While the protocol should be
// extended to support reliability under crash recovery in the future, this behaviour is currently a stub.
//
// Note that BUFFER_SIZE is currently fixed to internal constant tcpMailboxesReceiveChannelSize, although precise numbers of
// in-flight messages may slightly exceed this number, as "reception" speculatively accepts one commit of messages before rate-limiting.
func TCPMailboxesArchetypeResourceMaker(addressMappingFn AddressMappingFn) distsys.ArchetypeResourceMaker {
	return IncrementalArchetypeMapResourceMaker(func(index distsys.TLAValue) distsys.ArchetypeResourceMaker {
		typ, addr := addressMappingFn(index)
		switch typ {
		case TCPMailboxesLocal:
			return tcpMailboxesLocalArchetypeResourceMaker(addr)
		case TCPMailboxesRemote:
			return tcpMailboxesRemoteArchetypeResourceMaker(addr)
		default:
			panic(fmt.Errorf("invalid TCP mailbox type %d for address %s: expected local or remote, which are %d or %d", typ, addr, TCPMailboxesLocal, TCPMailboxesRemote))
		}
	})
}

type tcpMailboxesLocalArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin
	listenAddr string
	msgChannel chan distsys.TLAValue

	readBacklog     []distsys.TLAValue
	readsInProgress []distsys.TLAValue
}

var _ distsys.ArchetypeResource = &tcpMailboxesLocalArchetypeResource{}

func tcpMailboxesLocalArchetypeResourceMaker(listenAddr string) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		msgChannel := make(chan distsys.TLAValue, tcpMailboxesReceiveChannelSize)
		listener, err := net.Listen("tcp", listenAddr)
		if err != nil {
			panic(fmt.Errorf("could not listen on address %s: %w", listenAddr, err))
		}
		res := &tcpMailboxesLocalArchetypeResource{
			listenAddr: listenAddr,
			msgChannel: msgChannel,
		}
		go res.listen(listener)

		return &tcpMailboxesLocalArchetypeResource{
			msgChannel: msgChannel,
		}
	})
}

func (res *tcpMailboxesLocalArchetypeResource) listen(listener net.Listener) {
	for {
		conn, err := listener.Accept()
		if err != nil {
			panic(fmt.Errorf("error listening on %s: %w", res.listenAddr, err))
		}
		go res.handleConn(conn)
	}
}

func (res *tcpMailboxesLocalArchetypeResource) handleConn(conn net.Conn) {
	var err error
	encoder := gob.NewEncoder(conn)
	decoder := gob.NewDecoder(conn)
	var localBuffer []distsys.TLAValue
	hasBegun := false
	for {
		if err != nil {
			fmt.Printf("network error, dropping connection: %s", err.Error())
			break
		}
		var tag int
		err = decoder.Decode(&tag)
		if err != nil {
			continue
		}

		switch tag {
		case tcpNetworkBegin:
			localBuffer = nil
			hasBegun = true
		case tcpNetworkValue:
			var value distsys.TLAValue
			err = decoder.Decode(&value)
			if err != nil {
				continue
			}
			localBuffer = append(localBuffer, value)
		case tcpNetworkPreCommit:
			err = encoder.Encode(struct{}{})
			if err != nil {
				continue
			}
		case tcpNetworkCommit:
			if !hasBegun {
				panic("a correct TCP mailbox exchange must always start with tcpMailboxBegin")
			}
			// FIXME: this is weak to restarts, but fixing that without proper context is really hard
			// at least, in this case the msgChannel will function as a rate limiter, so
			// crash-free operation shouldn't do anything weird

			// a restart-proof method would take advantage of TCP necessarily dropping the connection,
			// thus ending this connection, and log enough that everything important can be recovered
			err = encoder.Encode(false)
			if err != nil {
				continue
			}
			for _, elem := range localBuffer {
				res.msgChannel <- elem
			}
			localBuffer = nil
			hasBegun = false
		}
	}
	err = conn.Close()
	if err != nil {
		fmt.Printf("error closing connection: %v", err)
	}
}

func (res *tcpMailboxesLocalArchetypeResource) Abort() chan struct{} {
	res.readBacklog = append(res.readsInProgress, res.readBacklog...)
	res.readsInProgress = nil
	return nil
}

func (res *tcpMailboxesLocalArchetypeResource) PreCommit() chan error {
	return nil
}

func (res *tcpMailboxesLocalArchetypeResource) Commit() chan struct{} {
	res.readsInProgress = nil
	return nil
}

func (res *tcpMailboxesLocalArchetypeResource) ReadValue() (distsys.TLAValue, error) {
	// if a critical section previously aborted, already-read values will be here
	if len(res.readBacklog) > 0 {
		value := res.readBacklog[0]
		res.readBacklog[0] = distsys.TLAValue{} // ensure this TLAValue is null, otherwise it will dangle and prevent potential GC
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
		return distsys.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *tcpMailboxesLocalArchetypeResource) WriteValue(value distsys.TLAValue) error {
	panic(fmt.Errorf("attempted to write value %v to a local mailbox archetype resource", value))
}

type readWriterWithConnIdleTimeout struct {
	conn    net.Conn
	timeout time.Duration
}

var _ io.ReadWriter = &readWriterWithConnIdleTimeout{}

func makeReadWriterWithConnIdleTimeout(conn net.Conn, timeout time.Duration) readWriterWithConnIdleTimeout {
	return readWriterWithConnIdleTimeout{
		conn:    conn,
		timeout: timeout,
	}
}

func (rw readWriterWithConnIdleTimeout) Read(data []byte) (n int, err error) {
	err = rw.conn.SetReadDeadline(time.Now().Add(rw.timeout))
	if err != nil {
		panic(err)
	}
	return rw.conn.Read(data)
}

func (rw readWriterWithConnIdleTimeout) Write(data []byte) (n int, err error) {
	err = rw.conn.SetWriteDeadline(time.Now().Add(rw.timeout))
	if err != nil {
		panic(err)
	}
	return rw.conn.Write(data)
}

type tcpMailboxesRemoteArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin
	dialAddr string

	inCriticalSection bool
	conn              net.Conn
	connEncoder       *gob.Encoder
	connDecoder       *gob.Decoder
}

var _ distsys.ArchetypeResource = &tcpMailboxesRemoteArchetypeResource{}

func tcpMailboxesRemoteArchetypeResourceMaker(dialAddr string) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		return &tcpMailboxesRemoteArchetypeResource{
			dialAddr: dialAddr,
		}
	})
}

func (res *tcpMailboxesRemoteArchetypeResource) ensureConnection() error {
	if res.conn == nil {
		var err error
		res.conn, err = net.DialTimeout("tcp", res.dialAddr, tcpMailboxesTCPTimeout)
		if err != nil {
			res.conn, res.connEncoder, res.connDecoder = nil, nil, nil
			fmt.Printf("failed to dial %s, aborting after 50ms: %v", res.dialAddr, err)
			time.Sleep(tcpMailboxesConnectionDroppedRetryDelay)
			return distsys.ErrCriticalSectionAborted
		}
		// res.conn is wrapped; don't try to use it directly, or you might miss resetting the deadline!
		wrappedReaderWriter := makeReadWriterWithConnIdleTimeout(res.conn, tcpMailboxesTCPTimeout)
		res.connEncoder = gob.NewEncoder(wrappedReaderWriter)
		res.connDecoder = gob.NewDecoder(wrappedReaderWriter)
	}
	return nil
}

func (res *tcpMailboxesRemoteArchetypeResource) Abort() chan struct{} {
	// nothing to do; the remote end tolerates just starting over with no explanation
	res.inCriticalSection = false // but note to ourselves that we are starting over, so we re-send the begin record
	return nil
}

func (res *tcpMailboxesRemoteArchetypeResource) PreCommit() chan error {
	ch := make(chan error, 1)
	go func() {
		var err error
		handleError := func() {
			fmt.Printf("network error while performing pre-commit handshake, aborting: %v", err)
			res.conn = nil
			ch <- distsys.ErrCriticalSectionAborted
		}
		// be resilient to somehow reaching this without any sends
		if !res.inCriticalSection {
			res.inCriticalSection = true
			err = res.connEncoder.Encode(tcpNetworkBegin)
			if err != nil {
				handleError()
				return
			}
		}
		err = res.connEncoder.Encode(tcpNetworkPreCommit)
		if err != nil {
			handleError()
			return
		}
		var ack struct{}
		err = res.connDecoder.Decode(&ack)
		if err != nil {
			handleError()
			return
		}
		ch <- nil
	}()
	return ch
}

func (res *tcpMailboxesRemoteArchetypeResource) Commit() chan struct{} {
	ch := make(chan struct{}, 1)
	go func() {
		var err error
	outerLoop:
		for {
			if err != nil {
				panic(fmt.Errorf("network error during commit: %s", err))
			}
			err = res.ensureConnection()
			if err != nil {
				continue outerLoop
			}

			err = res.connEncoder.Encode(tcpNetworkCommit)
			if err != nil {
				continue outerLoop
			}
			var shouldResend bool
			err = res.connDecoder.Decode(&shouldResend)
			if err != nil {
				continue outerLoop
			}
			if shouldResend {
				panic("resending is not implemented")
			}
			res.inCriticalSection = false
			ch <- struct{}{}
			return
		}
	}()
	return ch
}

func (res *tcpMailboxesRemoteArchetypeResource) ReadValue() (distsys.TLAValue, error) {
	panic(fmt.Errorf("attempted to read from a remote mailbox archetype resource"))
}

func (res *tcpMailboxesRemoteArchetypeResource) WriteValue(value distsys.TLAValue) error {
	var err error
	handleError := func() error {
		fmt.Printf("network error during remote value write, aborting: %v", err)
		res.conn = nil
		return distsys.ErrCriticalSectionAborted
	}

	err = res.ensureConnection()
	if err != nil {
		return err
	}
	if !res.inCriticalSection {
		res.inCriticalSection = true
		err = res.connEncoder.Encode(tcpNetworkBegin)
		if err != nil {
			return handleError()
		}
	}
	err = res.connEncoder.Encode(tcpNetworkValue)
	if err != nil {
		return handleError()
	}
	err = res.connEncoder.Encode(&value)
	if err != nil {
		return handleError()
	}
	return nil
}
