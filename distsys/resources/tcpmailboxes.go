package resources

import (
	"encoding/gob"
	"fmt"
	"io"
	"log"
	"net"
	"sync"
	"time"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

// Mailboxes as Archetype Resource
// -------------------------------

const (
	tcpNetworkBegin = iota
	tcpNetworkValue
	tcpNetworkPreCommit
	tcpNetworkCommit
)

// NewTCPMailboxes produces a distsys.ArchetypeResource for a collection of TCP mailboxes.
// Each individual mailbox will match the following mapping macro, assuming exactly one process "reads" from it:
//
//    \* assuming initially that:
//    \* $variable := [queue |-> <<>> (* empty buffer *), enabled |-> TRUE (* process running *)]
//
//    mapping macro LimitedBufferReliableFIFOLink {
//        read {
//        assert $variable.enabled;
//            await Len($variable.queue) > 0;
//            with (msg = Head($variable.queue)) {
//                $variable.queue := Tail($variable.queue);
//                yield msg;
//            };
//        }
//
//        write {
//            await Len($variable.queue) < BUFFER_SIZE /\ $variable.enabled;
//            yield [queue |-> Append($variable.queue, $value), enabled |-> $variable.enabled];
//        }
//    }
//
// As is shown above, each mailbox should be a fully reliable FIFO channel, which these resources approximated
// via a lightweight TCP-based protocol optimised for optimistic data transmission. While the protocol should be
// extended to support reliability under crash recovery in the future, this behaviour is currently a stub.
//
// Note that BUFFER_SIZE is currently fixed to internal constant tcpMailboxesReceiveChannelSize, although precise numbers of
// in-flight messages may slightly exceed this number, as "reception" speculatively accepts one commit of messages before rate-limiting.
//
// Note also that this protocol is not live, with respect to Commit. All other ops will recover from timeouts via aborts,
// which will not be visible and will not take infinitely long. Commit is the exception, as it _must complete_ for semantics
// to be preserved, or it would be possible to observe partial effects of critical sections.
func NewTCPMailboxes(addressMappingFn MailboxesAddressMappingFn, opts ...MailboxesOption) *Mailboxes {
	return &Mailboxes{
		NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
			typ, addr := addressMappingFn(index)
			switch typ {
			case MailboxesLocal:
				return newTCPMailboxesLocal(addr, opts...)
			case MailboxesRemote:
				return newTCPMailboxesRemote(addr, opts...)
			default:
				panic(fmt.Errorf("invalid mailbox type %d for address %s: expected local or remote, which are %d or %d", typ, addr, MailboxesLocal, MailboxesRemote))
			}
		}),
	}
}

type msgRecord struct {
	value tla.Value
	clock trace.VClock
}

type recvRecord struct {
	values []tla.Value
	clock  trace.VClock
}

type tcpMailboxesLocal struct {
	distsys.ArchetypeResourceLeafMixin
	listenAddr string
	msgChannel chan recvRecord
	listener   net.Listener

	readBacklog     []msgRecord
	readsInProgress []msgRecord

	done chan struct{}

	// lock protects closing and synchronizes wg.Add() and wg.Wait(). If
	// closing is true, then there will be no more wg.Add(). At this point,
	// using wg.Wait() is safe.
	lock    sync.RWMutex
	closing bool
	//wg      sync.WaitGroup // contains the number of responded pre-commits that we haven't responded to their commits yet.

	config mailboxesConfig
}

var _ distsys.ArchetypeResource = &tcpMailboxesLocal{}

func newTCPMailboxesLocal(listenAddr string, opts ...MailboxesOption) distsys.ArchetypeResource {
	config := defaultMailboxesConfig
	for _, opt := range opts {
		opt(config)
	}

	msgChannel := make(chan recvRecord, config.receiveChanSize)
	listener, err := net.Listen("tcp", listenAddr)
	if err != nil {
		panic(fmt.Errorf("could not listen on address %s: %w", listenAddr, err))
	}
	log.Printf("started listening on: %s", listenAddr)
	res := &tcpMailboxesLocal{
		listenAddr: listenAddr,
		msgChannel: msgChannel,
		listener:   listener,
		done:       make(chan struct{}),
		closing:    false,
		config:     config,
	}
	go res.listen()

	return res
}

func (res *tcpMailboxesLocal) listen() {
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

func (res *tcpMailboxesLocal) handleConn(conn net.Conn) {
	defer func() {
		err := conn.Close()
		if err != nil {
			log.Printf("error closing connection: %v", err)
		}
	}()

	var err error
	encoder := gob.NewEncoder(conn)
	decoder := gob.NewDecoder(conn)
	var localBuffer []tla.Value
	hasBegun := false
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
		var tag int
		errCh := make(chan error)
		// Reading in a separate goroutine to handle close semantics when
		// blocking on a connection read. Note that closing the listener does
		// not cause the connections to automatically return from a blocking
		// operations.
		go func() {
			errCh <- decoder.Decode(&tag)
		}()
		select {
		case err = <-errCh:
		case <-res.done:
			return
		}
		if err != nil {
			continue
		}

		switch tag {
		case tcpNetworkBegin:
			localBuffer = nil
			hasBegun = true
		case tcpNetworkValue:
			if !hasBegun {
				panic("a correct TCP mailbox exchange must always start with tcpMailboxBegin")
			}
			var value tla.Value
			func() {
				res.lock.RLock()
				defer res.lock.RUnlock()
				if res.closing {
					return
				}
				err = decoder.Decode(&value)
				if err != nil {
					return
				}
				localBuffer = append(localBuffer, value)
			}()
		case tcpNetworkPreCommit:
			if !hasBegun {
				panic("a correct TCP mailbox exchange must always start with tcpMailboxBegin")
			}
			func() {
				res.lock.RLock()
				defer res.lock.RUnlock()
				if res.closing {
					return
				}
				err = encoder.Encode(struct{}{})
				if err != nil {
					return
				}
				//res.wg.Add(1)
			}()
		case tcpNetworkCommit:
			if !hasBegun {
				panic("a correct TCP mailbox exchange must always start with tcpMailboxBegin")
			}
			var clock trace.VClock
			err = decoder.Decode(&clock)
			if err != nil {
				continue
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
			//res.wg.Done()
			if len(localBuffer) > 0 {
				res.msgChannel <- recvRecord{
					clock:  clock,
					values: localBuffer,
				}
			}
			localBuffer = nil
			hasBegun = false
		}
	}
}

func (res *tcpMailboxesLocal) Abort() chan struct{} {
	res.readBacklog = append(res.readsInProgress, res.readBacklog...)
	res.readsInProgress = nil
	return nil
}

func (res *tcpMailboxesLocal) PreCommit() chan error {
	return nil
}

func (res *tcpMailboxesLocal) Commit() chan struct{} {
	res.readsInProgress = nil
	return nil
}

func (res *tcpMailboxesLocal) ReadValue() (tla.Value, error) {
	// if a critical section previously aborted, already-read values will be here
	if len(res.readBacklog) > 0 {
		record := res.readBacklog[0]
		res.readBacklog[0] = msgRecord{} // ensure this reference is null, otherwise it will dangle and prevent potential GC
		res.readBacklog = res.readBacklog[1:]
		res.readsInProgress = append(res.readsInProgress, record)
		return record.value, nil
	}

	// otherwise, either pull a notification + atomically read a value from the buffer, or time out
	select {
	case record := <-res.msgChannel:
		valueRead := record.values[0]
		for _, value := range record.values[1:] {
			res.readBacklog = append(res.readBacklog, msgRecord{
				clock: record.clock,
				value: value,
			})
		}
		res.readsInProgress = append(res.readsInProgress, msgRecord{
			clock: record.clock,
			value: valueRead,
		})
		return valueRead, nil
	case <-time.After(res.config.readTimeout):
		return tla.Value{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *tcpMailboxesLocal) WriteValue(value tla.Value) error {
	panic(fmt.Errorf("attempted to write value %v to a local mailbox archetype resource", value))
}

func (res *tcpMailboxesLocal) VClockHint(vclock trace.VClock) trace.VClock {
	for _, record := range res.readsInProgress {
		vclock = vclock.Merge(record.clock)
	}
	return vclock
}

func (res *tcpMailboxesLocal) Close() error {
	res.lock.Lock()
	res.closing = true
	res.lock.Unlock()

	// wait for all the pre-commits that we have responded to be committed
	//res.wg.Wait()
	time.Sleep(500 * time.Millisecond)
	// signal to close the listener and active connections
	close(res.done)

	var err error
	if res.listener != nil {
		err = res.listener.Close()
	}
	return err
}

func (res *tcpMailboxesLocal) length() int {
	return len(res.readBacklog) + len(res.msgChannel)
}

type tcpMailboxesRemote struct {
	distsys.ArchetypeResourceLeafMixin
	dialAddr string

	clock, oldClock trace.VClock

	inCriticalSection bool
	conn              net.Conn
	connEncoder       *gob.Encoder
	connDecoder       *gob.Decoder

	resendBuffer []interface{}

	config mailboxesConfig
}

var _ distsys.ArchetypeResource = &tcpMailboxesRemote{}

func newTCPMailboxesRemote(dialAddr string, opts ...MailboxesOption) distsys.ArchetypeResource {
	config := defaultMailboxesConfig
	for _, opt := range opts {
		opt(config)
	}

	return &tcpMailboxesRemote{
		dialAddr: dialAddr,
		config:   config,
	}
}

func (res *tcpMailboxesRemote) ensureConnection() error {
	if res.conn == nil {
		var err error
		res.conn, err = net.DialTimeout("tcp", res.dialAddr, res.config.dialTimeout)
		if err != nil {
			res.conn, res.connEncoder, res.connDecoder = nil, nil, nil
			log.Printf("failed to dial %s, aborting: %v", res.dialAddr, err)
			return distsys.ErrCriticalSectionAborted
		}
		// res.conn is wrapped; don't try to use it directly, or you might miss resetting the deadline!
		wrappedReaderWriter := makeReadWriterConnTimeout(res.conn, res.config.writeTimeout)
		res.connEncoder = gob.NewEncoder(wrappedReaderWriter)
		res.connDecoder = gob.NewDecoder(wrappedReaderWriter)
	}
	return nil
}

func (res *tcpMailboxesRemote) Abort() chan struct{} {
	// nothing to do; the remote end tolerates just starting over with no explanation
	res.inCriticalSection = false // but note to ourselves that we are starting over, so we re-send the begin record
	res.resendBuffer = nil
	res.clock = res.oldClock
	return nil
}

func (res *tcpMailboxesRemote) PreCommit() chan error {
	if !res.inCriticalSection {
		return nil
	}

	ch := make(chan error, 1)
	go func() {
		var err error
		handleError := func() {
			log.Printf("network error while performing pre-commit handshake, aborting: %v", err)
			// close the connection to close the allocated file descriptors
			if err := res.conn.Close(); err != nil {
				log.Printf("error in closing conn: %s", err)
			}
			res.conn = nil
			ch <- distsys.ErrCriticalSectionAborted
		}

		if res.conn == nil {
			panic("no connection available while doing pre-commit")
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

// resend will be called only by Commit if a network error happens during the
// commit. resend requires the res.conn to be nil, and creates a new connection.
// It sends the necessary messages over the new connection, so the commit can
// be done after.
// We don't need to resend the pre-commit message, since we've got the
// pre-commit confirmation before. The tcpNetworkBegin and all the values
// should be sent in the same connection along with the commit message. So
// we resend these messages to make it possible to send the commit message
// over the new connection.
func (res *tcpMailboxesRemote) resend() error {
	if res.conn != nil {
		panic("resend requires the conn to be nil")
	}
	err := res.ensureConnection()
	if err != nil {
		return err
	}

	for _, msg := range res.resendBuffer {
		err = res.connEncoder.Encode(msg)
		if err != nil {
			return err
		}
	}
	return nil
}

func (res *tcpMailboxesRemote) Commit() chan struct{} {
	if !res.inCriticalSection {
		return nil
	}

	ch := make(chan struct{}, 1)
	go func() {
		var err error
		for {
			if err != nil {
				log.Printf("network error during commit: %s", err)
				if res.conn != nil {
					if err := res.conn.Close(); err != nil {
						log.Printf("error in closing conn: %s", err)
					}
					res.conn = nil
				}
				err = res.resend()
				if err != nil {
					continue
				}
			}
			if res.conn == nil {
				panic("no connection available while doing commit")
			}

			err = res.connEncoder.Encode(tcpNetworkCommit)
			if err != nil {
				continue
			}
			err = res.connEncoder.Encode(&res.clock)
			if err != nil {
				continue
			}
			var shouldResend bool
			err = res.connDecoder.Decode(&shouldResend)
			if err != nil {
				continue
			}
			if shouldResend {
				panic("shouldResend must be false since we don't support crash-recovery model right now.")
			}
			res.inCriticalSection = false
			res.resendBuffer = nil
			res.oldClock = res.clock
			ch <- struct{}{}
			return
		}
	}()
	return ch
}

func (res *tcpMailboxesRemote) ReadValue() (tla.Value, error) {
	panic(fmt.Errorf("attempted to read from a remote mailbox archetype resource"))
}

func (res *tcpMailboxesRemote) WriteValue(value tla.Value) error {
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

	// Note that we should send all the data in only *one* connection. If we got
	// an error anytime, we should abort the critical section.
	err = res.ensureConnection()
	if err != nil {
		return err
	}
	if !res.inCriticalSection {
		res.inCriticalSection = true
		res.oldClock = res.clock
		err = res.connEncoder.Encode(tcpNetworkBegin)
		if err != nil {
			return handleError()
		}
		res.resendBuffer = append(res.resendBuffer, tcpNetworkBegin)
	}
	err = res.connEncoder.Encode(tcpNetworkValue)
	if err != nil {
		return handleError()
	}
	res.resendBuffer = append(res.resendBuffer, tcpNetworkValue)
	err = res.connEncoder.Encode(&value)
	if err != nil {
		return handleError()
	}
	res.resendBuffer = append(res.resendBuffer, &value)
	return nil
}

func (res *tcpMailboxesRemote) VClockHint(vclock trace.VClock) trace.VClock {
	res.clock = res.clock.Merge(vclock)
	return res.clock
}

func (res *tcpMailboxesRemote) Close() error {
	var err error
	if res.conn != nil {
		err = res.conn.Close()
	}
	return err
}
