package resources

import (
	"encoding/gob"
	"fmt"
	"github.com/UBC-NSS/pgo/distsys"
	"log"
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
	tcpMailboxesSendTimeout                 = 20 * time.Millisecond // TODO: same as above
	tcpMailboxesConnectionDroppedRetryDelay = 50 * time.Millisecond // TODO: same
)

func TCPMailboxesArchetypeResourceMaker(addressMappingFn func(distsys.TLAValue) (TCPMailboxKind, string)) distsys.ArchetypeResourceMaker {
	return IncrementalArchetypeMapResourceMaker(func(index distsys.TLAValue) distsys.ArchetypeResourceMaker {
		tpe, addr := addressMappingFn(index)
		switch tpe {
		case TCPMailboxesLocal:
			return tcpMailboxesLocalArchetypeResourceMaker(addr)
		case TCPMailboxesRemote:
			return tcpMailboxesRemoteArchetypeResourceMaker(addr)
		default:
			panic(fmt.Errorf("invalid TCP mailbox type %d for address %s: expected local or remote, which are %d or %d", tpe, addr, TCPMailboxesLocal, TCPMailboxesRemote))
		}
	})
}

type tcpMailboxesLocalArchetypeResource struct {
	distsys.ArchetypeResourceLeafMixin
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
			log.Fatalf("could not listen on address %s", listenAddr)
		}
		go func() {
			for {
				conn, err := listener.Accept()
				if err != nil {
					log.Fatalf("error listening on %s", listenAddr)
				}
				go func() {
					var err error
					encoder := gob.NewEncoder(conn)
					decoder := gob.NewDecoder(conn)
					var localBuffer []distsys.TLAValue
					hasBegun := false
					for {
						if err != nil {
							log.Printf("network error: %s", err.Error())
							break
						}
						var tag int
						err = decoder.Decode(&tag)
						if err != nil {
							continue
						}
						switch tag {
						case tcpNetworkBegin:
							if localBuffer != nil {
								localBuffer = nil
							}
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
							// when crash-proofing, we need a way to identify repeat commits
							// _when an old commit was successful but didn't persist due to crash_
							// could be done by:
							// - send a unique incrementing counter on pre-commit
							// - commit-er sends this id on commit, and we store this commit attempt in a persistent set
							//   alongside the buffer itself
							// - receiving two commits for the same id can be detected by looking in the set, in which
							//   case do nothing and reply that the thing is done.
							// - starting a new critical section sends the id of the remote's last commit, which
							//   indicates that commit was successful, and that the id can be removed from the set
							if !hasBegun {
								err = encoder.Encode(true)
								if err != nil {
									continue
								}
							} else {
								// FIXME: this is weak to restarts, but fixing that without proper context is really hard
								// at least, in this case the msgChannel will function as a rate limiter, so
								// crash-free operation shouldn't do anything weird
								for _, elem := range localBuffer {
									msgChannel <- elem
								}
								err = encoder.Encode(false)
								if err != nil {
									continue
								}
								hasBegun = false
							}
						}
					}
					err = conn.Close()
					if err != nil {
						log.Printf("error closing connection: %s", err.Error())
					}
				}()
			}
		}()

		return &tcpMailboxesLocalArchetypeResource{
			msgChannel: msgChannel,
		}
	})
}

func (res *tcpMailboxesLocalArchetypeResource) Abort() chan struct{} {
	res.readBacklog = append(res.readBacklog, res.readsInProgress...)
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
		res.readBacklog[0] = distsys.TLAValue{}
		res.readBacklog = res.readBacklog[1:]
		return value, nil
	}

	// otherwise, either pull a notification + atomically read a value from the buffer, or time out
	select {
	case msg := <-res.msgChannel:
		res.readsInProgress = append(res.readsInProgress, msg)
		return msg, nil
	case <-time.After(tcpMailboxesSendTimeout):
		return distsys.TLAValue{}, distsys.ErrCriticalSectionAborted
	}
}

func (res *tcpMailboxesLocalArchetypeResource) WriteValue(value distsys.TLAValue) error {
	panic(fmt.Errorf("attempted to write value %v to a local mailbox archetype resource", value))
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
		res.conn, err = net.Dial("tcp", res.dialAddr)
		if err != nil {
			log.Printf("failed to dial %s, aborting after 50ms: %v", res.dialAddr, err)
			time.Sleep(tcpMailboxesConnectionDroppedRetryDelay)
			return distsys.ErrCriticalSectionAborted
		}
		res.connEncoder = gob.NewEncoder(res.conn)
		res.connDecoder = gob.NewDecoder(res.conn)
	}
	return nil
}

func (res *tcpMailboxesRemoteArchetypeResource) Abort() chan struct{} {
	// nothing to do; the remote end tolerates just starting over with no explanation
	return nil
}

func (res *tcpMailboxesRemoteArchetypeResource) PreCommit() chan error {
	ch := make(chan error, 1)
	go func() {
		var err error
		handleError := func() {
			log.Printf("network error while performing pre-commit handshake, aborting: %v", err)
			res.conn = nil
			ch <- distsys.ErrCriticalSectionAborted
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
				log.Printf("network error during commit, resetting: %v", err)
				res.conn = nil
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
		log.Printf("network error during remote value write, aborting: %v", err)
		res.conn = nil
		return distsys.ErrCriticalSectionAborted
	}

	err = res.ensureConnection()
	if err != nil {
		return err
	}
	if !res.inCriticalSection {
		err = res.connEncoder.Encode(tcpNetworkBegin)
		if err != nil {
			return handleError()
		}
	}
	err = res.connEncoder.Encode(tcpNetworkValue)
	if err != nil {
		return handleError()
	}
	addressableValue := new(distsys.TLAValue)
	*addressableValue = value
	err = res.connEncoder.Encode(addressableValue)
	if err != nil {
		return handleError()
	}
	return nil
}
