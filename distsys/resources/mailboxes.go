package resources

import (
	"fmt"
	"time"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

type Mailboxes struct {
	*IncMap
}

var defaultMailboxesConfig = mailboxesConfig{
	receiveChanSize: 100,
	dialTimeout:     1000 * time.Millisecond,
	readTimeout:     1000 * time.Millisecond,
	writeTimeout:    1000 * time.Millisecond,
}

type mailboxesConfig struct {
	receiveChanSize int
	dialTimeout     time.Duration
	readTimeout     time.Duration
	writeTimeout    time.Duration
}

type MailboxesOption func(mailboxesConfig)

func WithMailboxesReceiveChanSize(s int) MailboxesOption {
	return func(c mailboxesConfig) {
		c.receiveChanSize = s
	}
}

func WithMailboxesDialTimeout(t time.Duration) MailboxesOption {
	return func(c mailboxesConfig) {
		c.dialTimeout = t
	}
}

func WithMailboxesReadTimeout(t time.Duration) MailboxesOption {
	return func(c mailboxesConfig) {
		c.readTimeout = t
	}
}

func WithMailboxesWriteTimeout(t time.Duration) MailboxesOption {
	return func(c mailboxesConfig) {
		c.writeTimeout = t
	}
}

type MailboxKind int

const (
	MailboxesLocal MailboxKind = iota
	MailboxesRemote
)

func (mk MailboxKind) String() string {
	switch mk {
	case MailboxesLocal:
		return "LocalMailbox"
	case MailboxesRemote:
		return "RemoteMailbox"
	default:
		return "UnknownMailbox"
	}
}

// MailboxesAddressMappingFn is responsible for translating the index, as in network[index] from distsys.Value to a pair of
// MailboxKind and address string, where the address string would be appropriate to pass to net.Listen
// or net.Dial. It should return MailboxesLocal if this node is to be the only listener, and it should
// return MailboxesRemote if the mailbox is remote and should be dialed. This could potentially allow unusual setups
// where a single process "owns" more than one mailbox.
type MailboxesAddressMappingFn func(tla.Value) (MailboxKind, string)

type mailboxLengther interface {
	length() int
}

// NewMailboxesLength returns the number of buffered messages in a local
// mailbox. The local mailbox is supposed to be an element of a mailboxes
// collection. Mailboxes length resources matches the following mapping
// macro in MPCal:
//
//    \* assuming initially that:
//    \* $variable := [buffer |-> <<>> (* empty buffer *)]
//
//    mapping macro NetworkBufferLength {
//        read {
//    	      yield Len($variable.buffer);
//        }
//
//        write {
//            assert FALSE;
//            yield $value;
//        }
//    }
func NewMailboxesLength(mailboxes *Mailboxes) distsys.ArchetypeResource {
	return NewIncMap(func(index tla.Value) distsys.ArchetypeResource {
		mailbox, err := mailboxes.Index(index)
		if err != nil {
			panic(fmt.Errorf("wrong index for tcpmailboxes length: %s", err))
		}
		return newMailboxesLocalLength(mailbox.(mailboxLengther))
	})
}

type mailboxesLocalLength struct {
	distsys.ArchetypeResourceLeafMixin
	mailbox mailboxLengther
}

func newMailboxesLocalLength(mailbox mailboxLengther) distsys.ArchetypeResource {
	return &mailboxesLocalLength{mailbox: mailbox}
}

var _ distsys.ArchetypeResource = &mailboxesLocalLength{}

func (res *mailboxesLocalLength) Abort() chan struct{} {
	return nil
}

func (res *mailboxesLocalLength) PreCommit() chan error {
	return nil
}

func (res *mailboxesLocalLength) Commit() chan struct{} {
	return nil
}

func (res *mailboxesLocalLength) ReadValue() (tla.Value, error) {
	return tla.MakeNumber(int32(res.mailbox.length())), nil
}

func (res *mailboxesLocalLength) WriteValue(value tla.Value) error {
	panic(fmt.Errorf("attempted to write value %v to a local mailbox length resource", value))
}

func (res *mailboxesLocalLength) Close() error {
	return nil
}
