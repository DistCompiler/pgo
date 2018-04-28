package distsys

import (
	"fmt"
	"log"
	"sort"
	"sync"
)

type ObjectOwner struct {
	sync.RWMutex
	hostID int
}

func (t *ObjectOwner) getHost(network *Network) string {
	if t.hostID > len(network.hosts) {
		log.Panicf("invalid host id %v\n", t.hostID)
	}

	return network.hosts[t.hostID]
}

func (t *ObjectOwner) isLocalhost(network *Network) bool {
	return t.getHost(network) == network.localhost
}

// NetworkRPC is a thin Network wrapper
type NetworkRPC struct {
	network *Network
}

// Network holds the state of the network
type Network struct {
	// Connections to other peers
	connections *Connections

	// Network
	localhost string
	hosts     []string
	owners    map[string]*ObjectOwner

	// Other
	store     LocalDataStore
	migration IMigrationPolicy
}

// A TransactionSet is a set of keys in a transaction
type TransactionSet struct {
	Keys map[string]bool
}

func (t *TransactionSet) isEmpty() bool {
	return len(t.Keys) == 0
}

func (t *TransactionSet) sorted() []string {
	keys := make([]string, 0, len(t.Keys))

	for key := range t.Keys {
		keys = append(keys, key)
	}

	sort.Strings(keys)
	return keys
}

func (t *TransactionSet) isExclusive(key string) bool {
	exclusive, ok := t.Keys[key]
	return ok && exclusive
}

func (t *TransactionSet) subset(keys []string) TransactionSet {
	filtered := make(map[string]bool)

	for _, key := range keys {
		if exclusive, ok := t.Keys[key]; ok {
			filtered[key] = exclusive
		}
	}

	return TransactionSet{
		Keys: filtered,
	}
}

func (t *TransactionSet) remove(keys []string) TransactionSet {
	filtered := t.subset(keys).Keys

	for key, exclusive := range t.Keys {
		if _, ok := filtered[key]; ok {
			delete(filtered, key)
		} else {
			filtered[key] = exclusive
		}
	}

	return TransactionSet{
		Keys: filtered,
	}
}

type RemoteObject struct {
	Value    interface{}
	Migrated bool
	Acquired bool
}

type GetRemoteArgs struct {
	Host        string
	Transaction TransactionSet
}

type SetRemoteArgs struct {
	Host        string
	Transaction TransactionSet
	Values      map[string]interface{}
}

type AckMigrationArgs struct {
	Host string
	Key  string
}

type GetRemoteReply struct {
	Objects   map[string]RemoteObject
	Redirects map[string]string
}

type SetRemoteReply struct {
	Redirects map[string]string
	Errors    map[string]error
}

type NeverMigrate struct{}
type AlwaysMigrate struct{}

func (t *AlwaysMigrate) OnGet(host string, key string) {}
func (t *AlwaysMigrate) OnSet(host string, key string) {}
func (t *AlwaysMigrate) MigrateTo(host string, key string) bool {
	return true
}

func (t *NeverMigrate) OnGet(host string, key string) {}
func (t *NeverMigrate) OnSet(host string, key string) {}
func (t *NeverMigrate) MigrateTo(host string, key string) bool {
	return false
}

type HostFrequency struct {
	Frequency map[string]int
}

type MostFrequentlyUsed struct {
	Keys map[string]HostFrequency
}

type DisconnectedError string
type KeyNotFoundError string
type RangeMismatchError struct{}

// A TransactionError accounts for different errors that can occur while operating on a key
// eg. KeyNotFoundError, Mutex panics..., etc...
type TransactionError map[string]error

func (e DisconnectedError) Error() string {
	return fmt.Sprintf("Disconnected error [%s]", string(e))
}

func (e KeyNotFoundError) Error() string {
	return fmt.Sprintf("Key not found error [%v]", string(e))
}

func (e RangeMismatchError) Error() string {
	return fmt.Sprintf("Range mismatch error")
}

func (e TransactionError) Error() string {
	return fmt.Sprintf("Transaction error [%v]", e)
}

type AcquireSet struct {
	ReadNames  []string
	WriteNames []string
}

type ReleaseSet struct {
	WriteNames  []string
	Transaction TransactionSet
}

type StateServer interface {
	Acquire(set *AcquireSet) (*ReleaseSet, map[string]interface{}, error)
	Release(set *ReleaseSet, values ...interface{}) error

	SetPolicy(policy IMigrationPolicy)

	Close() error
}

type IMigrationPolicy interface {
	OnGet(host string, key string)
	OnSet(host string, key string)
	MigrateTo(host string, key string) bool
}

type LocalDataStore interface {
	Get(key string) (interface{}, error)
	GetExclusive(key string) (interface{}, error)
	Set(key string, value interface{})
	Release(key string)

	remove(key string)
	create(key string, value interface{})
}

func (t *MostFrequentlyUsed) OnGet(host string, key string) {
	entry, ok := t.Keys[key]

	if !ok {
		entry = HostFrequency{
			Frequency: make(map[string]int),
		}
	}

	freq, ok := entry.Frequency[host]
	if !ok {
		freq = 0
	}

	freq++

	entry.Frequency[host] = freq
	t.Keys[key] = entry
}

func (t *MostFrequentlyUsed) OnSet(host string, key string) {
	t.OnGet(host, key)
}

func (t *MostFrequentlyUsed) MigrateTo(host string, key string) bool {
	entry, ok := t.Keys[key]

	if !ok {
		return false
	}

	var maxHost string
	var maxFreq int

	for curr, freq := range entry.Frequency {
		if freq > maxFreq {
			maxHost = curr
			maxFreq = freq
		}
	}

	if host != maxHost {
		return false
	}

	return true
}

func NewStateServer(peers []string, self, coordinator string /*, identifiers map[string]int*/, initValues map[string]interface{}) (StateServer, error) {
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)

	pi := NewProcessInitialization(peers, self, coordinator)

	// FIXME this is assuming everything is centralized in one place
	selfId := -1
	for i, p := range peers {
		if p == self {
			selfId = i
		}
	}
	if selfId < 0 {
		panic("self is not in peers")
	}
	owners := make(map[string]*ObjectOwner, len(initValues))
	store := make(map[string]interface{})
	if pi.isCoordinator() {
		store = initValues
		for key, _ := range initValues {
			owners[key] = &ObjectOwner{
				hostID: selfId,
			}
		}
	}

	network := &Network{
		store:     CreateSimpleDataStore(store),
		owners:    owners,
		localhost: self,
		hosts:     peers,
		migration: &NeverMigrate{},
	}

	pi := NewProcessInitialization(peers, self, coordinator)
	err := pi.Init()
	if err != nil {
		return nil, err
	}
	network.connections = pi.Network
	if err := network.connections.ExposeImplementation("StateServer", &NetworkRPC{network}); err != nil {
		return nil, err
	}

	return network, nil
}

func (t *Network) getOwnerID(host string) (int, bool) {
	for ownerID, hostname := range t.hosts {
		if host == hostname {
			return ownerID, true
		}
	}

	return -1, false
}

type Batch struct {
	addr        string
	transaction TransactionSet
}

func (b *Batch) isLocalhost(t *Network) bool {
	return b.addr == t.localhost
}

func (t *Network) nextBatch(transaction TransactionSet) (*Batch, bool, error) {
	if len(transaction.Keys) == 0 {
		return nil, false, nil
	}

	var host string
	var keys []string

	for _, key := range transaction.sorted() {
		owner, ok := t.owners[key]

		if !ok {
			return nil, false, KeyNotFoundError(key)
		}

		owner.RLock()

		if len(keys) == 0 || host == owner.getHost(t) {
			host = owner.getHost(t)
			keys = append(keys, key)
		} else {
			owner.RUnlock()
			break
		}
	}

	return &Batch{
		addr:        host,
		transaction: transaction.subset(keys),
	}, len(keys) > 0, nil
}

func (t *Network) unlock(batch *Batch) error {
	for _, key := range batch.transaction.sorted() {
		owner, ok := t.owners[key]

		if !ok {
			return KeyNotFoundError(key)
		}

		owner.RUnlock()
	}

	return nil
}
