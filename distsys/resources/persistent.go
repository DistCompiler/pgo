package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"log"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

// TODO: recovery from persistent storage is not implemented yet.

type Persistable interface {
	distsys.ArchetypeResource
	GetState() ([]byte, error)
}

type Persistent struct {
	db *badger.DB

	wrappedRes  Persistable
	hasNewValue bool

	name string
}

func MakePersistent(name string, db *badger.DB, persistable Persistable) distsys.ArchetypeResource {
	persistentRes := &Persistent{
		db:          db,
		wrappedRes:  persistable,
		hasNewValue: false,
		name:        name,
	}
	//persistentRes.load()
	return persistentRes
}

func (res *Persistent) key() string {
	return fmt.Sprintf("pres-%s", res.name)
}

func (res *Persistent) load() {
	err := res.db.View(func(txn *badger.Txn) error {
		item, err := txn.Get([]byte(res.key()))
		if err != nil {
			return err
		}
		err = item.Value(func(val []byte) error {
			buf := bytes.NewBuffer(val)
			decoder := gob.NewDecoder(buf)
			var ans tla.Value
			err := decoder.Decode(&ans)
			if err == nil {
				log.Printf("key = %s, value = %v\n", res.key(), ans)
			}
			return err
		})
		return err
	})
	log.Println("err =", err)
}

func (res *Persistent) Abort(iface distsys.ArchetypeInterface) chan struct{} {
	res.hasNewValue = false
	return res.wrappedRes.Abort(iface)
}

func (res *Persistent) PreCommit(iface distsys.ArchetypeInterface) chan error {
	return res.wrappedRes.PreCommit(iface)
}

func (res *Persistent) Commit(iface distsys.ArchetypeInterface) chan struct{} {
	doneCh := make(chan struct{}, 1)
	go func() {
		if res.hasNewValue {
			err := res.db.Update(func(txn *badger.Txn) error {
				value, err := res.wrappedRes.GetState()
				if err != nil {
					return err
				}
				err = txn.Set([]byte(res.key()), value)
				return err
			})
			if err != nil {
				panic(err)
			}
			res.hasNewValue = false
		}

		ch := res.wrappedRes.Commit(iface)
		if ch != nil {
			<-ch
		}
		doneCh <- struct{}{}
	}()
	return doneCh
}

func (res *Persistent) ReadValue(iface distsys.ArchetypeInterface) (tla.Value, error) {
	return res.wrappedRes.ReadValue(iface)
}

func (res *Persistent) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	res.hasNewValue = true
	return res.wrappedRes.WriteValue(iface, value)
}

func (res *Persistent) Index(iface distsys.ArchetypeInterface, index tla.Value) (distsys.ArchetypeResource, error) {
	return res.wrappedRes.Index(iface, index)
}

func (res *Persistent) Close() error {
	return res.wrappedRes.Close()
}
