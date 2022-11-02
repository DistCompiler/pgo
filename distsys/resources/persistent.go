package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"log"

	"github.com/UBC-NSS/pgo/distsys/trace"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
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

func (res *Persistent) Abort() chan struct{} {
	res.hasNewValue = false
	return res.wrappedRes.Abort()
}

func (res *Persistent) PreCommit() chan error {
	return res.wrappedRes.PreCommit()
}

func (res *Persistent) Commit() chan struct{} {
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

		ch := res.wrappedRes.Commit()
		if ch != nil {
			<-ch
		}
		doneCh <- struct{}{}
	}()
	return doneCh
}

func (res *Persistent) ReadValue() (tla.Value, error) {
	return res.wrappedRes.ReadValue()
}

func (res *Persistent) WriteValue(value tla.Value) error {
	res.hasNewValue = true
	return res.wrappedRes.WriteValue(value)
}

func (res *Persistent) Index(index tla.Value) (distsys.ArchetypeResource, error) {
	return res.wrappedRes.Index(index)
}

func (res *Persistent) Close() error {
	return res.wrappedRes.Close()
}

func (res *Persistent) VClockHint(archClock trace.VClock) trace.VClock {
	return archClock
}
