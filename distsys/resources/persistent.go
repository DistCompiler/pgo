package resources

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"log"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/dgraph-io/badger/v3"
)

// TODO: recovery from persistent storage is not implemented yet.

type PersistableResource interface {
	distsys.ArchetypeResource
	GetState() ([]byte, error)
}

type PersistentResource struct {
	db *badger.DB

	wrappedRes  PersistableResource
	hasNewValue bool

	name string
}

func PersistentResourceMaker(name string, db *badger.DB, resMaker distsys.ArchetypeResourceMaker) distsys.ArchetypeResourceMaker {
	return distsys.ArchetypeResourceMakerFn(func() distsys.ArchetypeResource {
		wrapperRes := resMaker.Make().(PersistableResource)
		res := &PersistentResource{
			db:          db,
			wrappedRes:  wrapperRes,
			hasNewValue: false,
			name:        name,
		}
		res.load()
		return res
	})
}

func (res *PersistentResource) key() string {
	return fmt.Sprintf("pres-%s", res.name)
}

func (res *PersistentResource) load() {
	err := res.db.View(func(txn *badger.Txn) error {
		item, err := txn.Get([]byte(res.key()))
		if err != nil {
			return err
		}
		err = item.Value(func(val []byte) error {
			buf := bytes.NewBuffer(val)
			decoder := gob.NewDecoder(buf)
			var ans tla.TLAValue
			err := decoder.Decode(&ans)
			if err == nil {
				log.Println("ans =", ans)
			}
			return err
		})
		return err
	})
	log.Println("err =", err)
}

func (res *PersistentResource) Abort() chan struct{} {
	res.hasNewValue = false
	return res.wrappedRes.Abort()
}

func (res *PersistentResource) PreCommit() chan error {
	return res.wrappedRes.PreCommit()
}

func (res *PersistentResource) Commit() chan struct{} {
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

func (res *PersistentResource) ReadValue() (tla.TLAValue, error) {
	return res.wrappedRes.ReadValue()
}

func (res *PersistentResource) WriteValue(value tla.TLAValue) error {
	res.hasNewValue = true
	return res.wrappedRes.WriteValue(value)
}

func (res *PersistentResource) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	return res.wrappedRes.Index(index)
}

func (res *PersistentResource) Close() error {
	return res.wrappedRes.Close()
}
