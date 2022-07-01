package raftkvs

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"log"

	"github.com/UBC-NSS/pgo/distsys"
	"github.com/UBC-NSS/pgo/distsys/tla"
	"github.com/UBC-NSS/pgo/distsys/trace"
	"github.com/benbjohnson/immutable"
	"github.com/dgraph-io/badger/v3"
)

type ImmutableResource struct {
	distsys.ArchetypeResourceLeafMixin
	value tla.TLAValue
}

func (res *ImmutableResource) Abort() chan struct{} {
	return nil
}

func (res *ImmutableResource) PreCommit() chan error {
	return nil
}

func (res *ImmutableResource) Commit() chan struct{} {
	return nil
}

func (res *ImmutableResource) ReadValue() (tla.TLAValue, error) {
	return res.value, nil
}

func (res *ImmutableResource) WriteValue(value tla.TLAValue) error {
	panic("writing to an immutable resource is not allowed")
}

func (res *ImmutableResource) Close() error {
	return nil
}

var logConcat = tla.MakeTLAString("log_concat")
var logPop = tla.MakeTLAString("log_pop")

var PersistentLogConstantDefs = distsys.EnsureMPCalContextConfigs(
	distsys.DefineConstantValue("LogConcat", logConcat),
	distsys.DefineConstantValue("LogPop", logPop),
)

func NewPersistentLog(name string, db *badger.DB) distsys.ArchetypeResource {
	res := &PersistentLog{
		name:       name,
		db:         db,
		list:       immutable.NewList(),
		oldList:    immutable.NewList(),
		hasOldList: false,
	}
	//res.load()
	return res
}

type logOpType int

const (
	pushOp logOpType = iota
	popOp
)

type logOp struct {
	typ   logOpType
	entry tla.TLAValue
	index int
}

// PersistentLog is a distsys.ArchetypeResource that implements Raft's persistent
// log behavior.
type PersistentLog struct {
	name string
	db   *badger.DB

	list       *immutable.List
	oldList    *immutable.List
	hasOldList bool
	ops        []logOp
}

func (res *PersistentLog) key(index int) string {
	return fmt.Sprintf("raftkvs.plog.%v.%d", res.name, index)
}

func (res *PersistentLog) load() {
	err := res.db.View(func(txn *badger.Txn) error {
		for i := 0; ; i++ {
			item, err := txn.Get([]byte(res.key(i)))
			if err == badger.ErrKeyNotFound {
				break
			}
			if err != nil {
				return err
			}
			err = item.Value(func(val []byte) error {
				buf := bytes.NewBuffer(val)
				decoder := gob.NewDecoder(buf)
				var ans tla.TLAValue
				err := decoder.Decode(&ans)
				if err == nil {
					log.Printf("key = %s, value = %v\n", res.key(i), ans)
				}
				return err
			})
		}
		return nil
	})
	log.Println("err =", err)
}

func (res *PersistentLog) Abort() chan struct{} {
	if res.hasOldList {
		res.list = res.oldList
		res.hasOldList = false
		res.oldList = nil
		res.ops = nil
	}
	return nil
}

func (res *PersistentLog) PreCommit() chan error {
	return nil
}

func (res *PersistentLog) Commit() chan struct{} {
	ch := make(chan struct{}, 1)

	go func() {
		if res.hasOldList {
			res.hasOldList = false
			res.oldList = nil

			if len(res.ops) > 0 {
				//log.Println(len(res.ops))

				wb := res.db.NewWriteBatch()
				defer wb.Cancel()

				var err error
				for _, op := range res.ops {
					switch op.typ {
					case pushOp:
						var writer bytes.Buffer
						encoder := gob.NewEncoder(&writer)
						err = encoder.Encode(&op.entry)
						if err != nil {
							break
						}
						err = wb.Set([]byte(res.key(op.index)), writer.Bytes())
					case popOp:
						err = wb.Delete([]byte(res.key(op.index)))
					}
					if err != nil {
						break
					}
				}
				if err != nil {
					panic(err)
				}

				err = wb.Flush()
				if err != nil {
					panic(err)
				}
			}
			res.ops = nil
		}
		ch <- struct{}{}
	}()

	return ch
}

func (res *PersistentLog) ReadValue() (tla.TLAValue, error) {
	return tla.MakeTLATupleFromList(res.list), nil
}

func (res *PersistentLog) WriteValue(value tla.TLAValue) error {
	if !res.hasOldList {
		res.oldList = res.list
		res.hasOldList = true
	}
	if value.ApplyFunction(tla.MakeTLAString("cmd")).Equal(logConcat) {
		it := value.ApplyFunction(tla.MakeTLAString("entries")).AsTuple().Iterator()
		for !it.Done() {
			_, entry := it.Next()
			res.list = res.list.Append(entry)
			res.ops = append(res.ops, logOp{
				typ:   pushOp,
				entry: entry.(tla.TLAValue),
				index: res.list.Len() - 1,
			})
		}
	} else if value.ApplyFunction(tla.MakeTLAString("cmd")).Equal(logPop) {
		cnt := int(value.ApplyFunction(tla.MakeTLAString("cnt")).AsNumber())
		for i := 0; i < cnt; i++ {
			res.ops = append(res.ops, logOp{
				typ:   popOp,
				index: res.list.Len() - i - 1,
			})
		}
		if (res.list.Len() - cnt) >= 0 {
			res.list = res.list.Slice(0, res.list.Len()-cnt)
		}
	} else {
		panic("unknown")
	}
	return nil
}

func (res *PersistentLog) Index(index tla.TLAValue) (distsys.ArchetypeResource, error) {
	listIndex := int(index.AsNumber()) - 1
	if listIndex < 0 || listIndex >= res.list.Len() {
		panic("out of range index")
	}
	entry := res.list.Get(listIndex)
	entryRes := &ImmutableResource{value: entry.(tla.TLAValue)}
	return entryRes, nil
}

func (res *PersistentLog) Close() error {
	return nil
}

func (res *PersistentLog) VClockHint(archClock trace.VClock) trace.VClock {
	return trace.VClock{}
}
