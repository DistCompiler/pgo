package raftkvs

import (
	"bytes"
	"encoding/gob"
	"fmt"
	"log"

	"github.com/DistCompiler/pgo/distsys"
	"github.com/DistCompiler/pgo/distsys/tla"
	"github.com/benbjohnson/immutable"
	"github.com/dgraph-io/badger/v3"
)

type ImmutableResource struct {
	distsys.ArchetypeResourceLeafMixin
	value tla.Value
}

func (res *ImmutableResource) Abort(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *ImmutableResource) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *ImmutableResource) Commit(distsys.ArchetypeInterface) chan struct{} {
	return nil
}

func (res *ImmutableResource) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	return res.value, nil
}

func (res *ImmutableResource) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	panic("writing to an immutable resource is not allowed")
}

func (res *ImmutableResource) Close() error {
	return nil
}

var logConcat = tla.MakeString("log_concat")
var logPop = tla.MakeString("log_pop")

var PersistentLogConstantDefs = distsys.EnsureMPCalContextConfigs(
	distsys.DefineConstantValue("LogConcat", logConcat),
	distsys.DefineConstantValue("LogPop", logPop),
)

func NewPersistentLog(name string, db *badger.DB) distsys.ArchetypeResource {
	res := &PersistentLog{
		name:       name,
		db:         db,
		list:       immutable.NewList[tla.Value](),
		oldList:    immutable.NewList[tla.Value](),
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
	entry tla.Value
	index int
}

// PersistentLog is a distsys.ArchetypeResource that implements Raft's persistent
// log behavior.
type PersistentLog struct {
	name string
	db   *badger.DB

	list       *immutable.List[tla.Value]
	oldList    *immutable.List[tla.Value]
	hasOldList bool
	ops        []logOp
	vclock     tla.VClock
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
				var ans tla.Value
				err := decoder.Decode(&ans)
				if err == nil {
					log.Printf("key = %s, value = %v\n", res.key(i), ans)
				}
				return err
			})
			if err != nil {
				return err
			}
		}
		return nil
	})
	log.Println("err =", err)
}

func (res *PersistentLog) Abort(distsys.ArchetypeInterface) chan struct{} {
	if res.hasOldList {
		res.list = res.oldList
		res.hasOldList = false
		res.oldList = nil
		res.ops = nil
	}
	return nil
}

func (res *PersistentLog) PreCommit(distsys.ArchetypeInterface) chan error {
	return nil
}

func (res *PersistentLog) Commit(distsys.ArchetypeInterface) chan struct{} {
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

func (res *PersistentLog) ReadValue(distsys.ArchetypeInterface) (tla.Value, error) {
	return tla.WrapCausal(tla.MakeTupleFromList(res.list), res.vclock), nil
}

func (res *PersistentLog) WriteValue(iface distsys.ArchetypeInterface, value tla.Value) error {
	// update our special vclock field
	vclock := value.GetVClock()
	value = value.StripVClock()
	if vclock != nil {
		res.vclock = res.vclock.Merge(*vclock)
	}
	// ---
	if !res.hasOldList {
		res.oldList = res.list
		res.hasOldList = true
	}
	if value.ApplyFunction(tla.MakeString("cmd")).Equal(logConcat) {
		it := value.ApplyFunction(tla.MakeString("entries")).AsTuple().Iterator()
		for !it.Done() {
			_, entry := it.Next()
			res.list = res.list.Append(entry)
			res.ops = append(res.ops, logOp{
				typ:   pushOp,
				entry: entry,
				index: res.list.Len() - 1,
			})
		}
	} else if value.ApplyFunction(tla.MakeString("cmd")).Equal(logPop) {
		cnt := int(value.ApplyFunction(tla.MakeString("cnt")).AsNumber())
		for i := 0; i < cnt; i++ {
			res.ops = append(res.ops, logOp{
				typ:   popOp,
				index: res.list.Len() - i - 1,
			})
		}
		res.list = res.list.Slice(0, res.list.Len()-cnt)
	} else {
		panic("unknown")
	}
	return nil
}

func (res *PersistentLog) Index(iface distsys.ArchetypeInterface, index tla.Value) (distsys.ArchetypeResource, error) {
	listIndex := int(index.AsNumber()) - 1
	if listIndex < 0 || listIndex >= res.list.Len() {
		panic("out of range index")
	}
	entry := res.list.Get(listIndex)
	entryRes := &ImmutableResource{value: entry}
	return entryRes, nil
}

func (res *PersistentLog) Close() error {
	return nil
}

func (res *PersistentLog) SetIFace(iface distsys.ArchetypeInterface) {
}
