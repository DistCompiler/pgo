package distsys

import (
	"log"
	"reflect"
)

func (t *NetworkRPC) GetRemote(args *GetRemoteArgs, reply *GetRemoteReply) error {
	log.Printf("GetRemote(%v)\n", args)

	errors := make(map[string]error)
	redirects := make(map[string]string)
	objects := make(map[string]RemoteObject)

	for _, key := range args.Transaction.sorted() {
		owner, ok := t.network.owners[key]
		if !ok {
			errors[key] = KeyNotFoundError(key)
			continue
		}

		owner.RLock()
		// log.Printf("locked key owner %v\n", key)

		// disallow object access after redirecting, ensures locking order
		// local requests will redirect to itself
		if owner.isLocalhost(t.network) && len(redirects) == 0 {
			var err error
			var val interface{}

			if args.Transaction.isExclusive(key) {
				val, err = t.network.store.GetExclusive(key)
			} else {
				val, err = t.network.store.GetExclusive(key)
				// TODO: for non-exclusive reads
				// val, err = t.network.store.Get(key)
			}

			if err != nil {
				errors[key] = err
				continue
			}

			t.network.migration.OnGet(args.Host, key)

			acquired := args.Transaction.isExclusive(key)
			migrated := t.network.migration.MigrateTo(args.Host, key)
			objects[key] = RemoteObject{
				Value:    val,
				Acquired: acquired,
				Migrated: migrated,
			}

			// migration case will skip the remainder of the loop, not unlocking the owner
			// until an ACK is recieved
			if migrated {
				/*
					https://golang.org/src/sync/rwmutex.go

					* If a goroutine holds a RWMutex for reading and another goroutine might call Lock,
					* no goroutine should expect to be able to acquire a read lock until the initial
					* read lock is released ...
					* ... a blocked Lock call excludes new readers from acquiring the lock.

					// A writer is pending.
					74  		if atomic.AddInt32(&rw.readerWait, -1) == 0 {
					75  			// The last reader unblocks the writer.
					76  			runtime_Semrelease(&rw.writerSem, false)
					77  		}

					// Wait for active readers.
					97  	if r != 0 && atomic.AddInt32(&rw.readerWait, r) != 0 {
					98  		runtime_Semacquire(&rw.writerSem)
					99  	}

					thus if the current state is RLock, WLock will block until readerWait == 0;
					however, this cannot happen until the current RLock is released (readerWait)

					eg.
					RLock() 	=> readerWait = 0
					go WLock() 	=> readerWait = readerCount = 1 or more

					while readerWait != 1
					{ }			=> current state is not pending WLock
					RUnlock() 	=> release the last reader, releasing the writerSem
				*/
				go owner.Lock()

				for {
					readers := reflect.ValueOf(owner.RWMutex).FieldByName("readerWait").Int()

					// wait until owner.Lock is registered
					if readers >= 1 {
						owner.RUnlock()

						// TODO: more idiomatic way:
						// owner.TryLock()
						// if locked => upgrade then migrate
						// else => unlock

						/*
							type Mutex struct {
								sync.Mutex
							}

							const mutexLocked = 1 << iota

							func (m *Mutex) Unlock() {
								m.Mutex.Unlock()
							}

							func (m *Mutex) Lock() {
								m.Mutex.Lock()
							}

							func (m *Mutex) TryLock() bool {
								state := (*int32)(unsafe.Pointer(reflect.ValueOf(&m.Mutex).Elem().FieldByName("state").UnsafeAddr()))
								return atomic.CompareAndSwapInt32(state, 0, mutexLocked)

								// below is equivalent, just less clear
								// return atomic.CompareAndSwapInt32((*int32)(unsafe.Pointer(&m.Mutex)), 0, mutexLocked)
							}
						*/

						// this is the equivalent of TryReaders()...
						// will only migrate if there are no readers
						if readers == 1 {
							// no other readers, and we have exclusive access
							objects[key] = RemoteObject{
								Value:    val,
								Acquired: acquired,
								Migrated: migrated,
							}
						} else {
							// other readers are accessing this object, cannot migrate
							objects[key] = RemoteObject{
								Value:    val,
								Acquired: acquired,
								Migrated: false,
							}
						}

						break
					}
				}

				log.Printf("migrating key %v to host %v, waiting for ACK\n", key, args.Host)
				t.network.store.remove(key)
				continue
			}
		} else {
			redirects[key] = owner.getHost(t.network)
		}

		// log.Printf("unlocked key owner %v\n", key)
		owner.RUnlock()
	}

	if len(errors) > 0 {
		return TransactionError(errors)
	}

	reply.Objects = objects
	reply.Redirects = redirects
	return nil
}

func (t *NetworkRPC) SetRemote(args *SetRemoteArgs, reply *SetRemoteReply) error {
	log.Printf("SetRemote(%v)\n", args)

	errors := make(map[string]error)
	redirects := make(map[string]string)

	for _, key := range args.Transaction.sorted() {
		owner, ok := t.network.owners[key]
		if !ok {
			errors[key] = KeyNotFoundError(key)
			continue
		}

		owner.RLock()
		// log.Printf("locked key owner %v\n", key)

		// disallow object access after redirecting, ensures locking order
		// local requests will redirect to itself
		if owner.isLocalhost(t.network) && len(redirects) == 0 {
			var err error

			if val, ok := args.Values[key]; ok {
				t.network.store.Set(key, val)
			} else if args.Transaction.isExclusive(key) {
				t.network.store.Release(key)
			}

			if err != nil {
				errors[key] = err
				continue
			}

			t.network.migration.OnSet(args.Host, key)
		} else {
			redirects[key] = owner.getHost(t.network)
		}

		// log.Printf("unlocked key owner %v\n", key)
		owner.RUnlock()
	}

	if len(errors) > 0 {
		return TransactionError(errors)
	}

	reply.Redirects = redirects
	log.Printf("SetRemote redirects=%v, transaction=%v", redirects, args.Transaction.Keys)
	return nil
}

func (t *NetworkRPC) AckMigration(args *AckMigrationArgs, reply *bool) error {
	log.Printf("AckMigration(%v)\n", args)

	owner := t.network.owners[args.Key]
	owner.hostID, _ = t.network.getOwnerID(args.Host)

	owner.Unlock()
	// log.Printf("unlocked key owner %v\n", args.Key)

	*reply = true
	return nil
}
