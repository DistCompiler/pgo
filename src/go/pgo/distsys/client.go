package distsys

import (
	"log"
)

func (t *Network) Acquire(set *AcquireSet) (*ReleaseSet, map[string]interface{}, error) {
	log.Printf("[%v] Acquire(%v)\n", t.localhost, set)

	keys := make(map[string]bool)
	getSet := make(map[string]bool)
	setSet := make(map[string]bool)

	for _, key := range set.ReadNames {
		keys[key] = true
		getSet[key] = true
	}

	for _, key := range set.WriteNames {
		keys[key] = true
		setSet[key] = true
	}

	// build network transaction
	transaction := TransactionSet{
		Keys: keys,
	}

	completed := make([]string, 0, len(transaction.Keys))
	values := make(map[string]interface{}, len(set.ReadNames))

	for {
		remaining := transaction.remove(completed)

		if remaining.isEmpty() {
			break
		}

		batch, incomplete, err := t.nextBatch(remaining)

		if err != nil {
			return nil, nil, err
		}

		if !incomplete {
			break
		}

		if batch.isLocalhost(t) {
			for _, key := range batch.transaction.sorted() {
				var val interface{}
				var err error

				if batch.transaction.isExclusive(key) {
					val, err = t.store.GetExclusive(key)
				} else {
					val, err = t.store.GetExclusive(key)
					// TODO: for non-exclusive reads
					// val, err = t.store.Get(key)
				}

				if err != nil {
					return nil, nil, err
				}

				t.migration.OnGet(t.localhost, key)

				if _, ok := getSet[key]; ok {
					values[key] = val
				}

				completed = append(completed, key)
			}
		} else {
			args := GetRemoteArgs{
				Host:        t.localhost,
				Transaction: batch.transaction,
			}
			var reply GetRemoteReply

			t.client.Call(batch.addr, "StateServer.GetRemote", &args, &reply)

			log.Printf("GetRemote response from %s: %v\n", batch.addr, reply)

			for key, object := range reply.Objects {
				if _, ok := getSet[key]; ok {
					values[key] = object.Value
				}

				if object.Migrated {
					owner := t.owners[key]

					owner.hostID, _ = t.getOwnerID(t.localhost)
					t.store.create(key, object.Value)

					ack := AckMigrationArgs{
						Host: t.localhost,
						Key:  key,
					}

					t.client.Call(batch.addr, "StateServer.AckMigration", ack, new(bool))
				}

				completed = append(completed, key)
			}

			for key, owner := range reply.Redirects {
				object := t.owners[key]
				object.hostID, _ = t.getOwnerID(owner)
			}
		}

		t.unlock(batch)
	}

	log.Printf("[%v] Acquired()=(%v, %v)\n", t.localhost, ReleaseSet{set.WriteNames, transaction}, values)
	return &ReleaseSet{
		WriteNames:  set.WriteNames,
		Transaction: transaction,
	}, values, nil
}

func (t *Network) Release(set *ReleaseSet, values ...interface{}) error {
	log.Printf("[%v] Release(%v) = %v\n", t.localhost, set, values)

	if len(set.WriteNames) != len(values) {
		return RangeMismatchError{}
	}

	setSet := make(map[string]interface{})

	for i, key := range set.WriteNames {
		setSet[key] = values[i]
	}

	// use network transaction
	transaction := set.Transaction
	completed := make([]string, 0, len(transaction.Keys))

	for {
		remaining := transaction.remove(completed)

		if remaining.isEmpty() {
			break
		}

		batch, incomplete, err := t.nextBatch(remaining)

		if err != nil {
			return err
		}

		if !incomplete {
			break
		}

		if batch.isLocalhost(t) {
			for _, key := range batch.transaction.sorted() {
				var err error

				if val, ok := setSet[key]; ok {
					t.store.Set(key, val)
				} else if batch.transaction.isExclusive(key) {
					t.store.Release(key)
				}

				if err != nil {
					log.Panic(err)
				}

				t.migration.OnSet(t.localhost, key)

				completed = append(completed, key)
			}
		} else {
			args := SetRemoteArgs{
				Host:        t.localhost,
				Transaction: batch.transaction,
				Values:      setSet,
			}
			var reply SetRemoteReply

			t.client.Call(batch.addr, "StateServer.SetRemote", &args, &reply)

			for key, owner := range reply.Redirects {
				object := t.owners[key]
				object.hostID, _ = t.getOwnerID(owner)
			}

			for _, key := range batch.transaction.sorted() {
				if _, ok := reply.Redirects[key]; !ok {
					completed = append(completed, key)
				}
			}
		}

		t.unlock(batch)
	}

	return nil
}

func (t *Network) SetPolicy(policy IMigrationPolicy) {
	t.migration = policy
}

func (t *Network) Close() error {
	t.client.Close()
	t.listener.Close()
	return nil
}
