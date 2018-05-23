package distsys

import (
	"log"
)

func (net *Network) Acquire(set *AcquireSet) (*ReleaseSet, map[string]interface{}, error) {
	log.Printf("[%v] Acquire(%v)\n", net.localhost, set)

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

		batch, incomplete, err := net.nextBatch(remaining)

		if err != nil {
			return nil, nil, err
		}

		if !incomplete {
			break
		}

		if batch.isLocalhost(net) {
			for _, key := range batch.transaction.sorted() {
				var val interface{}
				var err error

				if batch.transaction.isExclusive(key) {
					val, err = net.store.HoldExclusive(key)
				} else {
					val, err = net.store.Hold(key)
				}

				if err != nil {
					return nil, nil, err
				}

				net.migration.OnGet(net.localhost, key)

				if _, ok := getSet[key]; ok {
					values[key] = val
				}

				completed = append(completed, key)
			}
		} else {
			args := GetRemoteArgs{
				Host:        net.localhost,
				Transaction: batch.transaction,
			}
			var reply GetRemoteReply

			net.connections.GetConnection(batch.addr).Call("StateServer.GetRemote", &args, &reply)

			for key, object := range reply.Objects {
				if _, ok := getSet[key]; ok {
					values[key] = object.Value
				}

				if object.Migrated {
					owner := net.owners[key]

					owner.hostID, _ = net.getOwnerID(net.localhost)
					net.store.create(key, object.Value)

					ack := AckMigrationArgs{
						Host: net.localhost,
						Key:  key,
					}

					net.connections.GetConnection(batch.addr).Call("StateServer.AckMigration", ack, new(bool))
				}

				completed = append(completed, key)
			}

			for key, owner := range reply.Redirects {
				object := net.owners[key]
				object.hostID, _ = net.getOwnerID(owner)
			}
		}

		net.unlock(batch)
	}

	return &ReleaseSet{
		WriteNames:  set.WriteNames,
		Transaction: transaction,
	}, values, nil
}

func (net *Network) Release(set *ReleaseSet, values ...interface{}) error {
	log.Printf("[%v] Release(%v) = %v\n", net.localhost, set, values)

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

		batch, incomplete, err := net.nextBatch(remaining)

		if err != nil {
			return err
		}

		if !incomplete {
			break
		}

		if batch.isLocalhost(net) {
			for _, key := range batch.transaction.sorted() {
				var err error

				if val, ok := setSet[key]; ok {
					net.store.Set(key, val)
				} else if batch.transaction.isExclusive(key) {
					net.store.Release(key)
				}

				if err != nil {
					log.Panic(err)
				}

				net.migration.OnSet(net.localhost, key)

				completed = append(completed, key)
			}
		} else {
			args := SetRemoteArgs{
				Host:        net.localhost,
				Transaction: batch.transaction,
				Values:      setSet,
			}
			var reply SetRemoteReply

			net.connections.GetConnection(batch.addr).Call("StateServer.SetRemote", &args, &reply)

			for key, owner := range reply.Redirects {
				object := net.owners[key]
				object.hostID, _ = net.getOwnerID(owner)
			}

			for _, key := range batch.transaction.sorted() {
				if _, ok := reply.Redirects[key]; !ok {
					completed = append(completed, key)
				}
			}
		}

		net.unlock(batch)
	}

	return nil
}

func (net *Network) SetPolicy(policy IMigrationPolicy) {
	net.migration = policy
}

func (net *Network) Close() error {
	net.connections.Close()
	return nil
}
