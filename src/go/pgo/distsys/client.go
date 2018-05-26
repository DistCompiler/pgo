package distsys

type stateHandler interface {
	GetState() (VarReferences, error)
	ReleaseState(VarReferences) error
}

type baseHandler struct {
	group       *VarReq
	stateServer *StateServer
}

type localHandler struct {
	*baseHandler
}

type remoteHandler struct {
	*baseHandler
}

func (local localHandler) GetState() (VarReferences, error) {
	refs := map[string]Reference{}

	for _, borrowVar := range local.group.Names {
		var hold func(string) (interface{}, error)

		if borrowVar.Exclusive {
			hold = local.stateServer.store.HoldExclusive
		} else {
			hold = local.stateServer.store.Hold
		}

		val, err := hold(borrowVar.Name)
		if err != nil {
			return nil, err
		}

		refs[borrowVar.Name] = Reference{
			Value:     val,
			Exclusive: borrowVar.Exclusive,
		}
	}

	return refs, nil
}

func (local localHandler) ReleaseState(refs VarReferences) error {
	for name, ref := range refs {
		if ref.Exclusive {
			local.stateServer.store.ReleaseExclusive(name)
		} else {
			local.stateServer.store.Release(name)
		}
	}

	return nil
}

func (remote remoteHandler) GetState() (VarReferences, error) {
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)
	refs := VarReferences(map[string]Reference{})

	if err := conn.Call("StateServer.GetState", remote.group, refs); err != nil {
		return nil, err
	}

	return refs, nil
}

func (remote remoteHandler) ReleaseState(refs VarReferences) error {
	var ok bool
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)

	if err := conn.Call("StateServer.ReleaseState", refs, &ok); err != nil {
		return err
	}

	return nil
}

func stateBuilder(group *VarReq, ss *StateServer) stateHandler {
	if group.Peer == ss.self {
		return localHandler{&baseHandler{group, ss}}
	}

	return remoteHandler{&baseHandler{group, ss}}
}

func (ss *StateServer) Acquire(spec *BorrowSpec) (VarReferences, error) {
	op := GlobalStateOperation{
		spec:      spec,
		ownership: ss.ownership,
	}

	// prevent migrations while we determine state ownership
	ss.ownership.RLock()
	defer ss.ownership.RUnlock()

	allRefs := VarReferences(map[string]Reference{})

	for _, group := range op.Groups() {
		refs, err := stateBuilder(group, ss).GetState()
		if err != nil {
			return nil, err
		}

		allRefs = allRefs.Merge(refs)
	}

	return allRefs, nil
}

func (ss *StateServer) Release(refs VarReferences) error {
	op := GlobalStateOperation{
		spec:      refs.ToBorrowSpec(),
		ownership: ss.ownership,
	}

	// prevent migrations while we determine state ownership
	ss.ownership.RLock()
	defer ss.ownership.RUnlock()

	for _, group := range op.Groups() {
		if err := stateBuilder(group, ss).ReleaseState(refs); err != nil {
			return err
		}
	}

	return nil
}

// func (net *Network) Acquire(set *AcquireSet) (*ReleaseSet, map[string]interface{}, error) {
// 	log.Printf("[%v] Acquire(%v)\n", net.localhost, set)

// 	keys := make(map[string]bool)
// 	getSet := make(map[string]bool)
// 	setSet := make(map[string]bool)

// 	for _, key := range set.ReadNames {
// 		keys[key] = true
// 		getSet[key] = true
// 	}

// 	for _, key := range set.WriteNames {
// 		keys[key] = true
// 		setSet[key] = true
// 	}

// 	// build network transaction
// 	transaction := TransactionSet{
// 		Keys: keys,
// 	}

// 	completed := make([]string, 0, len(transaction.Keys))
// 	values := make(map[string]interface{}, len(set.ReadNames))

// 	for {
// 		remaining := transaction.remove(completed)

// 		if remaining.isEmpty() {
// 			break
// 		}

// 		batch, incomplete, err := net.nextBatch(remaining)

// 		if err != nil {
// 			return nil, nil, err
// 		}

// 		if !incomplete {
// 			break
// 		}

// 		if batch.isLocalhost(net) {
// 			for _, key := range batch.transaction.sorted() {
// 				var val interface{}
// 				var err error

// 				if batch.transaction.isExclusive(key) {
// 					val, err = net.store.HoldExclusive(key)
// 				} else {
// 					val, err = net.store.Hold(key)
// 				}

// 				if err != nil {
// 					return nil, nil, err
// 				}

// 				net.migration.OnGet(net.localhost, key)

// 				if _, ok := getSet[key]; ok {
// 					values[key] = val
// 				}

// 				completed = append(completed, key)
// 			}
// 		} else {
// 			args := GetRemoteArgs{
// 				Host:        net.localhost,
// 				Transaction: batch.transaction,
// 			}
// 			var reply GetRemoteReply

// 			net.connections.GetConnection(batch.addr).Call("StateServer.GetRemote", &args, &reply)

// 			for key, object := range reply.Objects {
// 				if _, ok := getSet[key]; ok {
// 					values[key] = object.Value
// 				}

// 				if object.Migrated {
// 					owner := net.owners[key]

// 					owner.hostID, _ = net.getOwnerID(net.localhost)
// 					net.store.create(key, object.Value)

// 					ack := AckMigrationArgs{
// 						Host: net.localhost,
// 						Key:  key,
// 					}

// 					net.connections.GetConnection(batch.addr).Call("StateServer.AckMigration", ack, new(bool))
// 				}

// 				completed = append(completed, key)
// 			}

// 			for key, owner := range reply.Redirects {
// 				object := net.owners[key]
// 				object.hostID, _ = net.getOwnerID(owner)
// 			}
// 		}

// 		net.unlock(batch)
// 	}

// 	return &ReleaseSet{
// 		WriteNames:  set.WriteNames,
// 		Transaction: transaction,
// 	}, values, nil
// }

// func (net *Network) Release(set *ReleaseSet, values ...interface{}) error {
// 	log.Printf("[%v] Release(%v) = %v\n", net.localhost, set, values)

// 	if len(set.WriteNames) != len(values) {
// 		return RangeMismatchError{}
// 	}

// 	setSet := make(map[string]interface{})

// 	for i, key := range set.WriteNames {
// 		setSet[key] = values[i]
// 	}

// 	// use network transaction
// 	transaction := set.Transaction
// 	completed := make([]string, 0, len(transaction.Keys))

// 	for {
// 		remaining := transaction.remove(completed)

// 		if remaining.isEmpty() {
// 			break
// 		}

// 		batch, incomplete, err := net.nextBatch(remaining)

// 		if err != nil {
// 			return err
// 		}

// 		if !incomplete {
// 			break
// 		}

// 		if batch.isLocalhost(net) {
// 			for _, key := range batch.transaction.sorted() {
// 				var err error

// 				if val, ok := setSet[key]; ok {
// 					net.store.Set(key, val)
// 				} else if batch.transaction.isExclusive(key) {
// 					net.store.Release(key)
// 				}

// 				if err != nil {
// 					log.Panic(err)
// 				}

// 				net.migration.OnSet(net.localhost, key)

// 				completed = append(completed, key)
// 			}
// 		} else {
// 			args := SetRemoteArgs{
// 				Host:        net.localhost,
// 				Transaction: batch.transaction,
// 				Values:      setSet,
// 			}
// 			var reply SetRemoteReply

// 			net.connections.GetConnection(batch.addr).Call("StateServer.SetRemote", &args, &reply)

// 			for key, owner := range reply.Redirects {
// 				object := net.owners[key]
// 				object.hostID, _ = net.getOwnerID(owner)
// 			}

// 			for _, key := range batch.transaction.sorted() {
// 				if _, ok := reply.Redirects[key]; !ok {
// 					completed = append(completed, key)
// 				}
// 			}
// 		}

// 		net.unlock(batch)
// 	}

// 	return nil
// }

// func (net *Network) SetPolicy(policy MigrationPolicy) {
// 	net.migration = policy
// }

// func (net *Network) Close() error {
// 	net.connections.Close()
// 	return nil
// }
