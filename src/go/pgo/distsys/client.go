package distsys

type stateHandler interface {
	GetState() (VarReferences, error)
	ReleaseState(VarReferences) error
}

type remoteHandler struct {
	group       *VarReq
	stateServer *StateServer
}

func (remote remoteHandler) GetState() (VarReferences, error) {
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)
	refs := VarReferences(map[string]*Reference{})

	if err := conn.Call("StateServer.GetState", remote.group, &refs); err != nil {
		return nil, err
	}

	return refs, nil
}

func (remote remoteHandler) ReleaseState(refs VarReferences) error {
	var ok bool
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)

	if err := conn.Call("StateServer.ReleaseState", &refs, &ok); err != nil {
		return err
	}

	return nil
}

func stateBuilder(group *VarReq, ss *StateServer) stateHandler {
	if group.Peer == ss.self {
		return localStateHandler{group, ss.store}
	}

	return remoteHandler{group, ss}
}

func (ss *StateServer) Acquire(spec *BorrowSpec) (VarReferences, error) {
	op := GlobalStateOperation{
		spec:      spec,
		ownership: ss.ownership,
	}

	// prevent migrations while we determine state ownership
	ss.ownership.RLock()
	defer ss.ownership.RUnlock()

	allRefs := VarReferences(map[string]*Reference{})

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

// func (net *Network) Close() error {
// 	net.connections.Close()
// 	return nil
// }
