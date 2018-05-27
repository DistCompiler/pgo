package distsys

// stateHandler defines the interface of a state handler. Apart from the definitions
// of localStateHandler, which manipulate state located within the running node's
// local store, there is also the possibility that state lives in another node
// in the system, and a similar interface is required
type stateHandler interface {
	GetState() (VarReferences, error)
	ReleaseState(VarReferences) error
}

// remoteHandler implements stateHandler for the case where state lives in a different
// node in the network
type remoteHandler struct {
	group       *VarReq
	stateServer *StateServer
}

// GetState retrieves state that lives in another node in the system. The ownership table
// needs to be locked before this function is called since the variable may have
// moved.
func (remote remoteHandler) GetState() (VarReferences, error) {
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)
	refs := VarReferences(map[string]*Reference{})

	if err := conn.Call("StateServer.GetState", remote.group, &refs); err != nil {
		return nil, err
	}

	return refs, nil
}

// ReleaseState releases state that lives in another system. This function needs to be
// called once a counterpart GetState call has succeeded.
func (remote remoteHandler) ReleaseState(refs VarReferences) error {
	var ok bool
	conn := remote.stateServer.connections.GetConnection(remote.group.Peer)

	if err := conn.Call("StateServer.ReleaseState", &refs, &ok); err != nil {
		return err
	}

	return nil
}

// stateBuilder returns a stateHandler that either manipulates state in the running node's
// local store, or sends messages to the node that currently owns the state contained
// in the VarReq struct.
func stateBuilder(group *VarReq, ss *StateServer) stateHandler {
	if group.Peer == ss.self {
		return localStateHandler{group, ss.store}
	}

	return remoteHandler{group, ss}
}

// Acquire receives a BorrowSpec and returns a populated VarReferences struct containing
// the values of the variables in the spec given, with the requested permissions (i.e.,
// exclusive or non-exclusive (read-only) access).
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

// Release receives a set of references to variables, potentially manipulated by
// the application (after a call to Acquire), and releases any locks that were
// held, either locally or remotely on a different node in the system.
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
