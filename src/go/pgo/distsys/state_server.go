package distsys

func (iface *StateServerRPC) GetState(req *VarReq, refs *VarReferences) error {
	handler := requestStateHandler{
		group:     req,
		requester: req.Requester,
		store:     iface.server.store,
		self:      iface.server.self,

		migrationStrategy: iface.server.migrationStrategy,
	}

	state, err := handler.GetState()
	if err != nil {
		return err
	}

	*refs = state
	return nil
}

func (iface *StateServerRPC) ReleaseState(refs VarReferences, ok *bool) error {
	handler := requestStateHandler{store: iface.server.store}

	if err := handler.ReleaseState(refs); err != nil {
		return err
	}

	*ok = true
	return nil
}

func (iface *StateServerRPC) OwnershipMoved(req *VarReq, ok *bool) error {
	handler := requestStateHandler{store: iface.server.store, group: req}
	handler.StateMoveComplete()

	*ok = true
	return nil
}
