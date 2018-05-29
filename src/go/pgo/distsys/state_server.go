package distsys

func (iface *StateServerRPC) GetState(req *VarReq, refs *VarReferences) error {
	handler := localStateHandler{
		group:             req,
		store:             iface.server.store,
		ownership:         iface.server.ownership,
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
	handler := localStateHandler{
		store:             iface.server.store,
		ownership:         iface.server.ownership,
		migrationStrategy: iface.server.migrationStrategy,
	}

	if err := handler.ReleaseState(refs); err != nil {
		return err
	}

	*ok = true
	return nil
}
