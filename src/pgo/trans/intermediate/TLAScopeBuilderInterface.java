package pgo.trans.intermediate;

import pgo.scope.UID;

public interface TLAScopeBuilderInterface {

	void reference(QualifiedName fromTLAPrefix, UID uid);

	TLAScopeBuilderInterface makeNestedScope();

	void defineLocal(String id, UID uid);

}
