package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.scope.ChainMap;
import pgo.scope.UID;

public class PlusCalScopeBuilder implements TLAScopeBuilderInterface {
	
	Map<String, UID> tlaDeclarations;
	Map<QualifiedName, UID> tlaDefinitions;
	
	Map<String, UID> variables;
	
	Map<UID, UID> references;
	
	List<UID> danglingReferences;
	List<ScopeConflict> conflicts;

	public PlusCalScopeBuilder(Map<String, UID> tlaDeclarations, Map<QualifiedName, UID> tlaDefinitions,
			Map<String, UID> variables, Map<UID, UID> references, List<UID> danglingReferences, List<ScopeConflict> conflicts) {
		super();
		this.tlaDeclarations = tlaDeclarations;
		this.tlaDefinitions = tlaDefinitions;
		this.variables = variables;
		this.references = references;
		this.danglingReferences = danglingReferences;
		this.conflicts = conflicts;
	}
	
	@Override
	public PlusCalScopeBuilder makeNestedScope() {
		return new PlusCalScopeBuilder(tlaDeclarations, tlaDefinitions, new ChainMap<>(variables), references, danglingReferences, conflicts);
	}
	
	public void reference(String name, UID from) {
		QualifiedName qname = new QualifiedName(name);
		if(variables.containsKey(name)) {
			references.put(from, variables.get(name));
		}else if(tlaDefinitions.containsKey(qname)) {
			references.put(from, tlaDefinitions.get(qname));
		}else if(tlaDeclarations.containsKey(name)) {
			references.put(from, tlaDeclarations.get(name));
		}else {
			danglingReferences.add(from);
		}
	}
	
	public void declare(String name, UID id) {
		QualifiedName qname = new QualifiedName(name);
		if(variables.containsKey(name)) {
			conflicts.add(new ScopeConflict(name, variables.get(name), id));
		}else if(tlaDefinitions.containsKey(qname)) {
			conflicts.add(new ScopeConflict(name, tlaDefinitions.get(qname), id));
		}else if(tlaDeclarations.containsKey(name)) {
			conflicts.add(new ScopeConflict(name, tlaDeclarations.get(name), id));
		}else {
			variables.put(name, id);
		}
	}

	@Override
	public void reference(QualifiedName fromTLAPrefix, UID from) {
		if(fromTLAPrefix.getPrefix().isEmpty()) {
			reference(fromTLAPrefix.getBase(), from);
		}else {
			if(tlaDefinitions.containsKey(fromTLAPrefix)) {
				references.put(from, tlaDefinitions.get(fromTLAPrefix));
			}else {
				danglingReferences.add(from);
			}
		}
	}

	@Override
	public void defineLocal(String id, UID uid) {
		declare(id, uid);
	}

}
