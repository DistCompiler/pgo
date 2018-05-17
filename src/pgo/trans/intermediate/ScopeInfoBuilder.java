package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.scope.ChainMap;
import pgo.scope.UID;

public class ScopeInfoBuilder implements TLAScopeBuilderInterface {
	Map<String, UID> declarations;
	Map<QualifiedName, UID> definitions;
	
	Map<UID, UID> references;
	
	List<ScopeConflict> conflicts;
	List<UID> danglingReferences;
	
	public ScopeInfoBuilder(Map<String, UID> declarations, Map<QualifiedName, UID> definitions, List<ScopeConflict> conflicts, Map<UID, UID> references,
			List<UID> danglingReferences) {
		super();
		this.declarations = declarations;
		this.definitions = definitions;
		this.conflicts = conflicts;
		this.references = references;
		this.danglingReferences = danglingReferences;
	}
	
	public ScopeInfoBuilder makeNestedScope() {
		return new ScopeInfoBuilder(declarations, new ChainMap<>(definitions), conflicts, references, danglingReferences);
	}
	
	public void declare(String name, UID id) {
		QualifiedName qname = new QualifiedName(name);
		if(declarations.containsKey(name)) {
			conflicts.add(new ScopeConflict(name, declarations.get(name), id));
		}else if(definitions.containsKey(qname)) {
			conflicts.add(new ScopeConflict(name, definitions.get(qname), id));
		}else {
			declarations.put(name, id);
		}
	}
	
	public void defineLocal(QualifiedName name, UID id) {
		if(name.getPrefix().isEmpty() && declarations.containsKey(name.getBase())) {
			conflicts.add(new ScopeConflict(name, declarations.get(name.getBase()), id));
		}else if(definitions.containsKey(name)) {
			conflicts.add(new ScopeConflict(name, definitions.get(name), id));
		}else {
			definitions.put(name,  id);
		}
	}
	
	public void defineLocal(String name, UID id) {
		defineLocal(new QualifiedName(name), id);
	}
	
	public void defineGlobal(QualifiedName name, UID id) {
		defineLocal(name, id);
	}
	
	public void defineGlobal(String name, UID id) {
		defineGlobal(new QualifiedName(name), id);
	}
	
	public void reference(QualifiedName name, UID from) {
		if(name.getPrefix().isEmpty() && declarations.containsKey(name.getBase())) {
			references.put(from, declarations.get(name.getBase()));
		}else if(definitions.containsKey(name)) {
			references.put(from, definitions.get(name));
		}else{
			danglingReferences.add(from);
		}
	}
	
}
