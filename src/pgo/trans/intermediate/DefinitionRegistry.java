package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAUnit;
import pgo.scope.UID;

public class DefinitionRegistry {
	
	Map<UID, DefinitionType> types;
	Map<String, PGoTLAModule> modules;
	Map<UID, PGoTLAUnit> definitions;
	Map<UID, OperatorAccessor> operators;
	Map<UID, UID> references;
	
	public DefinitionRegistry() {
		this.types = new HashMap<>();
		this.modules = new HashMap<>();
		this.definitions = new HashMap<>();
		this.operators = new HashMap<>();
		this.references = new HashMap<>();
	}
	
	public Map<UID, UID> getReferences(){
		return references;
	}
	
	public void addModule(PGoTLAModule module) {
		if(!modules.containsKey(module.getName().getId())){
			modules.put(module.getName().getId(), module);
		}
	}
	
	public void addOperatorDefinition(PGoTLAOperatorDefinition def) {
		if(!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}
	
	public void addOperator(UID uid, OperatorAccessor op) {
		operators.put(uid, op);
	}
	
	public void addFunctionDefinition(PGoTLAFunctionDefinition def) {
		if(!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}
	
	public UID followReference(UID from) {
		if(!references.containsKey(from)) {
			throw new RuntimeException("internal compiler error");
		}
		return references.get(from);
	}
	
	public OperatorAccessor findOperator(UID id) {
		if(!operators.containsKey(id)) {
			throw new RuntimeException("internal compiler error");
		}
		return operators.get(id);
	}

	public PGoTLAModule findModule(String name) {
		return modules.get(name);
	}

}
