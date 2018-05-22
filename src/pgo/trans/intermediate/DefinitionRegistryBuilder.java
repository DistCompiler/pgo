package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.model.tla.PGoTLAFunctionDefinition;
import pgo.model.tla.PGoTLAModule;
import pgo.model.tla.PGoTLAOperatorDefinition;
import pgo.model.tla.PGoTLAUnit;
import pgo.scope.UID;

public class DefinitionRegistryBuilder {
	
	Map<UID, DefinitionType> types;
	Map<String, PGoTLAModule> modules;
	Map<UID, PGoTLAUnit> definitions;
	
	public DefinitionRegistryBuilder() {
		this.types = new HashMap<>();
		this.modules = new HashMap<>();
		this.definitions = new HashMap<>();
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
	
	public void addFunctionDefinition(PGoTLAFunctionDefinition def) {
		if(!definitions.containsKey(def.getUID())) {
			definitions.put(def.getUID(), def);
		}
	}

	public PGoTLAModule findModule(String name) {
		return modules.get(name);
	}

}
