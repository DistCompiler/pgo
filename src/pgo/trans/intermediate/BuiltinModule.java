package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.Map;

import pgo.scope.ChainMap;

public class BuiltinModule {
	
	Map<String, BuiltinOperator> operators;
	
	public BuiltinModule() {
		this.operators = new HashMap<>();
	}
	
	public BuiltinModule(BuiltinModule exts) {
		this.operators = new ChainMap<>(exts.operators);
	}
	
	public void addOperator(String name, BuiltinOperator op) {
		operators.put(name, op);
	}
	
	public Map<String, BuiltinOperator> getOperators(){
		return operators;
	}
	
	public void addDefinitionsToScope(TLAScopeBuilder scope) {
		for(Map.Entry<String, BuiltinOperator> op : operators.entrySet()) {
			scope.defineGlobal(op.getKey(), op.getValue().getUID());
		}
	}

	public void addDefinitionsToRegistry(DefinitionRegistry registry) {
		for(Map.Entry<String, BuiltinOperator> op : operators.entrySet()) {
			registry.addOperator(op.getValue().getUID(), op.getValue());
		}
	}

}
