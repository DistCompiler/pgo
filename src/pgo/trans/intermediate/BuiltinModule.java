package pgo.trans.intermediate;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import pgo.scope.ChainMap;

public class BuiltinModule {

	Map<String, OperatorAccessor> operators;

	public BuiltinModule() {
		this.operators = new HashMap<>();
	}

	public BuiltinModule(BuiltinModule exts) {
		this.operators = new ChainMap<>(exts.operators);
	}

	public void addOperator(String name, OperatorAccessor op) {
		operators.put(name, op);
	}

	public void addOperators(List<String> names, OperatorAccessor op) {
		for (String name : names) {
			addOperator(name, op);
		}
	}

	public Map<String, OperatorAccessor> getOperators(){
		return operators;
	}

	public void addDefinitionsToScope(TLAScopeBuilder scope) {
		for(Map.Entry<String, OperatorAccessor> op : operators.entrySet()) {
			scope.defineGlobal(op.getKey(), op.getValue().getUID());
		}
	}

	public void addDefinitionsToRegistry(DefinitionRegistry registry) {
		for(Map.Entry<String, OperatorAccessor> op : operators.entrySet()) {
			registry.addOperator(op.getValue().getUID(), op.getValue());
		}
	}

}
