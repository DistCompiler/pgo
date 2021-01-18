package pgo.trans.intermediate;

import pgo.scope.ChainMap;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

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

}
