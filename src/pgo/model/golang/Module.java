package pgo.model.golang;

import java.util.LinkedHashMap;
import java.util.Map;

public class Module {
	String name;
	Map<String, Type> types;
	Map<String, Expression> globals;
	Map<FunctionName, Function> functions;
	
	public Module(String name) {
		this.name = name;
		this.types = new LinkedHashMap<>();
		this.globals = new LinkedHashMap<>();
		this.functions = new LinkedHashMap<>();
	}
	
	public TypeName defineType(String name, Type type) {
		Type actual = types.putIfAbsent(name, type);
		return new TypeName(name, actual != null ? actual : type);
	}
	
	public Expression defineGlobal(String name, Type type, Expression value) {
		String realName = name;
		int counter = 0;
		while(globals.containsKey(realName)) {
			realName = name + counter;
			++counter;
		}
		globals.put(realName, value);
		return new VariableName(realName, type);
	}
	
	public Function defineFunction(Function fn) {
		FunctionName name = fn.getName();
		functions.put(name, fn);
		return fn;
	}
	
}
