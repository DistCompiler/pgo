package pgo.model.golang;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import pgo.scope.ChainSet;
import pgo.scope.UID;

public class ModuleBuilder extends ASTBuilder {
	
	private String name;
	private Set<String> names;
	private Set<String> imports;
	private Map<UID, VariableName> nameMap;
	private List<Declaration> declarations;
	
	public ModuleBuilder(String name) {
		this.name = name;
		this.names = new HashSet<>();
		this.imports = new TreeSet<>();
		this.nameMap = new HashMap<>();
		this.declarations = new ArrayList<>();
	}
	
	private String cleanName(String nameHint) {
		String actualName = nameHint;
		int count = 0;
		while(names.contains(nameHint)) {
			actualName = nameHint + count;
			++count;
		}
		return actualName;
	}
	
	@Override
	public TypeName defineType(String nameHint, Type type) {
		String actualName = cleanName(nameHint);
		declarations.add(new TypeDeclaration(actualName, type));
		return new TypeName(actualName);
	}
	
	@Override
	public BlockBuilder defineFunction(UID uid, String nameHint, List<FunctionArgument> arguments, List<FunctionArgument> returnTypes) {
		String actualName = cleanName(nameHint);
		nameMap.put(uid, new VariableName(actualName));
		return new BlockBuilder(
				this, new ChainSet<>(names), nameMap, new HashSet<>(),
				block -> addFunction(new FunctionDeclaration(actualName, null, arguments, returnTypes, block)));
	}
	
	public VariableName defineGlobal(UID uid, String nameHint, Expression value) {
		String actualName = cleanName(nameHint);
		VariableName vName = new VariableName(actualName);
		nameMap.put(uid, vName);
		declarations.add(new VariableDeclaration(actualName, value));
		return vName;
	}
	
	public Module getModule() {
		return new Module(name, new VariableName("main"), new ArrayList<>(imports), declarations);
	}

	@Override
	protected void addBlock(Block block) {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	protected void addFunction(FunctionDeclaration fn) {
		declarations.add(fn);
	}

	@Override
	protected void addStatement(Statement s) {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public void addImport(String name) {
		imports.add(name);
	}
}
