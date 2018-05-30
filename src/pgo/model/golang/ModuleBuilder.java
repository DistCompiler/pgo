package pgo.model.golang;

import java.util.*;

import pgo.scope.UID;

public class ModuleBuilder extends ASTBuilder {
	
	private String name;
	private Set<String> imports;
	private Map<UID, VariableName> nameMap;
	private List<Declaration> declarations;
	private NameCleaner nameCleaner;
	
	public ModuleBuilder(String name) {
		this.name = name;
		this.nameCleaner = new NameCleaner(new HashSet<>(Arrays.asList(
				"break",
				"default",
				"func",
				"interface",
				"select",
				"case",
				"defer",
				"go",
				"map",
				"struct",
				"chan",
				"else",
				"goto",
				"package",
				"switch",
				"const",
				"fallthrough",
				"if",
				"range",
				"type",
				"continue",
				"for",
				"import",
				"return",
				"var")));
		this.imports = new TreeSet<>();
		this.nameMap = new HashMap<>();
		this.declarations = new ArrayList<>();
	}
	
	@Override
	public TypeName defineType(String nameHint, Type type) {
		String actualName = nameCleaner.cleanName(nameHint);
		declarations.add(new TypeDeclaration(actualName, type));
		return new TypeName(actualName);
	}
	
	@Override
	public FunctionDeclarationBuilder defineFunction(UID uid, String nameHint) {
		String actualName = nameCleaner.cleanName(nameHint);
		nameMap.put(uid, new VariableName(actualName));
		return new FunctionDeclarationBuilder(this, actualName, nameCleaner.child(), nameMap);
	}
	
	public VariableName defineGlobal(UID uid, String nameHint, Type type, Expression value) {
		String actualName = nameCleaner.cleanName(nameHint);
		VariableName vName = new VariableName(actualName);
		nameMap.put(uid, vName);
		declarations.add(new VariableDeclaration(actualName, type, value));
		return vName;
	}
	
	public VariableName defineGlobal(UID uid, String nameHint, Expression value) {
		return defineGlobal(uid, nameHint, null, value);
	}
	
	public VariableName defineGlobal(UID uid, String nameHint, Type type) {
		return defineGlobal(uid, nameHint, type, null);
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
	public void addStatement(Statement s) {
		throw new RuntimeException("internal compiler error");
	}

	@Override
	public void addImport(String name) {
		imports.add(name);
	}
}
