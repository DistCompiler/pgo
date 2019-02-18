package pgo.model.golang.builder;

import pgo.InternalCompilerError;
import pgo.model.golang.*;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.scope.UID;
import pgo.trans.passes.codegen.NameCleaner;

import java.util.*;

public class GoModuleBuilder extends GoASTBuilder {

	private String name;
	private String pack;
	private Set<String> imports;
	private Map<UID, GoVariableName> nameMap;
	private List<GoDeclaration> declarations;
	private NameCleaner nameCleaner;

	public GoModuleBuilder(String name, String pack) {
		this.name = name;
		this.pack = pack;
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
	public GoTypeName defineType(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		declarations.add(new GoTypeDeclaration(actualName, type));
		return new GoTypeName(actualName);
	}

	@Override
	public GoFunctionDeclarationBuilder defineFunction(UID uid, String nameHint) {
		String actualName = nameCleaner.cleanName(nameHint);
		nameMap.put(uid, new GoVariableName(actualName));
		return new GoFunctionDeclarationBuilder(this, actualName, nameCleaner.child(), nameMap);
	}

	public GoVariableName defineGlobal(UID uid, String nameHint, GoType type, GoExpression value) {
		String actualName = nameCleaner.cleanName(nameHint);
		GoVariableName vName = new GoVariableName(actualName);
		nameMap.put(uid, vName);
		declarations.add(new GoVariableDeclaration(actualName, type, value));
		return vName;
	}

	public GoVariableName defineGlobal(UID uid, String nameHint, GoExpression value) {
		return defineGlobal(uid, nameHint, null, value);
	}

	public GoVariableName defineGlobal(UID uid, String nameHint, GoType type) {
		return defineGlobal(uid, nameHint, type, null);
	}

	public GoModule getModule() {
		return new GoModule(name, new GoVariableName(this.pack), new ArrayList<>(imports), declarations);
	}

	@Override
	protected void addBlock(GoBlock block) {
		throw new InternalCompilerError();
	}

	@Override
	protected void addFunction(GoFunctionDeclaration fn) {
		declarations.add(fn);
	}

	@Override
	public void addStatement(GoStatement s) {
		throw new InternalCompilerError();
	}

	@Override
	public void addImport(String name) {
		imports.add(name);
	}
}
