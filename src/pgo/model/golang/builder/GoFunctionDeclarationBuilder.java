package pgo.model.golang.builder;

import pgo.model.golang.GoFunctionParameter;
import pgo.model.golang.GoFunctionDeclaration;
import pgo.model.golang.GoVariableName;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.model.golang.type.GoType;
import pgo.scope.UID;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class GoFunctionDeclarationBuilder {
	private final GoASTBuilder parent;
	private final String name;

	private final List<GoFunctionParameter> params;
	private final List<GoFunctionParameter> returnValues;
	private GoFunctionParameter receiver;
	private final NameCleaner nameCleaner;
	private final Map<UID, GoVariableName> nameMap;

	public GoFunctionDeclarationBuilder(GoASTBuilder parent, String name, NameCleaner nameCleaner,
	                                    Map<UID, GoVariableName> nameMap) {
		this.parent = parent;
		this.name = name;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;

		this.receiver = null;
		this.params = new ArrayList<>();
		this.returnValues = new ArrayList<>();
	}

	public GoVariableName addParameter(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		params.add(new GoFunctionParameter(actualName, type));
		return new GoVariableName(actualName);
	}

	public void addReturn(GoType type) {
		returnValues.add(new GoFunctionParameter(null, type));
	}

	public GoVariableName addReturn(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		returnValues.add(new GoFunctionParameter(actualName, type));
		return new GoVariableName(actualName);
	}

	public GoVariableName setReceiver(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		receiver = new GoFunctionParameter(actualName, type);
		return new GoVariableName(actualName);
	}

	public GoBlockBuilder getBlockBuilder() {
		return new GoBlockBuilder(parent, nameCleaner, nameMap, new NameCleaner(), block -> {
			parent.addFunction(new GoFunctionDeclaration(name, receiver, params, returnValues, block));
		});
	}

}
