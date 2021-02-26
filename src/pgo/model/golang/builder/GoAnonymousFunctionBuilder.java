package pgo.model.golang.builder;

import pgo.model.golang.*;
import pgo.model.golang.type.GoType;
import pgo.scope.UID;
import pgo.trans.passes.codegen.NameCleaner;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class GoAnonymousFunctionBuilder {
	
	private final GoASTBuilder parent;
	private final NameCleaner nameCleaner;
	private final Map<UID, GoVariableName> nameMap;
	
	private final List<GoFunctionParameter> arguments;
	private final List<GoFunctionParameter> returnValues;
	private GoBlock block;
	
	public GoAnonymousFunctionBuilder(GoASTBuilder parent, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap) {
		this.parent = parent;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		
		this.arguments = new ArrayList<>();
		this.returnValues = new ArrayList<>();
		this.block = null;
	}
	
	public GoVariableName addArgument(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		arguments.add(new GoFunctionParameter(actualName, type));
		return new GoVariableName(actualName);
	}
	
	public void addReturn(GoType type) {
		returnValues.add(new GoFunctionParameter(null, type));
	}
	
	public GoAnonymousFunction getFunction() {
		return new GoAnonymousFunction(arguments, returnValues, block);
	}
	
	public GoBlockBuilder getBlockBuilder() {
		return new GoBlockBuilder(parent, nameCleaner, nameMap, new NameCleaner(), block -> this.block = block);
	}

}
