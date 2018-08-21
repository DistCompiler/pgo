package pgo.model.golang.builder;

import pgo.model.golang.GoFunctionArgument;
import pgo.model.golang.GoFunctionDeclaration;
import pgo.model.golang.GoVariableName;
import pgo.model.golang.NameCleaner;
import pgo.model.golang.type.GoType;
import pgo.scope.UID;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class GoFunctionDeclarationBuilder {

	private GoASTBuilder parent;
	private String name;
	
	private List<GoFunctionArgument> arguments;
	private List<GoFunctionArgument> returnValues;
	private GoFunctionArgument receiver;
	private NameCleaner nameCleaner;
	private Map<UID, GoVariableName> nameMap;

	public GoFunctionDeclarationBuilder(GoASTBuilder parent, String name, NameCleaner nameCleaner, Map<UID, GoVariableName> nameMap) {
		this.parent = parent;
		this.name = name;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		
		this.receiver = null;
		this.arguments = new ArrayList<>();
		this.returnValues = new ArrayList<>();
	}
	
	public GoVariableName addArgument(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		arguments.add(new GoFunctionArgument(actualName, type));
		return new GoVariableName(actualName);
	}
	
	public void addReturn(GoType type) {
		returnValues.add(new GoFunctionArgument(null, type));
	}
	
	public GoVariableName addReturn(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		returnValues.add(new GoFunctionArgument(actualName, type));
		return new GoVariableName(actualName);
	}
	
	public GoVariableName setReceiver(String nameHint, GoType type) {
		String actualName = nameCleaner.cleanName(nameHint);
		receiver = new GoFunctionArgument(actualName, type);
		return new GoVariableName(actualName);
	}
	
	public GoBlockBuilder getBlockBuilder() {
		return new GoBlockBuilder(parent, nameCleaner, nameMap, new NameCleaner(), block -> {
			parent.addFunction(new GoFunctionDeclaration(name, receiver, arguments, returnValues, block));
		});
	}

}
