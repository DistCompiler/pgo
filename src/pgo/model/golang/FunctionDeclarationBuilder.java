package pgo.model.golang;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import pgo.scope.UID;

public class FunctionDeclarationBuilder {

	private ASTBuilder parent;
	private String name;
	
	private List<FunctionArgument> arguments;
	private List<FunctionArgument> returnValues;
	private FunctionArgument receiver;
	private NameCleaner nameCleaner;
	private Map<UID, VariableName> nameMap;

	public FunctionDeclarationBuilder(ASTBuilder parent, String name, NameCleaner nameCleaner, Map<UID, VariableName> nameMap) {
		this.parent = parent;
		this.name = name;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		
		this.receiver = null;
		this.arguments = new ArrayList<>();
		this.returnValues = new ArrayList<>();
	}
	
	public VariableName addArgument(String nameHint, Type type) {
		String actualName = nameCleaner.cleanName(nameHint);
		arguments.add(new FunctionArgument(actualName, type));
		return new VariableName(actualName);
	}
	
	public void addReturn(Type type) {
		returnValues.add(new FunctionArgument(null, type));
	}
	
	public VariableName addReturn(String nameHint, Type type) {
		String actualName = nameCleaner.cleanName(nameHint);
		returnValues.add(new FunctionArgument(actualName, type));
		return new VariableName(actualName);
	}
	
	public VariableName setReceiver(String nameHint, Type type) {
		String actualName = nameCleaner.cleanName(nameHint);
		receiver = new FunctionArgument(actualName, type);
		return new VariableName(actualName);
	}
	
	public BlockBuilder getBlockBuilder() {
		return new BlockBuilder(parent, nameCleaner, nameMap, new NameCleaner(), block -> {
			parent.addFunction(new FunctionDeclaration(name, receiver, arguments, returnValues, block));
		});
	}

}
