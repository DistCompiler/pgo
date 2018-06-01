package pgo.model.golang;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import pgo.scope.UID;

public class AnonymousFunctionBuilder {
	
	private ASTBuilder parent;
	private NameCleaner nameCleaner;
	private Map<UID, VariableName> nameMap;
	
	private List<FunctionArgument> arguments;
	private List<FunctionArgument> returnValues;
	private Block block;
	
	public AnonymousFunctionBuilder(ASTBuilder parent, NameCleaner nameCleaner, Map<UID, VariableName> nameMap) {
		this.parent = parent;
		this.nameCleaner = nameCleaner;
		this.nameMap = nameMap;
		
		this.arguments = new ArrayList<>();
		this.returnValues = new ArrayList<>();
		this.block = null;
	}
	
	public VariableName addArgument(String nameHint, Type type) {
		String actualName = nameCleaner.cleanName(nameHint);
		arguments.add(new FunctionArgument(actualName, type));
		return new VariableName(actualName);
	}
	
	public void addReturn(Type type) {
		returnValues.add(new FunctionArgument(null, type));
	}
	
	public AnonymousFunction getFunction() {
		return new AnonymousFunction(arguments, returnValues, block);
	}
	
	public BlockBuilder getBlockBuilder() {
		return new BlockBuilder(parent, nameCleaner, nameMap, new NameCleaner(), block -> this.block = block);
	}

}
