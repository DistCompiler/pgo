package pgo.model.golang;

import java.util.List;

import pgo.scope.UID;

public abstract class ASTBuilder {
	
	public abstract TypeName defineType(String nameHint, Type type);
	
	public abstract void addImport(String name);
	
	public abstract BlockBuilder defineFunction(UID uid, String nameHint, List<FunctionArgument> arguments, List<FunctionArgument> returnTypes);
	
	public BlockBuilder defineFunction(String nameHint, List<FunctionArgument> arguments, List<FunctionArgument> returnTypes) {
		return defineFunction(new UID(), nameHint, arguments, returnTypes);
	}
	
	protected abstract void addBlock(Block block);
	
	protected abstract void addFunction(FunctionDeclaration fn);

	protected abstract void addStatement(Statement s);

}
