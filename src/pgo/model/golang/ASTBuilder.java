package pgo.model.golang;

import pgo.scope.UID;

public abstract class ASTBuilder {
	
	public abstract TypeName defineType(String nameHint, Type type);
	
	public abstract void addImport(String name);
	
	public abstract FunctionDeclarationBuilder defineFunction(UID uid, String nameHint);
	
	public FunctionDeclarationBuilder defineFunction(String nameHint) {
		return defineFunction(new UID(), nameHint);
	}
	
	protected abstract void addBlock(Block block);
	
	protected abstract void addFunction(FunctionDeclaration fn);

	public abstract void addStatement(Statement s);

}
