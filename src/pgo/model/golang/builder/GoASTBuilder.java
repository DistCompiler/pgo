package pgo.model.golang.builder;

import pgo.model.golang.GoBlock;
import pgo.model.golang.GoFunctionDeclaration;
import pgo.model.golang.GoStatement;
import pgo.model.golang.type.GoType;
import pgo.model.golang.type.GoTypeName;
import pgo.scope.UID;

public abstract class GoASTBuilder {
	
	public abstract GoTypeName defineType(String nameHint, GoType type);
	
	public abstract void addImport(String name);
	
	public abstract GoFunctionDeclarationBuilder defineFunction(UID uid, String nameHint);
	
	public GoFunctionDeclarationBuilder defineFunction(String nameHint) {
		return defineFunction(new UID(), nameHint);
	}
	
	protected abstract void addBlock(GoBlock block);
	
	protected abstract void addFunction(GoFunctionDeclaration fn);

	public abstract void addStatement(GoStatement s);

}
