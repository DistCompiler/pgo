package pgo.model.mpcal;

public abstract class ModularPlusCalNodeVisitor<T, E extends Throwable> {

	public abstract T visit(ModularPlusCalArchetype modularPlusCalArchetype) throws E;
	public abstract T visit(ModularPlusCalInstance modularPlusCalInstance) throws E;
	public abstract T visit(ModularPlusCalMappingMacro modularPlusCalMappingMacro) throws E;
	public abstract T visit(ModularPlusCalVariableDeclaration modularPlusCalVariableDeclaration) throws E;

}
