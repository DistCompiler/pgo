package pgo.model.golang;

import pgo.model.golang.type.GoInterfaceTypeField;
import pgo.model.golang.type.GoStructTypeField;
import pgo.model.golang.type.GoType;

public abstract class GoNodeVisitor<T, E extends Throwable> {

	public abstract T visit(GoModule module) throws E;
	public abstract T visit(GoStatement statement) throws E;
	public abstract T visit(GoDeclaration declaration) throws E;
	public abstract T visit(GoType type) throws E;
	public abstract T visit(GoStructTypeField structTypeField) throws E;
	public abstract T visit(GoSwitchCase switchCase) throws E;
	public abstract T visit(GoLabelName labelName) throws E;
	public abstract T visit(GoFunctionArgument functionArgument) throws E;
	public abstract T visit(GoExpression expression) throws E;
	public abstract T visit(GoInterfaceTypeField interfaceTypeField) throws E;
	public abstract T visit(GoSelectCase selectCase) throws E;
	public abstract T visit(GoStructLiteralField structLiteralField) throws E;
}
