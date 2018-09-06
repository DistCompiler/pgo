package pgo.model.pcal;

import pgo.model.mpcal.ModularPlusCalYield;

public abstract class PlusCalStatementVisitor<T, E extends Throwable>{
	public abstract T visit(PlusCalLabeledStatements labeledStatements) throws E;
	public abstract T visit(PlusCalWhile plusCalWhile) throws E;
	public abstract T visit(PlusCalIf plusCalIf) throws E;
	public abstract T visit(PlusCalEither plusCalEither) throws E;
	public abstract T visit(PlusCalAssignment plusCalAssignment) throws E;
	public abstract T visit(PlusCalReturn plusCalReturn) throws E;
	public abstract T visit(PlusCalSkip skip) throws E;
	public abstract T visit(PlusCalCall plusCalCall) throws E;
	public abstract T visit(PlusCalMacroCall macroCall) throws E;
	public abstract T visit(PlusCalWith with) throws E;
	public abstract T visit(PlusCalPrint plusCalPrint) throws E;
	public abstract T visit(PlusCalAssert plusCalAssert) throws E;
	public abstract T visit(PlusCalAwait plusCalAwait) throws E;
	public abstract T visit(PlusCalGoto plusCalGoto) throws E;
	public abstract T visit(ModularPlusCalYield modularPlusCalYield) throws E;
}
