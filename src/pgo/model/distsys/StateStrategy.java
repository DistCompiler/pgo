package pgo.model.distsys;

import pgo.model.golang.Expression;
import pgo.model.golang.GoProgram;
import pgo.model.golang.Statement;
import pgo.model.intermediate.PGoVariable;

import java.util.List;
import java.util.stream.Stream;

// TODO flesh out this interface
public interface StateStrategy {
	void generateConfig(GoProgram go);
	void generateGlobalVariables(GoProgram go);
	void lock(int lockGroup, List<Statement> stmts, Stream<PGoVariable> vars);
	void unlock(int lockGroup, List<Statement> stmts, Stream<PGoVariable> vars);
	String getGlobalStateVariableName();

	// FIXME flesh these out
	void setVar(PGoVariable var, Expression rhs, List<Expression> exps);
	String getVar(PGoVariable var);
}
