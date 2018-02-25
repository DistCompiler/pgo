package pgo.model.distsys;

import pgo.model.golang.Expression;
import pgo.model.golang.GoProgram;
import pgo.model.golang.Statement;
import pgo.model.intermediate.PGoVariable;

import java.util.Vector;
import java.util.stream.Stream;

// TODO flesh out this interface
public interface StateStrategy {
	void generateConfig(GoProgram go);
	void generateGlobalVariables(GoProgram go);
	void initializeGlobalVariables(GoProgram go);
	void lock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars);
	void unlock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars);

	// FIXME flesh these out
	void setVar(PGoVariable var, Expression rhs, Vector<Expression> exps);
	String getVar(PGoVariable var);
}
