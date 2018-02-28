package pgo.model.distsys;

import pgo.PGoNetOptions;
import pgo.model.golang.*;
import pgo.model.intermediate.PGoVariable;

import java.util.Vector;
import java.util.stream.Stream;

public class CentralizedStateStrategy implements StateStrategy {
    private PGoNetOptions.StateOptions stateOptions;

	public CentralizedStateStrategy(PGoNetOptions.StateOptions stateOptions) {
            this.stateOptions = stateOptions;
    }

    public void generateConfig(GoProgram go) {
	    Vector<Statement> main = go.getMain().getBody();
	    main.add(new Comment("generate config", false));
    }

    public void generateGlobalVariables(GoProgram go) {
        Vector<Statement> main = go.getMain().getBody();
        main.add(new Comment("generate global variables", false));
    }

    public void initializeGlobalState(GoProgram go) {
        Vector<Statement> main = go.getMain().getBody();
        main.add(new Comment("initializing global state", false));
    }

    public void lock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
	    stmts.add(new Comment("Locking group " + lockGroup + ".", false));
    }

    public void unlock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
        stmts.add(new Comment("Unlocking group " + lockGroup + ".", false));
    }

    public void setVar(PGoVariable var, Expression rhs, Vector<Expression> exps) {
    }

    public String getVar(PGoVariable var) {
	    return "not-implemented";
    }
}
