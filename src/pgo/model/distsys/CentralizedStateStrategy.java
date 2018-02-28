package pgo.model.distsys;

import pgo.PGoNetOptions;
import pgo.PGoOptionException;
import pgo.model.golang.*;
import pgo.model.intermediate.PGoVariable;

import java.util.Vector;
import java.util.stream.Stream;

// The centralized state distribution strategy is similar to the etcd approach,
// but instead of using etcd as a dependency for the compile project, the state
// server is one of the PlusCal processes. The process responsible for maintaining
// distributed state is declared in the "endpoints" field of the configuration file.
//
// Assumption: When this strategy is used, only one address is specified in the
// "endpoints" array, and that is chosen to be both the process coordinator
// and state server for the entire system.
public class CentralizedStateStrategy implements StateStrategy {
    private PGoNetOptions.StateOptions stateOptions;

	public CentralizedStateStrategy(PGoNetOptions.StateOptions stateOptions) throws PGoOptionException {
	    validate(stateOptions);
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

    private void validate(PGoNetOptions.StateOptions options) throws PGoOptionException {
	    if (options.endpoints.size() != 1) {
	        throw new PGoOptionException("Centralized state strategy requires only one endpoint (found " +
                options.endpoints.size() + ")");
        }
    }
}
