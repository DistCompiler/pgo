package pgo.model.distsys;

import pgo.PGoNetOptions;
import pgo.model.golang.*;
import pgo.model.intermediate.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.Vector;
import java.util.stream.Stream;

public class CentralizedStateStrategy implements StateStrategy {
	public static final String GLOBAL_STATE_OBJECT = "globalState";

	private PGoNetOptions.StateOptions stateOptions;

	public CentralizedStateStrategy(PGoNetOptions.StateOptions stateOptions) {
		this.stateOptions = stateOptions;
	}

	@Override
	public void generateConfig(GoProgram go) {
		Vector<Statement> topLevelMain = go.getMain().getBody();
		topLevelMain.add(new FunctionCall("datatypes.GobInit", new Vector<>()));
		topLevelMain.add(new Assignment(
				new Vector<>(Collections.singletonList("endpoints")),
				new Token(String.format("%s{%s}", new PGoCollectionType.PGoSlice("string").toGo(),
						String.join(", ",
								stateOptions.endpoints.stream().map(e -> String.format("\"%s\"", e))
										.toArray(String[]::new)))),
				true));

		topLevelMain.add(new VariableDeclaration(
				"err", PGoType.inferFromGoTypeName("error"), null, false, false, false
		));

		topLevelMain.add(new Comment("is this instance a server?", false));
		// TODO fix state server init
		topLevelMain.add(new For(
				new Token("_, endpoint := range endpoints"),
				new Vector<>(Collections.singletonList(
						new If(new Token("endpoint == ipAddr"),
								new Vector<>(Arrays.asList(
										new Assignment(
												new Vector<>(Collections.singletonList("server")),
												new FunctionCall("distsys.NewStateServer", new Vector<>(Collections.singletonList(new Token("ipAddr")))),
												true
										),
										new Assignment(
												new Vector<>(Collections.singletonList("server.HeartBeatInterval")),
												new Token(Integer.toString(stateOptions.timeout)),
												false),
										new Token("go server.Serve()"),
										new Assignment(
												new Vector<>(Collections.singletonList(GLOBAL_STATE_OBJECT)),
												new Token("server"),
												false),
										new Token("break")
								)),
								new Vector<>())))
		));

		go.getImports().addImport("regexp");
		topLevelMain.add(new If(new Token(String.format("%s == nil", GLOBAL_STATE_OBJECT)),
				new Vector<>(Arrays.asList(
						new Comment("this instance is a client", false),
						new For(new Vector<>(Arrays.asList(
								new Assignment(
										new Vector<>(Arrays.asList(GLOBAL_STATE_OBJECT, "err")),
										new FunctionCall("distsys.NewCentralizedState",
												new Vector<>(Arrays.asList(new Token("ipAddr"), new Token("endpoints")))),
										false),
								new If(new SimpleExpression(new Vector<>(Arrays.asList(
										new Token("err == nil"),
										new Token("||"),
										new Token("!"),
										new FunctionCall(
												"regexp.MustCompile(\".*connection refused.*\").MatchString",
												new Vector<>(Collections.singletonList(
														new FunctionCall("err.Error", new Vector<>()))))))),
										new Vector<>(Collections.singletonList(new Token("break"))),
										new Vector<>())))))),
				new Vector<>()));

		go.getImports().addImport("os");
		Vector<Statement> ifBody = new Vector<Statement>() {
			{
				add(new Comment("handle error - could not initialize global state", false));
				add(new FunctionCall("os.Exit",
						new Vector<>(Collections.singletonList(new Token("1")))));
			}
		};

		If errIf = new If(new Token("err != nil"), ifBody, new Vector<>());
		topLevelMain.add(errIf);
	}

	@Override
	public void generateGlobalVariables(GoProgram go) {
		VariableDeclaration stateDecl = new VariableDeclaration(GLOBAL_STATE_OBJECT,
				new PGoMiscellaneousType.State(), null, false, false, false);

		go.addGlobal(stateDecl);
	}

	@Override
	public void initializeGlobalState(GoProgram go) {
		// TODO
		Vector<Statement> topLevelMain = go.getMain().getBody();

		for (VariableDeclaration gVar : go.getGlobals()) {
			if (!gVar.isRemote()) {
				continue;
			}

			go.getImports().addImport("strconv");
			topLevelMain.add(initializeGlobalVariable(gVar));
		}

		topLevelMain.add(new SimpleExpression(new Vector<>(Arrays.asList(
				new Token("<-"),
				new FunctionCall("StartChan", new Vector<>(), new Token(GLOBAL_STATE_OBJECT))))));
	}

	@Override
	public void lock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		stmts.add(new FunctionCall("Lock", new Vector<Expression>() {
			{
				add(new Token("selfStr"));
				add(new Token("\"" + Integer.toString(lockGroup) + "\""));
			}
		}, new Token(GLOBAL_STATE_OBJECT)));
		fetchDataForCurrentLockGroup(stmts, vars);
	}

	@Override
	public void unlock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		pushDataForCurrentLockGroup(stmts, vars);
		stmts.add(new FunctionCall(
				"Unlock",
				new Vector<>(Arrays.asList(new Token("selfStr"),
						new Token("\"" + Integer.toString(lockGroup) + "\""))),
				new Token(GLOBAL_STATE_OBJECT)));
	}

	@Override
	public void setVar(PGoVariable var, Expression rhs, Vector<Expression> exps) {
		// assigning to a global, remote variable (managed by etcd)
		Vector<Expression> params = new Vector<>(Arrays.asList(new Token("\"" + var.getName() + "\""), rhs));
		exps.add(new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT)));
	}

	@Override
	public String getVar(PGoVariable var) {
		return String.format("*%s.Get(\"%s\", &%s).(*%s)", GLOBAL_STATE_OBJECT, var.getName(), var.getName(), var.getType());
	}

	private void fetchDataForCurrentLockGroup(Vector<Statement> stmts, Stream<PGoVariable> vars) {
		StateStrategy stateStrategy = this;
		vars.forEach(var ->
				stmts.add(new Assignment(
						new Vector<>(Collections.singletonList(var.getName())),
						new VariableReference(var.getName(), var, false, stateStrategy),
						false))
		);
	}

	private void pushDataForCurrentLockGroup(Vector<Statement> stmts, Stream<PGoVariable> vars) {
		vars.forEach(var -> {
			Vector<Expression> params = new Vector<>(Arrays.asList(new Token("\"" + var.getName() + "\""), new Token(var.getName())));
			stmts.add(new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT)));
		});
	}

	// given a remote, global variable declaration, this generates code to initialize
	// it with a proper value. Since multiple processes might be running at the same
	// time, initialization must be made only once. This is achieved by making use
	// of the locking functionality available in the `pgo/distsys' package.
	private Statement initializeGlobalVariable(VariableDeclaration decl) {
		// TODO
		Expression initVal = decl.getDefaultValue();
		if (initVal == null) {
			initVal = new Token(decl.getName());
		}
		Vector<Expression> params = new Vector<>(Arrays.asList(new Token("\"" + decl.getName() + "\""), initVal));
		return new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT));
	}
}
