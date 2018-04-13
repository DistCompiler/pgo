package pgo.model.distsys;

import pgo.PGoNetOptions;
import pgo.model.golang.*;
import pgo.model.intermediate.*;

import java.util.*;
import java.util.stream.Collectors;
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

		String globalValues = "map[string]interface{}{\n" + go.getGlobals()
				.stream()
				.filter(VariableDeclaration::isRemote)
				.map(g ->String.format(
						"\"%s\": &%s,\n",
						g.getName(),
						Optional.ofNullable(g.getDefaultValue()).orElse(new Token(g.getName())).toGo().get(0)))
				.collect(Collectors.joining()) +
				"}";
		topLevelMain.add(new Comment("is this instance a server?", false));
		// TODO fix state server init
		topLevelMain.add(new For(
				new Token("_, endpoint := range endpoints"),
				new Vector<>(Collections.singletonList(
						new If(new Token("endpoint == ipAddr"),
								new Vector<>(Arrays.asList(
										new Assignment(
												new Vector<>(Collections.singletonList("server")),
												new FunctionCall("distsys.NewStateServer",
														new Vector<>(Arrays.asList(new Token("ipAddr"),
																new Token(globalValues)))),
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

		topLevelMain.add(new SimpleExpression(new Vector<>(Arrays.asList(
				new Token("<-"),
				new FunctionCall("StartChan", new Vector<>(), new Token(GLOBAL_STATE_OBJECT))))));
	}

	@Override
	public void lock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		List<PGoVariable> vs = vars.sorted(Comparator.comparing(PGoVariable::getName)).collect(Collectors.toList());
		String lockName = "_lg" + lockGroup;
		String varName = "_v" + lockGroup;
		Expression acquireCall = new FunctionCall(
				"Acquire",
				new Vector<>(Arrays.asList(
						new Token("[]string{}"),
						new Token("[]string{" +
								vs.stream().map(v -> String.format("\"%s\",", v.getName())).collect(Collectors.joining()) +
								"}"))) ,
				new Token(GLOBAL_STATE_OBJECT));
		stmts.add(new Assignment(new Vector<>(Arrays.asList(lockName, varName)), acquireCall, true));
		for (PGoVariable v : vs) {
			stmts.add(new Assignment(
					new Vector<>(Collections.singleton(v.getName())),
					new Token(String.format("*%s[\"%s\"].(*%s)", varName, v.getName(), v.getType())),
					false));
		}
	}

	@Override
	public void unlock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		String lockName = "_lg" + lockGroup;
		stmts.add(new FunctionCall(
				"Release",
				new Vector<>(Arrays.asList(
						new Token(lockName),
						new Token("[]interface{}{" +
								vars.sorted(Comparator.comparing(PGoVariable::getName))
										.map(v -> String.format("&%s", v.getName()))
										.collect(Collectors.joining()) +
								"}"))) ,
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
}
