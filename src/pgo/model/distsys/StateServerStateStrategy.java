package pgo.model.distsys;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Vector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import pgo.PGoNetOptions;
import pgo.PGoNetOptions.StateOptions;
import pgo.model.golang.Assignment;
import pgo.model.golang.Builder;
import pgo.model.golang.Expression;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.GoProgram;
import pgo.model.golang.If;
import pgo.model.golang.MapConstructor;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;
import pgo.model.golang.VariableDeclaration;
import pgo.model.intermediate.PGoMiscellaneousType;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;

public class StateServerStateStrategy implements StateStrategy {
	private static final String GLOBAL_STATE_OBJECT = "globalState";
	private static final String LOCK_OBJECT = "remoteLock";
	private static final String VARS_OBJECT = "remoteVars";

	private static final String PEERS_VAR = "peers";
	private static final String COORDINATOR_VAR = "coordinator";
	private static final String SELF_VAR = "ipAddr";

	private StateOptions stateOptions;

	public StateServerStateStrategy(PGoNetOptions.StateOptions stateOptions) {
		this.stateOptions = stateOptions;
	}

	@Override
	public void generateConfig(GoProgram go) {
		// make sure distsys is available
		go.getImports().addImport("pgo/distsys");

		List<Statement> topLevelMain = go.getMain().getBody();
		topLevelMain.add(new Assignment(
				new Vector<>(Collections.singletonList(PEERS_VAR)),
				Builder.sliceLiteral(
						PGoType.inferFromGoTypeName("string"),
						stateOptions.peers
						.stream()
						.map(Builder::stringLiteral)
						.collect(Collectors.toList())),
				true));

		MapConstructor globalValues = Builder.mapLiteral(
				PGoType.inferFromGoTypeName("string"),
				PGoType.inferFromGoTypeName("interface{}"),
				go.getGlobals()
				.stream()
				.filter(VariableDeclaration::isRemote)
				.map(g -> new Object[] {
						Builder.stringLiteral(g.getName()),
						Optional.ofNullable(
								g.getDefaultValue())
						.orElse(
								new Token(g.getName()))
				}).collect(Collectors.toList()));

		topLevelMain.add(new Assignment(
						new Vector<>(Arrays.asList(COORDINATOR_VAR)),
						new Token(PEERS_VAR + "[0]"),
						true));

		topLevelMain.add(new Assignment(
								new Vector<>(Arrays.asList(GLOBAL_STATE_OBJECT, "err")),
								new FunctionCall("distsys.NewStateServer",
										new Vector<>(Arrays.asList(
												new Token(PEERS_VAR),
												new Token(SELF_VAR),
												new Token(COORDINATOR_VAR),
												globalValues,
												new FunctionCall("distsys.NewRandomMigrate",
														new Vector<>(Arrays.asList(
																		new Token(SELF_VAR))))))),
								false)
						);

		topLevelMain.add(new If(new Token("err != nil"),
				Builder.stmts(
						new FunctionCall("panic",
								new Vector<>(Collections.singleton(new Token("err"))))
				),
				Builder.stmts()
				));

	}

	@Override
	public void generateGlobalVariables(GoProgram go) {
		go.addGlobal(
				new VariableDeclaration(
						"err",
						PGoType.inferFromGoTypeName("error"),
						null, false, false, false));
		go.addGlobal(
				new VariableDeclaration(
						GLOBAL_STATE_OBJECT,
						new PGoMiscellaneousType.StateServer(),
						null, false, false, false));
		go.addGlobal(
				new VariableDeclaration(
						LOCK_OBJECT,
						new PGoMiscellaneousType.StateServerReleaseSet(),
						null, false, false, false));
		go.addGlobal(
				new VariableDeclaration(
						VARS_OBJECT,
						new PGoMiscellaneousType.StateServerValueMap(),
						null, false, false, false));

	}

	@Override
	public void lock(int lockGroup, List<Statement> stmts, Stream<PGoVariable> vars) {
		List<PGoVariable> vList = vars.collect(Collectors.toList());

		List<Expression> varNamesStr = vList
				.stream()
				.map(v -> Builder.stringLiteral(v.getName()))
				.collect(Collectors.toList());

		stmts.add(new Token("_ = selfStr // bad warnings bad"));

		stmts.add(
				new Assignment(new Vector<>(Arrays.asList(LOCK_OBJECT, VARS_OBJECT, "err")),
				new FunctionCall(
						"Acquire",
						new Vector<>(Collections.singleton(
								Builder.structLiteral(
										new PGoMiscellaneousType.StateServerAcquireSet(),
										new Object[] {
												"ReadNames", Builder.sliceLiteral(
														PGoType.inferFromGoTypeName("string"),
														varNamesStr)
										},
										new Object[] {
												"WriteNames", Builder.sliceLiteral(
														PGoType.inferFromGoTypeName("string"),
														varNamesStr)
										}
								))),
						new Token(GLOBAL_STATE_OBJECT)),
				false));

		// pull all values out of the map and into globals
		for(PGoVariable v : vList) {
			stmts.add(
					new Assignment(
							new Vector<>(Collections.singleton(v.getName())),
							new Token(
									VARS_OBJECT + "[" + String.join(
											"",
											Builder.stringLiteral(v.getName()).toGo())
									+ "].(" + v.getType().toGo() + ")"),
							false));
		}

	}

	@Override
	public void unlock(int lockGroup, List<Statement> stmts, Stream<PGoVariable> vars) {
		List<String> varNames = vars.map(PGoVariable::getName).collect(Collectors.toList());

		Vector<Expression> releaseNames = new Vector<>();
		releaseNames.add(new Token(LOCK_OBJECT));
		releaseNames.addAll(varNames
				.stream()
				.map(Token::new)
				.collect(Collectors.toList()));

		stmts.add(
				new Assignment(
						new Vector<>(Collections.singleton("err")),
						new FunctionCall("Release", releaseNames, new Token(GLOBAL_STATE_OBJECT)),
						false));

		stmts.add(new If(new Token("err != nil"),
				Builder.stmts(new FunctionCall("panic", new Vector<>(Collections.singleton(new Token("err"))))),
				Builder.stmts()));
	}

	@Override
	public String getGlobalStateVariableName() {
		return GLOBAL_STATE_OBJECT;
	}

	@Override
	public void setVar(PGoVariable var, Expression rhs, List<Expression> exps) {
		// TODO: fix this mess, this is a terrible hack / abuse of the AST
		// since for some reason you can only use expressions to set variables, not statements?
		exps.add(new Token(String.join(
				"",
				new Assignment(new Vector<>(Collections.singleton(var.getName())), rhs, false).toGo())));
	}

	@Override
	public String getVar(PGoVariable var) {
		return var.getName();
	}

}
