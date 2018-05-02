package pgo.model.distsys;

import pgo.PGoNetOptions;
import pgo.PGoOptionException;
import pgo.model.golang.*;
import pgo.model.intermediate.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.Optional;
import java.util.Vector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

// This state distribution strategy maintains all the distributed state on
// etcd, a key-value store. When choosing this state management strategy, the
// developer is adding etcd as a dependency for the compiled system. The programmer
// is responsible for starting the etcd cluster and updating the "endpoints" list
// to include the addresses of the etcd servers.
public class EtcdStateStrategy implements StateStrategy {
	private static final String GLOBAL_STATE_OBJECT = "globalState";

	private PGoNetOptions.StateOptions stateOptions;

	public EtcdStateStrategy(PGoNetOptions.StateOptions stateOptions) throws PGoOptionException {
		validate(stateOptions);
		this.stateOptions = stateOptions;
	}

	@Override
	public void generateConfig(GoProgram go) {
		Vector<Statement> topLevelMain = go.getMain().getBody();

		topLevelMain.add(new FunctionCall("datatypes.GobInit", new Vector<>()));

		SliceConstructor endpoints = Builder.sliceLiteral(
				PGoType.inferFromGoTypeName("string"),
				stateOptions.endpoints
						.stream()
						.map(e -> Builder.stringLiteral("https://" + e))
						.collect(Collectors.toList()));

		SliceConstructor peers = Builder.sliceLiteral(
				PGoType.inferFromGoTypeName("string"),
				stateOptions.peers
						.stream()
						.map(Builder::stringLiteral)
						.collect(Collectors.toList()));

		VariableDeclaration errDecl = new VariableDeclaration(
				"err",
				PGoType.inferFromGoTypeName("error"), null, false, false, false);
		topLevelMain.add(errDecl);

		Assignment stateObj = new Assignment(
				new Vector<>(Arrays.asList(GLOBAL_STATE_OBJECT, "err")),
				new FunctionCall("distsys.NewEtcdState",
						new Vector<>(Arrays.asList(
								endpoints,
								Builder.intLiteral(stateOptions.timeout),
								peers,
								new Token("ipAddr"),
								Builder.stringLiteral(stateOptions.peers.get(0)),
								Builder.mapLiteral(
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
												}).collect(Collectors.toList()))
								))),
				false);
		topLevelMain.add(stateObj);

		go.getImports().addImport("os");
		Vector<Statement> ifBody = new Vector<>(Arrays.asList(
				new Comment("handle error - could not connect to etcd", false),
				new FunctionCall("os.Exit", new Vector<>(Collections.singletonList(new IntLiteral(1))))));

		pgo.model.golang.If errIf = new pgo.model.golang.If(new Token("err != nil"), ifBody, new Vector<>());
		topLevelMain.add(errIf);
	}

	@Override
	public void generateGlobalVariables(GoProgram go) {
		VariableDeclaration stateDecl = new VariableDeclaration(GLOBAL_STATE_OBJECT,
				new PGoMiscellaneousType.EtcdState(), null, false, false, false);

		go.addGlobal(stateDecl);
	}

	@Override
	public void lock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		stmts.add(new FunctionCall(
				"Lock",
				new Vector<>(Arrays.asList(new Token("selfStr"), new StringLiteral(Integer.toString(lockGroup)))),
				new Token(GLOBAL_STATE_OBJECT)));
		fetchDataForCurrentLockGroup(stmts, vars);
	}

	@Override
	public void unlock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		pushDataForCurrentLockGroup(stmts, vars);
		stmts.add(new FunctionCall(
				"Unlock",
				new Vector<>(Arrays.asList(new Token("selfStr"), new StringLiteral(Integer.toString(lockGroup)))),
				new Token(GLOBAL_STATE_OBJECT)));
	}

	@Override
	public String getGlobalStateVariableName() {
		return GLOBAL_STATE_OBJECT;
	}

	@Override
	public void setVar(PGoVariable var, Expression rhs, Vector<Expression> exps) {
		// assigning to a global, remote variable (managed by etcd)
		Vector<Expression> params = new Vector<>(Arrays.asList(new StringLiteral(var.getName()), rhs));
		exps.add(new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT)));
	}

	@Override
	public String getVar(PGoVariable var) {
		// TODO this is bad for performance
		return String.format("*%s.Get(\"%s\", &%s).(*%s)",
				GLOBAL_STATE_OBJECT, var.getName(), var.getName(), var.getType().toGo());
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
			Vector<Expression> params = new Vector<>(Arrays.asList(
					new StringLiteral(var.getName()),
					new Token(var.getName())));
			stmts.add(new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT)));
		});
	}

	private void validate(PGoNetOptions.StateOptions options) throws PGoOptionException {
	    if (options.endpoints.isEmpty()) {
	        throw new PGoOptionException("At least one etcd endpoint needs to be declared");
		}
	}
}
