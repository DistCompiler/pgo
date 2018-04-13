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
import pgo.model.golang.SliceConstructor;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;
import pgo.model.golang.VariableDeclaration;
import pgo.model.intermediate.PGoMiscellaneousType;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;

public class DistributedObjectStateStrategy implements StateStrategy {

	private StateOptions stateOptions;

	public DistributedObjectStateStrategy(PGoNetOptions.StateOptions stateOptions) {
		this.stateOptions = stateOptions;
	}

	@Override
	public void generateConfig(GoProgram go) {
		// make sure doslib is available
		go.getImports().addImport("doslib");
		
		Vector<Statement> topLevelMain = go.getMain().getBody();
		topLevelMain.add(new Assignment(
				new Vector<>(Collections.singletonList("endpoints")),
				Builder.sliceLiteral(
						PGoType.inferFromGoTypeName("string"),
						stateOptions.endpoints
						.stream()
						.map(e -> Builder.stringLiteral(e))
						.collect(Collectors.toList())),
				true));
		
		SliceConstructor endpoints = Builder.sliceLiteral(
				PGoType.inferFromGoTypeName("string"),
				stateOptions.endpoints.stream()
				.map(s -> Builder.stringLiteral(s))
				.collect(Collectors.toList()));
		
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
		
		MapConstructor variableAllocations = Builder.mapLiteral(
				PGoType.inferFromGoTypeName("string"),
				PGoType.inferFromGoTypeName("int"),
				go.getGlobals()
				.stream()
				.filter(VariableDeclaration::isRemote)
				.map(g -> new Object[] {
						Builder.stringLiteral(g.getName()),
						Builder.intLiteral(0),
				})
				.collect(Collectors.toList()));
		
		topLevelMain.add(new If(new Token("endpoints[0] == ipAddr"),
				Builder.stmts(
						new Assignment(
								new Vector<>(Arrays.asList("doslibInstance, err")),
								new FunctionCall("doslib.MountLocalCache",
										new Vector<>(Arrays.asList(
												new Token("ipAddr"),
												new Token("ipAddr"),
												endpoints,
												variableAllocations,
												globalValues))),
								false)
						),
				Builder.stmts(
						new Assignment(
								new Vector<>(Arrays.asList("doslibInstance", "err")),
								new FunctionCall("doslib.MountLocalCache",
										new Vector<>(Arrays.asList(
												new Token("ipAddr"),
												new Token("ipAddr"),
												endpoints,
												variableAllocations,
												Builder.mapLiteral(
														PGoType.inferFromGoTypeName("string"),
														PGoType.inferFromGoTypeName("interface{}")
												)))),
										false)
						)
				));
		
		topLevelMain.add(new If(new Token("err != nil"),
				Builder.stmts(
						new FunctionCall("panic",
								new Vector<>(Arrays.asList(new Token("err"))))
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
						"doslibInstance",
						new PGoMiscellaneousType.DosLib(),
						null, false, false, false));
		go.addGlobal(
				new VariableDeclaration(
						"doslibLock",
						new PGoMiscellaneousType.DosLibReleaseSet(),
						null, false, false, false));
		go.addGlobal(
				new VariableDeclaration(
						"doslibValues",
						new PGoMiscellaneousType.DosLibValueMap(),
						null, false, false, false));

	}

	@Override
	public void initializeGlobalState(GoProgram go) {
		// pass, done in config right now
	}

	@Override
	public void lock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		List<PGoVariable> vList = vars.collect(Collectors.toList());
		
		List<Expression> varNamesStr = vList
				.stream()
				.map(v -> Builder.stringLiteral(v.getName()))
				.collect(Collectors.toList());
		
		stmts.add(new Token("_ = selfStr // bad warnings bad"));
		
		stmts.add(
				new Assignment(new Vector<String>(Arrays.asList("doslibLock", "doslibValues", "err")),
				new FunctionCall(
						"doslibInstance.Acquire",
						new Vector<>(Arrays.asList(
								Builder.structLiteral(
										new PGoMiscellaneousType.DosLibAcquireSet(),
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
								)
								))),
				false));
		
		// pull all values out of the map and into globals
		for(PGoVariable v : vList) {
			stmts.add(
					new Assignment(
							new Vector<>(Arrays.asList(v.getName())),
							new Token(
									"doslibValues[" + String.join(
											"",
											Builder.stringLiteral(v.getName()).toGo())
									+ "].(" + v.getType().toGo() + ")"),
							false));
		}

	}

	@Override
	public void unlock(int lockGroup, Vector<Statement> stmts, Stream<PGoVariable> vars) {
		List<String> varNames = vars.map(v -> v.getName()).collect(Collectors.toList());
		
		Vector<Expression> releaseNames = new Vector<>();
		releaseNames.add(new Token("doslibLock"));
		releaseNames.addAll(varNames
				.stream()
				.map(name -> new Token(name))
				.collect(Collectors.toList()));
		
		stmts.add(
				new Assignment(
						new Vector<>(Arrays.asList("err")),
						new FunctionCall(
								"doslibInstance.Release",
								releaseNames),
						false));
		
		stmts.add(new If(new Token("err != nil"),
				Builder.stmts(
						new FunctionCall("panic", new Vector<>(Arrays.asList(new Token("err"))))
						),
				Builder.stmts()));
	}

	@Override
	public void setVar(PGoVariable var, Expression rhs, Vector<Expression> exps) {
		// TODO: fix this mess, this is a terrible hack / abuse of the AST
		// since for some reason you can only use expressions to set variables, not statements?
		exps.add(
				new Token(
						String.join(
								"",
								new Assignment(
									new Vector<>(Arrays.asList(var.getName())),
									rhs,
									false).toGo())));
	}

	@Override
	public String getVar(PGoVariable var) {
		return var.getName();
	}

}
