package pgo.model.distsys;

import pgo.PGoNetOptions;
import pgo.model.golang.*;
import pgo.model.intermediate.*;

import java.util.Vector;
import java.util.stream.Stream;

public class CentralizedEtcdStateStrategy implements StateStrategy {
	public static final String GLOBAL_STATE_OBJECT = "globalState";

	private PGoNetOptions.StateOptions stateOptions;

	public CentralizedEtcdStateStrategy(PGoNetOptions.StateOptions stateOptions) {
		this.stateOptions = stateOptions;
	}

	@Override
	public void generateConfig(GoProgram go) {
		Vector<Statement> topLevelMain = go.getMain().getBody();
		String configObj = "cfg";

		Assignment cfgDecl = new Assignment(
				new Vector<String>() {
					{
						add(configObj);
					}
				},
				new Expression() {
					@Override
					public Vector<String> toGo() {
						StructDefinition sdef = new StructDefinition("distsys.Config", true);
						sdef.addField("Endpoints", new Expression() {
							@Override
							public Vector<String> toGo() {
								Vector<String> endpoints = new Vector<>();
								for (String h : stateOptions.endpoints) {
									endpoints.add(String.format("\"http://%s\"", h));
								}

								return new Token(String.format("%s{%s}",
										new PGoCollectionType.PGoSlice("string").toGo(),
										String.join(", ", endpoints))).toGo();
							}
						});

						sdef.addField("Timeout", new Expression() {
							@Override
							public Vector<String> toGo() {
								int timeout = stateOptions.timeout;
								return new Token(String.format("%d", timeout)).toGo();
							}
						});

						return sdef.toGo();
					}
				},
				true
		);
		topLevelMain.add(cfgDecl);

		VariableDeclaration errDecl = new VariableDeclaration(
				"err", PGoType.inferFromGoTypeName("error"), null, false, false, false
		);
		topLevelMain.add(errDecl);

		Vector<Expression> params = new Vector<>();
		params.add(new Expression() {
			@Override
			public Vector<String> toGo() {
				return new Token(configObj).toGo();
			}
		});

		Assignment stateObj = new Assignment(
				new Vector<String>() {
					{
						add(GLOBAL_STATE_OBJECT);
						add("err");
					}
				},
				new FunctionCall("distsys.InitGlobals", params),
				false
		);
		topLevelMain.add(stateObj);

		go.getImports().addImport("os");
		Vector<Expression> exitParams = new Vector<Expression>() {
			{
				add(new Expression() {
					@Override
					public Vector<String> toGo() {
						return new Token("1").toGo();
					}
				});
			}
		};
		Vector<Statement> ifBody = new Vector<Statement>() {
			{
				add(new Comment("handle error - could not connect to etcd", false));
				add(new FunctionCall("os.Exit", exitParams));
			}
		};

		pgo.model.golang.If errIf = new pgo.model.golang.If(new Token("err != nil"), ifBody, new Vector<>());
		topLevelMain.add(errIf);
	}

	@Override
	public void generateGlobalVariables(GoProgram go) {
		VariableDeclaration stateDecl = new VariableDeclaration(GLOBAL_STATE_OBJECT,
				new PGoMiscellaneousType.PGoNetCentralizedState(),
				null, false, false, false);

		go.addGlobal(stateDecl);
	}

	@Override
	public void initializeGlobalVariables(GoProgram go) {
		Vector<Statement> topLevelMain = go.getMain().getBody();
		boolean initLockInserted = false;
		String initLockGroup = "init-lock";
		String pidVarName = "lockId";
		Vector<Expression> strconvParams = new Vector<Expression>() {
			{
				add(new Token(pidVarName));
			}
		};

		for (VariableDeclaration gVar : go.getGlobals()) {
			if (!gVar.isRemote()) {
				continue;
			}

			go.getImports().addImport("strconv");
			if (!initLockInserted) {
				// A lock must be acquired in order to make sure only one process
				// initializes global variables with their default values.
				//
				// Since processes have no identifiers at this point (before parsing
				// arguments passed on the command line), we generate a random identifier
				// and use it when trying to get the lock. However, there is still a
				// slight chance of very bad luck where two processes happen to get
				// the same random ID and race to get the lock.
				int maxProcesses = 10000;

				Vector<Expression> randParams = new Vector<Expression>() {
					{
						add(new Token(Integer.toString(maxProcesses)));
					}
				};

				Assignment pidDecl = new Assignment(
						new Vector<String>() {
							{
								add(pidVarName);
							}
						},
						new FunctionCall("rand.Intn", randParams),
						true
				);
				FunctionCall lock = new FunctionCall("Lock", new Vector<Expression>() {
					{
						add(new FunctionCall("strconv.Itoa", strconvParams));
						add(new Token("\"" + initLockGroup + "\""));
					}
				}, new Token(GLOBAL_STATE_OBJECT));

				topLevelMain.add(pidDecl);
				topLevelMain.add(lock);
				initLockInserted = true;
			}

			topLevelMain.add(initializeGlobalVariable(gVar));
		}

		if (initLockInserted) {
			FunctionCall lock = new FunctionCall("Unlock", new Vector<Expression>() {
				{
					add(new FunctionCall("strconv.Itoa", strconvParams));
					add(new Token("\"" + initLockGroup + "\""));
				}
			}, new Token(GLOBAL_STATE_OBJECT));

			topLevelMain.add(lock);
		}
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
		stmts.add(new FunctionCall("Unlock", new Vector<Expression>() {
			{
				add(new Token("selfStr"));
				add(new Token("\"" + Integer.toString(lockGroup) + "\""));
			}
		}, new Token(GLOBAL_STATE_OBJECT)));
	}

	@Override
	public void setVar(PGoVariable var, Expression rhs, Vector<Expression> exps) {
		// assigning to a global, remote variable (managed by etcd)
		Vector<Expression> params = new Vector<Expression>() {
			{
				add(new Token("\"" + var.getName() + "\""));
			}
		};
		params.add(rhs);

		exps.add(new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT)));
	}

	@Override
	public String getVar(PGoVariable var) {
		String fn = "";
		if (var.getType() instanceof PGoPrimitiveType.PGoInt) {
			fn = "GetInt";
		}
		else if (var.getType() instanceof PGoPrimitiveType.PGoString) {
			fn = "GetString";
		}
		else if (var.getType() instanceof PGoCollectionType.PGoSlice) {
			switch (var.getType().toString()) {
				case "[]int":
					fn = "GetIntCollection";
					break;
				case "[]string":
					fn = "GetStringCollection";
					break;
				default:
					assert(false);
			}

		}
		else {
			// should not be reachable - variable type is not supported
			assert(false);
		}

		return String.format("%s.%s(\"%s\")", GLOBAL_STATE_OBJECT, fn, var.getName());
	}

	private void fetchDataForCurrentLockGroup(Vector<Statement> stmts, Stream<PGoVariable> vars) {
		StateStrategy stateStrategy = this;
		vars.forEach(var ->
				stmts.add(new Assignment(
						new Vector<String>(){
							{
								add(var.getName());
							}
						},
						new Expression() {
							@Override
							public Vector<String> toGo() {
								return new VariableReference(var.getName(), var, false, stateStrategy).toGo();
							}
						},
						false)));
	}

	private void pushDataForCurrentLockGroup(Vector<Statement> stmts, Stream<PGoVariable> vars) {
		vars.forEach(var -> {
			Vector<Expression> params = new Vector<>();
			params.add(new Expression() {
				@Override
				public Vector<String> toGo() {
					Vector<String> list = new Vector<>();
					list.add("\"" + var.getName() + "\"");
					return list;
				}
			});
			params.add(new Expression() {
				@Override
				public Vector<String> toGo() {
					return new Vector<String>(){
						{
							add(var.getName());
						}
					};
				}
			});
			stmts.add(new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT)));
		});
	}

	// given a remote, global variable declaration, this generates code to initialize
	// it with a proper value. Since multiple processes might be running at the same
	// time, initialization must be made only once. This is achieved by making use
	// of the locking functionality available in the `pgo/distsys' package.
	private Statement initializeGlobalVariable(VariableDeclaration decl) {
		Vector<Expression> params = new Vector<Expression>() {
			{
				add(new Token("\"" + decl.getName() + "\""));
				add(decl.getDefaultValue());
			}
		};
		FunctionCall setVar = new FunctionCall("Set", params, new Token(GLOBAL_STATE_OBJECT));
		Vector<Statement> ifBody = new Vector<Statement>() {
			{
				add(setVar);
			}
		};

		Vector<Expression> existsParams = new Vector<Expression>() {
			{
				add(new Token("\"" + decl.getName() + "\""));
			}
		};
		Expression cond = new FunctionCall("Exists", existsParams, new Token(GLOBAL_STATE_OBJECT));
		pgo.model.golang.If existenceIf = new pgo.model.golang.If(cond, ifBody, new Vector<>());
		existenceIf.negate();

		return existenceIf;
	}
}
