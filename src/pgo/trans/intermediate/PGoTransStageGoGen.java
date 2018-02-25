package pgo.trans.intermediate;

import java.util.*;
import java.util.logging.Logger;

import pcal.AST;
import pcal.AST.*;
import pcal.AST.If;
import pcal.AST.Return;
import pcal.TLAExpr;
import pgo.model.golang.*;
import pgo.model.intermediate.*;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoMiscellaneousType.PGoWaitGroup;
import pgo.model.intermediate.PGoMiscellaneousType.PGoNetCentralizedState;
import pgo.model.intermediate.PGoPrimitiveType.PGoBool;
import pgo.model.intermediate.PGoPrimitiveType.PGoDecimal;
import pgo.model.intermediate.PGoPrimitiveType.PGoInt;
import pgo.model.intermediate.PGoPrimitiveType.PGoNatural;
import pgo.model.intermediate.PGoPrimitiveType.PGoString;
import pgo.model.parser.AnnotatedVariable.ArgAnnotatedVariable;
import pgo.model.tla.PGoTLA;
import pgo.model.tla.PGoTLAArray;
import pgo.model.tla.PGoTLADefinition;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.TLAExprToGo;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

import static pgo.PGoNetOptions.StateOptions.STATE_CENTRALIZED_ETCD;

/**
 * The last stage of the translation. Takes given intermediate data and converts
 * it to a Go AST, properly
 *
 */
public class PGoTransStageGoGen {
	// the ast
	private GoProgram go;

	// the main block pointer
	private Vector<Statement> main;

	// the intermediate data, which we use to generate the Go AST
	// when translating, this may be temporarily replaced by a PGoTempData which
	// stores some local variables
	PGoTransIntermediateData data;

	public PGoTransStageGoGen(PGoTransStageAtomicity s1) throws PGoTransException {
		this.data = s1.data;

		go = new GoProgram("main");

		main = go.getMain().getBody();

		generateArgParsing();
		generateDistributedStateConfig();
		generateGlobalVariables();
		generateFunctions();
		generateMain();
	}

	public GoProgram getGo() {
		return go;
	}

	private void generateMain() throws PGoTransException {
		Logger.getGlobal().info("Generating Main Function");

		if (this.data.isMultiProcess && this.data.netOpts.isEnabled()) {
			// Switch on `processName` to know which process/function to invoke and passing `processArg`
			// as the argument to the process/function. They are instantiated in `addPositionalArgToMain`.

			Vector<Expression> exp, args;
			Vector<Statement> code;
			Switch switchProcess = new Switch(new Token("processName"));
			exp = new Vector<>();
			exp.add(new Token("\"Unknown process \""));
			exp.add(new Token(" + "));
			exp.add(new Token("processName"));
			args = new Vector<>();
			args.add(new SimpleExpression(exp));
			code = new Vector<>();
			code.add(new FunctionCall("panic", args));
			switchProcess.addDefaultCase(code);
			for (Map.Entry<String, PGoFunction> entry : data.funcs.entrySet()) {
				String processName = entry.getKey();
				PGoFunction process = entry.getValue();

				if (process.getType() != PGoFunction.FunctionType.Process) {
					continue;
				}

				exp = new Vector<>();
				args = new Vector<>();
				code = new Vector<>();

				args.add(new Token("processArg.(" + process.getParams().get(0).getType().toTypeName() + ")"));
				exp.add(new FunctionCall(processName, args));
				code.add(new SimpleExpression(exp));
				switchProcess.addCase(new Token("\"" + processName + "\""), code);
			}
			go.getMain().getBody().add(switchProcess);
		} else if (this.data.isMultiProcess) {
			main.addAll(convertGoRoutinesToGo(this.data.goroutines.values()));
		} else {
			Vector block = this.data.mainBlock;
			Vector<Statement> stmts = convertStatementToGo(block);
			main.addAll(stmts);
		}

		// remote state requires initialization, which requires a random process
		// identifier to be generated when acquiring the lock
		if (hasRemoteState()) {
			go.getImports().addImport("math/rand");
		}

		// if we use math/rand we also need to set a seed
		if (go.getImports().containsPackage("math/rand")) {
			go.getImports().addImport("time");
			FunctionCall seed = new FunctionCall("rand.Seed", new Vector<Expression>() {
				{
					add(new FunctionCall("UnixNano", new Vector<>(), new FunctionCall("time.Now", new Vector<>())));
				}
			});
			go.getMain().getBody().add(0, seed);
		}
	}

	private void generateArgParsing() throws PGoTransException {
		int argN = 0;
		boolean hasArg = false;

		Vector<Statement> positionalArgs = new Vector<>();
		Vector<String> positionalArgNames = new Vector<>();
		boolean hasFlagArgs = false;

		if (data.netOpts.isEnabled()) {
			go.getImports().addImport("flag");
			go.getImports().addImport("pgo/datatypes");
			hasArg = true;
			PGoVariable var = PGoVariable.processIdArg();
			var.setType(PGoPrimitiveType.PROCESS_ID);
			positionalArgNames.add("process(argument)");
			addPositionalArgToMain(argN++, positionalArgs, var);
		}

		for (PGoVariable pv : this.data.globals.values()) {
			// Add flags as necessary
			if (pv.getArgInfo() != null) {
				Logger.getGlobal().info("Generating command line argument code for variable \""
						+ pv.getName() + "\"");
				go.getImports().addImport("flag");
				hasArg = true;
				if (pv.getArgInfo().isPositionalArg()) {
					addPositionalArgToMain(argN++, positionalArgs, pv);
					positionalArgNames.add(pv.getName());
				} else {
					hasFlagArgs = true;
					addFlagArgToMain(pv);
				}

			}
		}

		if (hasArg) {
			final int fArgN = argN;
			final boolean fHasFlagArgs = hasFlagArgs;
			go.getImports().addImport("os");
			go.getImports().addImport("fmt");
			main.add(new FunctionCall("flag.Parse", new Vector<>()));

			// check arguments
			Expression cond = new SimpleExpression(new Vector<Expression>() {
				{
					add(new FunctionCall("flag.NArg", new Vector<>()));
					add(new Token("<"));
					add(new Token(Integer.toString(fArgN)));
				}
			});
			Vector<Statement> thenPart = new Vector<Statement>() {
				{
					add(new FunctionCall("fmt.Fprintf", new Vector<Expression>() {
						{
							add(new Token("os.Stderr"));
							add(new Token((fHasFlagArgs ? "\"Usage: %s [options...] " : "\"Usage: %s ") +
									String.join(" ", positionalArgNames) +
									(fHasFlagArgs ? "\\nOptions:" : "") +
									"\\n\""
							));
							add(new Token("os.Args[0]"));
						}
					}));
					add(new FunctionCall("os.Exit", new Vector<Expression>() {
						{
							add(new Token("1"));
						}
					}));
				}
			};
			if (fHasFlagArgs) {
				thenPart.add(new FunctionCall("flag.PrintDefaults", new Vector<>()));
			}
			main.add(new pgo.model.golang.If(cond, thenPart, new Vector<>()));

			main.addAll(positionalArgs);
		}
	}


	/**
	 * Convert the TLA AST to the equivalent Go AST while adding the required
	 * imports.
	 *
	 * @throws PGoTransException
	 */
	private Expression TLAToGo(PGoTLA tla) throws PGoTransException {
		if (data instanceof PGoTempData) {
			return new TLAExprToGo(tla, go.getImports(), new PGoTempData((PGoTempData) data))
					.toExpression();
		}
		return new TLAExprToGo(tla, go.getImports(), new PGoTempData(data)).toExpression();
	}

	// whether or not we are compiling a program which has remote global state.
	// Specifically, this is true if:
	//
	// * we are compiling a distributed algorithm (networking option enabled)
	// * we have at least one global variable
	private boolean hasRemoteState() {
		return data.netOpts.isEnabled() && data.globals.size() > 0;
	}

	/**
	 * Converts a given code black into Go code. Given code block should not
	 * have function
	 * definitions and such in pluscal TODO finish visit methods (issue #4)
	 *
	 * @param stmts
	 * @return
	 * @throws PGoTransException
	 */
	private Vector<Statement> convertStatementToGo(Vector<AST> stmts) throws PGoTransException {
		go.addUsedLabels(PcalASTUtil.collectUsedLabels(stmts));
		return new PcalASTUtil.Walker<Vector<Statement>>() {
			// the current label that we are in
			String curLabel = null;
			// the current lock group we are in (-1 if no lock)
			int curLockGroup = -1;

			private void addVariablesToCache() {
				for (PGoVariable var : data.globals.values()) {
					if (var.getLockGroup() != curLockGroup) {
						continue;
					}
					data.cachedVarSet.add(var);
				}
			}

			private void removeVariablesFromCache() {
				for (PGoVariable var : data.globals.values()) {
					if (var.getLockGroup() != curLockGroup) {
						continue;
					}
					data.cachedVarSet.remove(var);
				}
			}

			// DANGER: set lock group without generating lock code
			// This is used in cases where we're still holding the lock in one code path but releasing it in another,
			// e.g. in an await statement.
			private void setLockGroup() throws PGoTransException {
				if (data.needsLock) {
					if (curLockGroup != -1) {
						throw new PGoTransException("Nested lock or await/when statement is not first in a labelled block");
					}
					int lockGroup = data.labToLockGroup.get(curLabel);
					if (lockGroup == -1) {
						return;
					}
					curLockGroup = lockGroup;
					addVariablesToCache();
				}
			}

			// Add a statement to lock, if we need thread safety
			private void lock() throws PGoTransException {
				setLockGroup();
				if (data.needsLock) {
					if (data.netOpts.isEnabled()) {
						data.netOpts.getStateStrategy().lock(curLockGroup, result,
								data.globals.values().stream().filter(var -> var.getLockGroup() == curLockGroup));
					} else {
						result.add(new FunctionCall("Lock", new Vector<>(),
								new Token("PGoLock[" + Integer.toString(curLockGroup) + "]")));
					}
				}
			}

			private void unlock() {
				if (curLockGroup != -1 && data.needsLock) {
					if (data.netOpts.isEnabled()) {
						data.netOpts.getStateStrategy().unlock(curLockGroup, result,
								data.globals.values().stream().filter(var -> var.getLockGroup() == curLockGroup));
						removeVariablesFromCache();
					} else {
						result.add(new FunctionCall("Unlock", new Vector<>(),
								new Token("PGoLock[" + Integer.toString(curLockGroup) + "]")));
					}
					curLockGroup = -1;
				}
			}

			@Override
			protected void init() {
				result = new Vector<>();
			}

			@Override
			public Vector<Statement> getResult(Vector<AST> stmts) throws PGoTransException {
				// fill the result
				super.getResult(stmts);
				// add an unlock, if we need it
				unlock();
				return result;
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				// unlock if we're still locked from another label (e.g. if
				// this is a label inside the body of a while, the
				// LabeledStmts are nested)
				unlock();
				curLabel = ls.label;
				// only add the label if we use it in a goto
				if (go.isLabelUsed(ls.label)) {
					result.add(new Label(ls.label));
				}

				// if the first statement is a while or an await, we should lock on the
				// loop interior
				assert (!ls.stmts.isEmpty());
				if (!(ls.stmts.get(0) instanceof While || ls.stmts.get(0) instanceof When)) {
					lock();
				}

				super.visit(ls);
				// we don't need to unlock afterward, since this statement will
				// be followed by a label
			}

			@Override
			protected void visit(While w) throws PGoTransException {
				Expression cond = TLAToGo(data.findPGoTLA(w.test));

				Vector<Statement> loopBody = new Vector<>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = loopBody; // we send the loop body to be filled

				if (!w.unlabDo.isEmpty()) {
					lock();
					walk(w.unlabDo); // this is the body before the first label
				}
				walk(w.labDo);
				unlock();

				For loopAst = new For(cond, result);
				result = tempRes;
				result.add(loopAst);
			}

			@Override
			protected void visit(Assign as) throws PGoTransException {
				if (as.ass.size() > 1) {
					// pluscal semantics:
					// u = v || v = u is equivalent to setting new_u and new_v
					for (SingleAssign sa : (Vector<SingleAssign>) as.ass) {
						Vector<Expression> exps = new Vector<>();
						exps.add(new Token(sa.lhs.var + "_new"));
						// TODO parse sub for [2] etc
						exps.add(new Token(" := "));
						Expression rhs = TLAToGo(data.findPGoTLA(sa.rhs));

						exps.add(rhs);

						result.add(new SimpleExpression(exps));
					}

					for (SingleAssign sa : (Vector<SingleAssign>) as.ass) {
						Vector<Expression> exps = new Vector<>();
						if (!sa.lhs.sub.tokens.isEmpty()) {
							// the sub is [expr, expr...] (map/array access) or
							// .<name> for a record field

							PGoTLA ptla = data.findPGoTLA(sa.lhs.sub);
							// TODO handle record fields
							PGoTLAFunctionCall fc = (PGoTLAFunctionCall) ptla;
							// Check for type consistency.
							TLAToGo(fc);
							// We compile differently based on the variable's
							// type.
							PGoVariable assign = data.findPGoVariable(sa.lhs.var);
							if (assign.getType() instanceof PGoSlice) {
								// just var[expr]
								assert (fc.getParams().size() == 1);
								exps.add(new Token(sa.lhs.var));
								exps.add(new Token("["));
								exps.add(TLAToGo(fc.getParams().get(0)));
								exps.add(new Token("]"));
								exps.add(new Token(" = "));
								exps.add(new Token(sa.lhs.var + "_new"));
							} else if (assign.getType() instanceof PGoTuple) {
								// var = var.Set(index, assign)
								assert (fc.getParams().size() == 1);
								exps.add(new Token(sa.lhs.var));
								exps.add(new Token(" = "));
								Vector<Expression> params = new Vector<>();
								params.add(TLAToGo(fc.getParams().get(0)));
								params.add(new Token(sa.lhs.var + "_new"));
								exps.add(new FunctionCall("Set", params, new Token(sa.lhs.var)));
							} else if (assign.getType() instanceof PGoMap) {
								// var.Put(params, assign)
								Vector<Expression> params = new Vector<>();
								// if there is a single param, we can just put
								// it
								// otherwise, we make a tuple
								if (fc.getParams().size() == 1) {
									params.add(TLAToGo(fc.getParams().get(0)));
								} else {
									Vector<Expression> tupleElts = new Vector<>();
									for (PGoTLA tla : fc.getParams()) {
										tupleElts.add(TLAToGo(tla));
									}
									params.add(new FunctionCall("datatypes.NewTuple", tupleElts));
								}
								params.add(new Token(sa.lhs.var + "_new"));
								exps.add(new FunctionCall("Put", params, new Token(sa.lhs.var)));
							} else {
								assert false;
							}
						} else {
							// the lhs is a simple variable
							exps.add(new Token(sa.lhs.var));
							exps.add(new Token(" = "));
							exps.add(new Token(sa.lhs.var + "_new"));
						}
						result.add(new SimpleExpression(exps));
					}
				} else {
					// only one assign, just treat it like a single assignment
					// without temp variables
					walk(as.ass);
				}
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				Vector<Expression> exps = new Vector<>();
				Expression rhs = TLAToGo(data.findPGoTLA(sa.rhs));
				if (!sa.lhs.sub.tokens.isEmpty()) {
					// the sub is [expr, expr...] (map/array access) or
					// .<name> for a record field

					PGoTLA ptla = data.findPGoTLA(sa.lhs.sub);
					// TODO handle record fields
					PGoTLAFunctionCall fc = (PGoTLAFunctionCall) ptla;
					// Check for type consistency.
					TLAToGo(fc);
					// We compile differently based on the variable's type.
					PGoVariable assign = data.findPGoVariable(sa.lhs.var);
					if (assign.getType() instanceof PGoSlice) {
						// just var[expr]
						assert (fc.getParams().size() == 1);
						exps.add(new Token(sa.lhs.var));
						exps.add(new Token("["));
						exps.add(TLAToGo(fc.getParams().get(0)));
						exps.add(new Token("]"));
						exps.add(new Token(" = "));
						exps.add(rhs);
					} else if (assign.getType() instanceof PGoTuple) {
						// var = var.Set(index, assign)
						assert (fc.getParams().size() == 1);
						exps.add(new Token(sa.lhs.var));
						exps.add(new Token(" = "));
						Vector<Expression> params = new Vector<>();
						params.add(TLAToGo(fc.getParams().get(0)));
						params.add(rhs);
						exps.add(new FunctionCall("Set", params, new Token(sa.lhs.var)));
					} else if (assign.getType() instanceof PGoMap) {
						// var.Put(params, assign)
						Vector<Expression> params = new Vector<>();
						// if there is a single param, we can just put it
						// otherwise, we make a tuple
						if (fc.getParams().size() == 1) {
							params.add(TLAToGo(fc.getParams().get(0)));
						} else {
							Vector<Expression> tupleElts = new Vector<>();
							for (PGoTLA tla : fc.getParams()) {
								tupleElts.add(TLAToGo(tla));
							}
							params.add(new FunctionCall("datatypes.NewTuple", tupleElts));
						}
						params.add(rhs);
						exps.add(new FunctionCall("Put", params, new Token(sa.lhs.var)));
					} else {
						assert false;
					}
				} else {
					// the lhs is a simple variable
					PGoVariable var = data.findPGoVariable(sa.lhs.var);

					if (var.isRemote() && !data.cachedVarSet.contains(var)) {
						data.netOpts.getStateStrategy().setVar(var, rhs, exps);
					} else {
						// assigning to a regular, non-remote variable
						exps.add(new Token(sa.lhs.var));
						exps.add(new Token(" = "));
						exps.add(rhs);
					}
				}
				result.add(new SimpleExpression(exps));
			}

			@Override
			protected void visit(If ifast) throws PGoTransException {
				Expression cond = TLAToGo(data.findPGoTLA(ifast.test));

				Vector<Statement> thenS = new Vector<>(), elseS = new Vector<>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = thenS; // we send the loop body to be filled
				walk(ifast.Then);
				result = elseS;
				walk(ifast.Else);

				pgo.model.golang.If ifAst = new pgo.model.golang.If(cond, thenS, elseS);

				result = tempRes;
				result.add(ifAst);
			}

			@Override
			protected void visit(Either ei) {
				for (Vector v : (Vector<Vector>) ei.ors) {
					// either has vector of vectors
					// walk(v);
					// TODO handle either
				}
			}

			@Override
			protected void visit(With with) throws PGoTransException {
				// Select a random element of with.exp and perform with.Do on it
				// multiple vars in one with are nested by the PcalParser
				Vector<Statement> pre = new Vector<>();
				// we will add new typing data for local variables, but we
				// should keep them within the scope of this with
				PGoTransIntermediateData oldData = data;
				data = new PGoTempData(data);
				AST cur = with;
				// if the withs are nested, we don't want to keep nesting them,
				// so get them all at once
				while (cur instanceof With) {
					with = (With) cur;
					String varName = with.var;
					if (with.isEq) {
						// of the form with x = a
						PGoTLA varExpr = data.findPGoTLA(with.exp);
						TLAExprToGo trans = new TLAExprToGo(varExpr, go.getImports(),
								new PGoTempData((PGoTempData) data));

						VariableDeclaration v = new VariableDeclaration(varName, trans.getType(), trans.toExpression(),
								false, true, false);
						pre.add(v);
						((PGoTempData) data).getLocals().put(varName,
								PGoVariable.convert(varName, trans.getType()));
					} else {
						// x \in S
						// var x type = S.ToSlice()[rand.Intn(S.Size())].(type)
						PGoTLA setExpr = data.findPGoTLA(with.exp);
						TLAExprToGo trans = new TLAExprToGo(setExpr, go.getImports(),
								new PGoTempData(data));
						PGoType setType = trans.getType();
						assert (setType instanceof PGoSet);
						PGoType containedType = ((PGoSet) setType).getElementType();

						Vector<Expression> rhs = new Vector<>();
						rhs.add(new FunctionCall("ToSlice", new Vector<>(), trans.toExpression()));
						rhs.add(new Token("["));
						rhs.add(new FunctionCall("rand.Intn", new Vector<Expression>() {
							{
								add(new FunctionCall("Size", new Vector<>(), trans.toExpression()));
							}
						}));
						rhs.add(new Token("]"));

						VariableDeclaration v = new VariableDeclaration(varName, containedType,
								new TypeAssertion(new SimpleExpression(rhs), containedType), false, true, false);
						pre.add(v);
						go.getImports().addImport("math/rand");
						((PGoTempData) data).getLocals().put(varName,
								PGoVariable.convert(varName, containedType));
					}
					// if there are multiple statements, this is no longer a
					// nested with
					if (with.Do.size() > 1) {
						break;
					}
					cur = (AST) with.Do.get(0);
				}
				CodeBlock cb = new CodeBlock(pre);
				Vector<Statement> tempRes = result;
				// put the with body in the code block
				result = cb.getInside();
				walk(with.Do);
				tempRes.add(cb);
				result = tempRes;
				data = oldData;
			}

			/// An await statement
			///     await exp;
			/// is translated into the following
			///     for {
			///         lock
			///         if exp {
			///             break
			///         }
			///         unlock
			///         yield
			///     }
			/// where yield is a call to invoke the Go runtime scheduler.
			@Override
			protected void visit(When when) throws PGoTransException {
				// we're about to enter an infinite loop so unlock for safety
				unlock();
				Vector<Statement> body = new Vector<>();
				Vector<Statement> then = new Vector<Statement>() {
					{
						add(new Token("break"));
					}
				};
				Vector<Statement> oldResult = result;
				result = body;
				lock();
				body.add(new pgo.model.golang.If(TLAToGo(data.findPGoTLA(when.exp)), then, new Vector<>()));
				unlock();
				if (!data.netOpts.isEnabled()) {
					go.getImports().addImport("runtime");
					body.add(new FunctionCall("Gosched", new Vector<>(), new Token("runtime")));
				}
				result = oldResult;
				result.add(new For(body));
				// we're still holding the lock
				setLockGroup();
			}

			@Override
			protected void visit(PrintS ps) throws PGoTransException {
				PGoTLA argExp = data.findPGoTLA(ps.exp);
				Vector<Expression> args = new Vector<>();
				// if this is a tuple, we print each element individually
				if (argExp instanceof PGoTLAArray) {
					Vector<String> strfmt = new Vector<>();
					for (PGoTLA arg : ((PGoTLAArray) argExp).getContents()) {
						strfmt.add("%v");
						args.add(TLAToGo(arg));
					}
					args.add(0, new Token("\"" + String.join(" ", strfmt) + "\\n\""));
				} else {
					// fmt.Printf("%v\n", arg)
					args.add(0, new Token("\"%v\\n\""));
					args.add(TLAToGo(argExp));
				}

				go.getImports().addImport("fmt");
				FunctionCall fc = new FunctionCall("fmt.Printf", args);
				result.add(fc);
			}

			@Override
			protected void visit(Assert as) {
				// TODO actually do we even want this?
			}

			@Override
			protected void visit(Skip s) {
				Vector<String> cmt = new Vector<>();
				cmt.add("TODO skipped from pluscal");
				result.add(new Comment(cmt, false));
			}

			@Override
			protected void visit(LabelIf lif) throws PGoTransException {
				Expression cond = TLAToGo(data.findPGoTLA(lif.test));

				// we might change labels in the then block, but the else block
				// should start at the old label
				String oldLabel = curLabel;
				int oldLockGroup = curLockGroup;

				Vector<Statement> thenS = new Vector<>(), elseS = new Vector<>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = thenS; // we send the loop body to be filled
				walk(lif.unlabThen);
				walk(lif.labThen);
				unlock();

				curLabel = oldLabel;
				curLockGroup = oldLockGroup;
				result = elseS;
				walk(lif.unlabElse);
				walk(lif.labElse);
				unlock();

				pgo.model.golang.If ifAst = new pgo.model.golang.If(cond, thenS, elseS);

				result = tempRes;
				result.add(ifAst);
			}

			@Override
			protected void visit(LabelEither le) {
				// TODO
				// walk(le.clauses);
			}

			@Override
			protected void visit(Clause c) {
				// TODO handle with either
				// walk(c.unlabOr);
				// walk(c.labOr);
			}

			@Override
			protected void visit(Call c) throws PGoTransException {
				Vector<Expression> args = new Vector<>();
				for (TLAExpr t : (Vector<TLAExpr>) c.args) {
					PGoTLA tla = data.findPGoTLA(t);
					args.add(TLAToGo(tla));
				}
				unlock();
				FunctionCall fc = new FunctionCall(c.to, args);
				result.add(fc);
			}

			@Override
			protected void visit(Return r) {
				// TODO learn to get the return variable
				result.add(new pgo.model.golang.Return(null));
			}

			@Override
			protected void visit(CallReturn cr) throws PGoTransException {
				Vector<Expression> args = new Vector<>();
				for (TLAExpr t : (Vector<TLAExpr>) cr.args) {
					PGoTLA tla = data.findPGoTLA(t);
					args.add(TLAToGo(tla));
				}
				unlock();
				FunctionCall fc = new FunctionCall(cr.to, args);
				result.add(fc);
			}

			@Override
			protected void visit(Goto g) {
				// we are jumping to a label which will immediately lock, so
				// unlock before
				int oldLockGroup = curLockGroup;
				unlock();
				// control jumps to a different label at which point we are
				// unlocked, but the rest of the ast we are walking is still
				// locked
				curLockGroup = oldLockGroup;
				result.add(new GoTo(g.to));
				assert (go.isLabelUsed(g.to));
			}

			@Override
			protected void visit(MacroCall m) {
				// TODO
			}
		}.getResult(stmts);
	}

	/**
	 * Generate the go routines init blocks as statements
	 * 
	 * @param goroutines
	 * @throws PGoTransException
	 */
	private Vector<Statement> convertGoRoutinesToGo(Collection<PGoRoutineInit> goroutines) throws PGoTransException {
		Vector<Statement> ret = new Vector<>();
		for (PGoRoutineInit goroutine : goroutines) {
			if (goroutine.getIsSimpleInit()) {
				// The waitgroup was added in generateGlobalVariables()
				// PGoWait.Add(1)
				// go foo(id)
				ret.add(new FunctionCall("Add", new Vector<Expression>() {
					{
						add(new Token("1"));
					}
				}, new Token("PGoWait")));

				Vector<Expression> se = new Vector<>();
				se.add(new Token("go "));
				PGoTLA id = data.findPGoTLA(goroutine.getInitTLA());
				se.add(new FunctionCall(goroutine.getName(), new Vector<Expression>() {
					{
						add(new TLAExprToGo(id, go.getImports(), new PGoTempData(data))
								.toExpression());
					}
				}));
				ret.add(new SimpleExpression(se));
			} else {
				// for procId := range set.Iter() {
				// PGoWait.Add(1)
				// go foo(procId.(type))
				// }

				PGoTLA setTLA = data.findPGoTLA(goroutine.getInitTLA());
				TLAExprToGo trans = new TLAExprToGo(setTLA, go.getImports(), new PGoTempData(data));
				PGoType setType = trans.getType();
				assert (setType instanceof PGoSet);
				PGoType eltType = ((PGoSet) setType).getElementType();

				Vector<Expression> range = new Vector<>();
				range.add(new Token("procId"));
				range.add(new Token(" := "));
				range.add(new Token("range "));
				range.add(new FunctionCall("Iter", new Vector<>(), trans.toExpression()));

				Vector<Statement> forBody = new Vector<>();
				forBody.add(new FunctionCall("Add", new Vector<Expression>() {
					{
						add(new Token("1"));
					}
				}, new Token("PGoWait")));

				TypeAssertion param = new TypeAssertion(new Token("procId"), eltType);

				Vector<Expression> se = new Vector<>();
				se.add(new Token("go "));
				se.add(new FunctionCall(goroutine.getName(), new Vector<Expression>() {
					{
						add(param);
					}
				}));
				forBody.add(new SimpleExpression(se));

				For loop = new For(new SimpleExpression(range), forBody);
				ret.add(loop);
			}
		}
		// close(PGoStart)
		// PGoWait.Wait()
		ret.add(new FunctionCall("close", new Vector<Expression>() {
			{
				add(new Token("PGoStart"));
			}
		}));
		ret.add(new FunctionCall("Wait", new Vector<>(), new Token("PGoWait")));
		return ret;
	}

	/**
	 * Create declarations for all functions
	 * 
	 * @throws PGoTransException
	 */
	private void generateFunctions() throws PGoTransException {
		for (PGoFunction pf : this.data.funcs.values()) {
			// Add typing data for params and locals.
			PGoTransIntermediateData oldData = data;
			PGoTempData localData = new PGoTempData(oldData);

			Vector<ParameterDeclaration> params = new Vector<>();
			for (PGoVariable param : pf.getParams()) {
				params.add(new ParameterDeclaration(param.getName(), param.getType()));
				localData.getLocals().put(param.getName(), param);
			}
			Vector<VariableDeclaration> locals = new Vector<>();
			for (PGoVariable local : pf.getVariables()) {
				PGoTLA initTLA = data.findPGoTLA(local.getPcalInitBlock());
				// if initTLA is empty, the local init is defaultInitValue
				// (no initialization code)
				if (initTLA == null) {
					locals.add(new VariableDeclaration(local, null));
				} else {
					Expression init = new TLAExprToGo(initTLA, go.getImports(), localData, local).toExpression();
					locals.add(new VariableDeclaration(local, init));
				}

				localData.getLocals().put(local.getName(), local);
			}

			Vector<Statement> body = new Vector<>();
			// if this is a goroutine, we need to use waitgroup and flag channel
			// in the function body
			if (data.goroutines.containsKey(pf.getName())) {
				// defer PGoWait.Done()
				Vector<Expression> se = new Vector<>();
				se.add(new Token("defer "));
				se.add(new FunctionCall("Done", new Vector<>(), new Token("PGoWait")));
				body.add(new SimpleExpression(se));
				// to synchronize start of all processes, we pull from a dummy
				// channel which is closed when we want to start the goroutines

				// <-PGoStart
				se = new Vector<>();
				se.add(new Token("<-"));
				se.add(new Token("PGoStart"));
				body.add(new SimpleExpression(se));
			}
			if (pf.getType() == PGoFunction.FunctionType.Process) {
				if (pf.getParams().get(0).getType().equals(PGoPrimitiveType.STRING)) {
					body.add(new SimpleExpression(new Vector<Expression>() {
						{
							add(new Token("selfStr"));
							add(new Token(" := "));
							add(new Token("\"" + pf.getName() + "(\""));
							add(new Token(" + "));
							add(new Token("self"));
							add(new Token(" + "));
							add(new Token("\")\""));
						}
					}));
				} else if (pf.getParams().get(0).getType().equals(PGoPrimitiveType.INT)) {
					go.getImports().addImport("strconv");
					body.add(new SimpleExpression(new Vector<Expression>() {
						{
							add(new Token("selfStr"));
							add(new Token(" := "));
							add(new Token("\"" + pf.getName() + "(\""));
							add(new Token(" + "));
							add(new FunctionCall("strconv.Itoa", new Vector<Expression>() {
								{
									add(new Token("self"));
								}
							}));
							add(new Token(" + "));
							add(new Token("\")\""));
						}
					}));
				} else {
					throw new PGoTransException("Unsupported argument type " + pf.getParams().get(0).getType() +
							" for process " + pf.getName(), pf.getLine());
				}
			}

			data = localData;
			body.addAll(convertStatementToGo(pf.getBody()));
			data = oldData;

			Function f = new Function(pf.getName(), pf.getReturnType(), params, locals, body);
			go.addFunction(f);
		}

		for (PGoTLADefinition tlaDef : this.data.defns.values()) {
			Vector<ParameterDeclaration> params = new Vector<>();
			for (PGoVariable param : tlaDef.getParams()) {
				params.add(new ParameterDeclaration(param.getName(), param.getType()));
			}
			// tla defn's don't have locals
			Vector<Statement> body = new Vector<>();
			// add typing information for parameters
			PGoTempData temp = new PGoTempData(data);
			for (PGoVariable param : tlaDef.getParams()) {
				temp.getLocals().put(param.getName(), param);
			}

			TLAExprToGo trans = new TLAExprToGo(tlaDef.getExpr(), go.getImports(), temp, tlaDef.getType());
			body.add(new pgo.model.golang.Return(trans.toExpression()));

			go.addFunction(new Function(tlaDef.getName(), trans.getType(), params, new Vector<>(), body));
		}
	}

	/**
	 * Generate the code for global variables
	 * 
	 * @throws PGoTransException
	 */
	private void generateGlobalVariables() throws PGoTransException {
		// if the algorithm needs locking, we should create sync.RWMutexes
		if (!data.netOpts.isEnabled() && data.needsLock) {
			// make([]sync.RWMutex, size)
			Vector<Expression> params = new Vector<>();
			params.add(new Token(new PGoSlice("sync.RWMutex").toGo()));
			params.add(new Token(((Integer) data.numLockGroups).toString()));

			// if the algorithm needs lock, then networking must not be enabled
			go.addGlobal(new VariableDeclaration("PGoLock", new PGoSlice("sync.RWMutex"),
					new FunctionCall("make", params), false, false, false));
			go.getImports().addImport("sync");
		}
		// Generate all variables from TLA definitions first.
		for (PGoVariable pv : this.data.globals.values()) {
			if (this.data.annots.getAnnotatedTLADefinition(pv.getName()) == null) {
				continue;
			}

			generateSimpleVariable(pv, false);
		}
		// we delay initialization once we hit a variable with \in, in case
		// other variable refer to it. We also want to reset the other values to
		// the initial value. Constants will still be generated at the time
		boolean delay = false;
		for (PGoVariable pv : this.data.globals.values()) {
			if (pv.getIsSimpleAssignInit()) {
				continue;
			}

			delay = true;

			// this is var \in collection

			Logger.getGlobal()
					.info("Generating go variable \"" + pv.getName() + "\" with loop");

			// being part of the rhs, the parsed result should just be
			// one coherent expression
			PGoTLA ptla = data.findPGoTLA(pv.getPcalInitBlock());
			Expression se = TLAToGo(ptla);

			go.addGlobal(new VariableDeclaration(pv, null));
			Vector<Expression> toks = new Vector<>();
			toks.add(new Token(pv.getName() + "_interface"));
			toks.add(new Token(" := "));
			toks.add(new Token("range "));
			toks.add(new FunctionCall("Iter", new Vector<>(), se));

			For loop = new For(new SimpleExpression(toks), new Vector<>());
			main.add(loop);
			// we need to cast the interface value to its actual type
			Vector<Expression> cast = new Vector<>();
			cast.add(new Token(pv.getName()));
			cast.add(new Token(" = "));
			cast.add(new TypeAssertion(new Token(pv.getName() + "_interface"), pv.getType()));
			loop.getThen().add(new SimpleExpression(cast));
			main = loop.getThen();
			// we set the rest of the main to go in here
		}

		for (PGoVariable pv : this.data.globals.values()) {
			if (!pv.getIsSimpleAssignInit()) {
				// already did var \in set
				continue;
			}
			if (this.data.annots.getAnnotatedTLADefinition(pv.getName()) != null) {
				// already generated TLA defns
				continue;
			}
			generateSimpleVariable(pv, delay);
		}

		// if the program contains goroutines, we need to add a waitgroup
		// (prevent early termination of main goroutine) and a dummy channel
		// (synchronize the start of the goroutines)
		if (!data.goroutines.isEmpty()) {
			go.getImports().addImport("sync");
			go.addGlobal(new VariableDeclaration("PGoWait", new PGoWaitGroup(), null, false, false, false));

			Expression init = new FunctionCall("make", new Vector<Expression>() {
				{
					add(new Token(PGoType.inferFromGoTypeName("chan[bool]").toGo()));
				}
			});
			VariableDeclaration chanDecl = new VariableDeclaration("PGoStart",
					PGoType.inferFromGoTypeName("chan[bool]"), init, false, false, false);
			go.addGlobal(chanDecl);
		}

		if (hasRemoteState()) {
			data.netOpts.getStateStrategy().generateGlobalVariables(go);
		}
	}

	private void generateSimpleVariable(PGoVariable pv, boolean delay) throws PGoTransException {
		Logger.getGlobal().info("Generating go variable \"" + pv.getName() + "\"");

		if (!pv.getGoVal().isEmpty()) {
			// If we have a specifieVector<E>ang value for the variable,
			// use it

			go.addGlobal(new VariableDeclaration(pv, new Token(pv.getGoVal())));
			return;
		} else if (pv.getArgInfo() != null) {
			go.addGlobal(new VariableDeclaration(pv, null));
			// generateMain will fill the main function
		} else {
			// being part of the rhs, the parsed result should just be
			// one coherent expression
			PGoTLA ptla = data.findPGoTLA(pv.getPcalInitBlock());
			Expression stmt = new TLAExprToGo(ptla, go.getImports(), new PGoTempData(data), pv)
					.toExpression();

			if (pv.getIsConstant() || !delay) {
				go.addGlobal(new VariableDeclaration(pv, stmt));
			} else {
				go.addGlobal(new VariableDeclaration(pv, null));
				Vector<Expression> toks = new Vector<>();
				toks.add(new Token(pv.getName()));
				toks.add(new Token(" = "));
				toks.add(stmt);
				main.add(new SimpleExpression(toks));
			}
		}
	}

	/**
	 * Add the position based argument command line parsing code to main
	 * 
	 * @param argN
	 * @param positionalArgs
	 * @param pv
	 */
	private void addPositionalArgToMain(int argN, Vector<Statement> positionalArgs, PGoVariable pv) {
		if (pv.getType().equals(PGoType.PROCESS_ID)) {
			Vector<Expression> emptyArgs = new Vector<>();
			Vector<Expression> exp, args;

			exp = new Vector<>();
			args = new Vector<>();
			exp.add(new FunctionCall("flag.Args", emptyArgs));
			exp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(exp));

			exp = new Vector<>();
			exp.add(new Token("processName, processArg"));
			exp.add(new Token(" := "));
			exp.add(new FunctionCall("datatypes.ParseProcessId", args));
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(PGoPrimitiveType.STRING)) {
			// var = flag.Args()[..]
			Vector<Expression> args = new Vector<>(), exp = new Vector<>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(" = "));
			exp.add(new FunctionCall("flag.Args", args));
			exp.add(new Token("[" + argN + "]"));
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(PGoPrimitiveType.INT)) {
			// var,_ = strconv.Atoi(flag.Args()[..])
			Vector<Expression> args = new Vector<>(), argExp = new Vector<>();
			FunctionCall fc = new FunctionCall("flag.Args", args);

			args = new Vector<>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			FunctionCall convert = new FunctionCall("strconv.Atoi", args);
			go.getImports().addImport("strconv");

			Vector<Expression> exp = new Vector<>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(", _"));
			exp.add(new Token(" = "));
			exp.add(convert);

			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(PGoPrimitiveType.UINT64)) {
			// var,_ = strconv.ParseUint(flag.Args()[..], 10, 64)
			Vector<Expression> args = new Vector<>(), argExp = new Vector<>();
			FunctionCall fc = new FunctionCall("flag.Args", args);

			args = new Vector<>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			args.add(new Token("10"));
			args.add(new Token("64"));
			FunctionCall convert = new FunctionCall("strconv.ParseUint", args);
			go.getImports().addImport("strconv");

			Vector<Expression> exp = new Vector<>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(", _"));
			exp.add(new Token(" = "));
			exp.add(convert);

			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(PGoPrimitiveType.FLOAT64)) {
			// var = strconv.ParseFloat64(flag.Args()[..], 10, 64)
			Vector<Expression> args = new Vector<>(), argExp = new Vector<>();
			FunctionCall fc = new FunctionCall("flag.Args", args);

			args = new Vector<>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			args.add(new Token("10"));
			args.add(new Token("64"));
			FunctionCall convert = new FunctionCall("strconv.ParseFloat64", args);
			go.getImports().addImport("strconv");

			Vector<Expression> exp = new Vector<>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(", _"));
			exp.add(new Token(" = "));
			exp.add(convert);

			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(PGoPrimitiveType.BOOL)) {
			// var = strconv.ParseBool(flag.Args()[..])
			Vector<Expression> args = new Vector<>(), argExp = new Vector<>();
			FunctionCall fc = new FunctionCall("flag.Args", args);

			args = new Vector<>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			FunctionCall convert = new FunctionCall("strconv.ParseBool", args);
			go.getImports().addImport("strconv");

			Vector<Expression> exp = new Vector<>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(", _"));
			exp.add(new Token(" = "));
			exp.add(convert);

			positionalArgs.add(new SimpleExpression(exp));
		}
	}

	// generates initialization code for the remote global state management.
	// Uses `pgo/distsys' package functions. Generated code code looks like:
	//
	// 		cfg := &Config{
	//			Endpoints: []string{"10.0.0.1:1234", "10.0.0.2:1234"}, // based on networking options
	// 			Timeout: 2, // based on networking options
	// 		}
	//		var err error
	//		globalState, err = distsys.InitGlobals(cfg)
	// 		if err != nil {
	// 			// handle error
	// 		}
	private void generateDistributedStateConfig() {
		if (!hasRemoteState()) {
			return;
		}

		go.getImports().addImport("pgo/distsys");

		data.netOpts.getStateStrategy().generateConfig(go);

		data.netOpts.getStateStrategy().initializeGlobalVariables(go);
	}

	private void addFlagArgToMain(PGoVariable pv) throws PGoTransException {
		// flag arguments

		ArgAnnotatedVariable argInfo = pv.getArgInfo();

		Vector<Expression> args = new Vector<>();
		args.add(new Token("&" + pv.getName()));
		args.add(new Token("\"" + argInfo.getArgName() + "\""));

		if (pv.getType() instanceof PGoInt) {
			// TODO we support default value and help message. Add this
			// to annotations
			args.add(new Token("0"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flag.IntVar", args));
		} else if (pv.getType() instanceof PGoBool) {
			args.add(new Token("false"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flag.BoolVar", args));
		} else if (pv.getType() instanceof PGoString) {
			args.add(new Token(""));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flag.StringVar", args));
		} else if (pv.getType() instanceof PGoNatural) {
			args.add(new Token("0"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flag.Uint64Var", args));
		} else if (pv.getType() instanceof PGoDecimal) {
			args.add(new Token("0.0"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flag.Float64Var", args));
		} else {
			throw new PGoTransException("Unsupported go argument type \"" + pv.getType().toGo()
					+ "\" for variable \"" + pv.getName() + "\"", pv.getLine());
		}
	}

}
