package pgo.trans.intermediate;

import java.util.Collection;
import java.util.Vector;
import java.util.logging.Logger;

import pcal.AST;
import pcal.AST.*;
import pcal.AST.If;
import pcal.AST.Return;
import pcal.TLAToken;
import pgo.model.golang.*;
import pgo.model.intermediate.PGoCollectionType.PGoMap;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoCollectionType.PGoSlice;
import pgo.model.intermediate.PGoCollectionType.PGoTuple;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoMiscellaneousType.PGoWaitGroup;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.PGoTLA;
import pgo.model.tla.PGoTLAArray;
import pgo.model.tla.PGoTLABool;
import pgo.model.tla.PGoTLADefinition;
import pgo.model.tla.PGoTLAFunctionCall;
import pgo.model.tla.PGoTLANumber;
import pgo.model.tla.PGoTLAString;
import pgo.model.tla.PGoTLAVariable;
import pgo.model.tla.TLAExprToGo;
import pgo.parser.PGoParseException;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

/**
 * The last stage of the translation. Takes given intermediate data and converts
 * it to a Go AST,
 * properly
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

	public PGoTransStageGoGen(PGoTransStageAtomicity s1) throws PGoParseException, PGoTransException {
		this.data = s1.data;

		go = new GoProgram("main");

		main = go.getMain().getBody();

		generateArgParsing();
		generateGlobalVariables();
		generateFunctions();
		generateMain();
	}

	public GoProgram getGo() {
		return go;
	}

	private void generateMain() throws PGoTransException {
		Logger.getGlobal().info("Generating Main Function");

		if (this.data.isMultiProcess) {
			main.addAll(convertGoRoutinesToGo(this.data.goroutines.values()));
		} else {
			Vector block = this.data.mainBlock;
			Vector<Statement> stmts = convertStatementToGo(block);
			main.addAll(stmts);
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

		Vector<Statement> positionalArgs = new Vector<Statement>();
		for (PGoVariable pv : this.data.globals.values()) {
			// Add flags as necessary
			if (pv.getArgInfo() != null) {
				Logger.getGlobal().info("Generating command line argument code for variable \""
						+ pv.getName() + "\"");
				go.getImports().addImport("flag");
				hasArg = true;
				if (pv.getArgInfo().isPositionalArg()) {
					addPositionalArgToMain(argN, positionalArgs, pv);

					argN++;
				} else {
					addFlagArgToMain(pv);
				}

			}
		}

		if (hasArg) {
			main.add(new FunctionCall("flag.Parse", new Vector<Expression>()));
			main.addAll(positionalArgs);
			main.add(new Token(""));
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

	private Vector<Expression> TLAToGo(Vector<PGoTLA> tla) throws PGoTransException {
		Vector<Expression> ret = new Vector<>();
		for (PGoTLA ptla : tla) {
			if (data instanceof PGoTempData) {
				ret.add(new TLAExprToGo(ptla, go.getImports(), new PGoTempData((PGoTempData) data))
						.toExpression());
			} else {
				ret.add(new TLAExprToGo(ptla, go.getImports(), new PGoTempData(data)).toExpression());
			}
		}
		return ret;
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

			@Override
			protected void init() {
				result = new Vector<Statement>();
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				// only add the label if we use it in a goto
				if (go.isLabelUsed(ls.label)) {
					result.add(new Label(ls.label));
				}
				super.visit(ls);
			}

			@Override
			protected void visit(While w) throws PGoTransException {
				Vector<Expression> cond = TLAToGo(new TLAExprParser(w.test, w.line).getResult());
				assert (cond.size() == 1);

				Vector<Statement> loopBody = new Vector<>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = loopBody; // we send the loop body to be filled
				super.visit(w); // visit the loop body
				For loopAst = new For(cond.get(0), result);
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
						// TODO this is tlaexpr exps.add(sa.rhs);
						Vector<Expression> rhs = TLAToGo(new TLAExprParser(sa.rhs, sa.line).getResult());

						assert (rhs.size() == 1);
						exps.add(rhs.get(0));

						result.add(new SimpleExpression(exps));
					}

					for (SingleAssign sa : (Vector<SingleAssign>) as.ass) {
						Vector<Expression> exps = new Vector<>();
						if (!sa.lhs.sub.tokens.isEmpty()) {
							// the sub is [expr, expr...] (map/array access) or
							// .<name> for a record field

							// to parse properly, prepend the variable name
							((Vector<TLAToken>) sa.lhs.sub.tokens.get(0)).add(0,
									new TLAToken(sa.lhs.var, 0, TLAToken.IDENT));
							Vector<PGoTLA> ptla = new TLAExprParser(sa.lhs.sub, as.line).getResult();
							assert (ptla.size() == 1);
							// TODO handle record fields
							assert (ptla.get(0) instanceof PGoTLAFunctionCall);
							PGoTLAFunctionCall fc = (PGoTLAFunctionCall) ptla.get(0);
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
									params.add(new FunctionCall("pgoutil.NewTuple", tupleElts));
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
				Vector<Expression> rhs = TLAToGo(new TLAExprParser(sa.rhs, sa.line).getResult());
				assert (rhs.size() == 1);
				if (!sa.lhs.sub.tokens.isEmpty()) {
					// the sub is [expr, expr...] (map/array access) or
					// .<name> for a record field

					// to parse properly, prepend the variable name
					((Vector<TLAToken>) sa.lhs.sub.tokens.get(0)).add(0,
							new TLAToken(sa.lhs.var, 0, TLAToken.IDENT));
					Vector<PGoTLA> ptla = new TLAExprParser(sa.lhs.sub, sa.line).getResult();
					assert (ptla.size() == 1);
					// TODO handle record fields
					assert (ptla.get(0) instanceof PGoTLAFunctionCall);
					PGoTLAFunctionCall fc = (PGoTLAFunctionCall) ptla.get(0);
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
						exps.add(rhs.get(0));
					} else if (assign.getType() instanceof PGoTuple) {
						// var = var.Set(index, assign)
						assert (fc.getParams().size() == 1);
						exps.add(new Token(sa.lhs.var));
						exps.add(new Token(" = "));
						Vector<Expression> params = new Vector<>();
						params.add(TLAToGo(fc.getParams().get(0)));
						params.add(rhs.get(0));
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
							params.add(new FunctionCall("pgoutil.NewTuple", tupleElts));
						}
						params.add(rhs.get(0));
						exps.add(new FunctionCall("Put", params, new Token(sa.lhs.var)));
					} else {
						assert false;
					}
				} else {
					// the lhs is a simple variable
					exps.add(new Token(sa.lhs.var));
					exps.add(new Token(" = "));
					exps.add(rhs.get(0));
				}
				result.add(new SimpleExpression(exps));
			}

			@Override
			protected void visit(If ifast) throws PGoTransException {
				Vector<Expression> cond = TLAToGo(new TLAExprParser(ifast.test, ifast.line).getResult());
				assert (cond.size() == 1);

				Vector<Statement> thenS = new Vector<>(), elseS = new Vector<>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = thenS; // we send the loop body to be filled
				walk(ifast.Then);
				result = elseS;
				walk(ifast.Else);

				pgo.model.golang.If ifAst = new pgo.model.golang.If(cond.get(0), thenS, elseS);

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
						Vector<PGoTLA> varExpr = new TLAExprParser(with.exp, with.line).getResult();
						assert (varExpr.size() == 1);
						TLAExprToGo trans = new TLAExprToGo(varExpr.get(0), go.getImports(),
								new PGoTempData((PGoTempData) data));
						Vector<Expression> se = new Vector<>();
						se.add(new Token(varName));
						se.add(new Token(" := "));
						se.add(trans.toExpression());
						pre.add(new SimpleExpression(se));
						((PGoTempData) data).getLocals().put(varName,
								PGoVariable.convert(varName, trans.getType()));
					} else {
						// x \in S
						// x := S.ToSlice()[rand.Intn(S.Size())].(type)
						Vector<PGoTLA> setExpr = new TLAExprParser(with.exp, with.line).getResult();
						assert (setExpr.size() == 1);
						TLAExprToGo trans = new TLAExprToGo(setExpr.get(0), go.getImports(),
								new PGoTempData(data));
						PGoType setType = trans.getType();
						assert (setType instanceof PGoSet);
						PGoType containedType = ((PGoSet) setType).getElementType();
						Vector<Expression> se = new Vector<>();
						se.add(new Token(varName));
						se.add(new Token(" := "));
						Vector<Expression> rhs = new Vector<>();
						rhs.add(new FunctionCall("ToSlice", new Vector<>(), trans.toExpression()));
						rhs.add(new Token("["));
						rhs.add(new FunctionCall("rand.Intn", new Vector<Expression>() {
							{
								add(new FunctionCall("Size", new Vector<>(), trans.toExpression()));
							}
						}));
						rhs.add(new Token("]"));
						se.add(new TypeAssertion(new SimpleExpression(rhs), containedType));
						pre.add(new SimpleExpression(se));
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

			@Override
			protected void visit(When when) {
				// TODO handle await
			}

			@Override
			protected void visit(PrintS ps) throws PGoTransException {
				Vector<PGoTLA> argExp = new TLAExprParser(ps.exp, ps.line).getResult();
				assert (argExp.size() == 1); // print should only have 1
												// argument as a tupple
				assert (argExp.get(0) instanceof PGoTLAArray); // convert tupple
																// to array

				PGoTLAArray tup = (PGoTLAArray) argExp.get(0);
				Vector<String> strfmt = new Vector<String>();
				Vector<Expression> args = new Vector<Expression>();
				for (PGoTLA arg : tup.getContents()) {
					if (arg instanceof PGoTLAString) {
						strfmt.add(((PGoTLAString) arg).getString());
					} else if (arg instanceof PGoTLANumber) {
						strfmt.add(((PGoTLANumber) arg).getVal());
					} else if (arg instanceof PGoTLABool) {
						strfmt.add(String.valueOf(((PGoTLABool) arg).getVal()));
					} else if (arg instanceof PGoTLAVariable) {
						strfmt.add("%v"); // use go default printing
						args.add(new Token(((PGoTLAVariable) arg).getName()));
					} else {
						strfmt.add("%v");
						args.add(new TLAExprToGo(arg, go.getImports(), new PGoTempData(data))
								.toExpression());
					}
				}

				args.add(0, new Token("\"" + String.join(" ", strfmt) + "\\n\""));

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
				Vector<Expression> cond = TLAToGo(new TLAExprParser(lif.test, lif.line).getResult());
				assert (cond.size() == 1);

				Vector<Statement> thenS = new Vector<>(), elseS = new Vector<>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = thenS; // we send the loop body to be filled
				walk(lif.unlabThen);
				walk(lif.labThen);
				result = elseS;
				walk(lif.unlabElse);
				walk(lif.labElse);

				pgo.model.golang.If ifAst = new pgo.model.golang.If(cond.get(0), thenS, elseS);

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
			protected void visit(Call c) {
				// TODO c.args is vector of tlaExpr
				Vector<Expression> args = new Vector<>();
				FunctionCall fc = new FunctionCall(c.to, args);
				result.add(fc);
			}

			@Override
			protected void visit(Return r) {
				// TODO learn to get the return variable
				result.add(new pgo.model.golang.Return(null));
			}

			@Override
			protected void visit(CallReturn cr) {
				// TODO c.args is vector of tlaExpr
				Vector<Expression> args = new Vector<>();
				FunctionCall fc = new FunctionCall(cr.to, args);
				result.add(fc);
			}

			@Override
			protected void visit(Goto g) {
				result.add(new pgo.model.golang.GoTo(g.to));
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
				Vector<PGoTLA> id = new TLAExprParser(goroutine.getInitTLA(), -1).getResult();
				assert (id.size() == 1);
				se.add(new FunctionCall(goroutine.getName(), new Vector<Expression>() {
					{
						add(new TLAExprToGo(id.get(0), go.getImports(), new PGoTempData(data))
								.toExpression());
					}
				}));
			} else {
				// for procId := range set.Iter() {
				// PGoWait.Add(1)
				// go foo(procId.(type))
				// }

				Vector<PGoTLA> setTLA = new TLAExprParser(goroutine.getInitTLA(), -1).getResult();
				assert (setTLA.size() == 1);
				TLAExprToGo trans = new TLAExprToGo(setTLA.get(0), go.getImports(), new PGoTempData(data));
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

			Vector<ParameterDeclaration> params = new Vector<ParameterDeclaration>();
			for (PGoVariable param : pf.getParams()) {
				params.add(new ParameterDeclaration(param.getName(), param.getType()));
				localData.getLocals().put(param.getName(), param);
			}
			Vector<VariableDeclaration> locals = new Vector<VariableDeclaration>();
			for (PGoVariable local : pf.getVariables()) {
				Vector<PGoTLA> initTLA = new TLAExprParser(local.getPcalInitBlock(), local.getLine()).getResult();
				assert (initTLA.size() <= 1);
				// if initTLA is empty, the local init is defaultInitValue
				// (no initialization code)
				if (initTLA.isEmpty()) {
					locals.add(new VariableDeclaration(local.getName(), local.getType(), null, new Vector<>(),
							local.getIsConstant()));
				} else {
					Expression init = new TLAExprToGo(initTLA.get(0), go.getImports(), localData, local).toExpression();
					Vector<Expression> se = new Vector<>();
					se.add(init);
					locals.add(new VariableDeclaration(local.getName(), local.getType(), new SimpleExpression(se),
							new Vector<>(), local.getIsConstant()));
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

			TLAExprToGo trans = new TLAExprToGo(tlaDef.getExpr(), go.getImports(), temp);
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
			TLAExprParser parser = new TLAExprParser(pv.getPcalInitBlock(), pv.getLine());
			Vector<PGoTLA> ptla = parser.getResult();
			assert (ptla.size() == 1);
			Vector<Expression> stmt = TLAToGo(ptla);

			assert (stmt.size() == 1);
			Expression se = stmt.get(0);

			go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), null,
					new Vector<>(), pv.getIsConstant()));
			Vector<Expression> toks = new Vector<>();
			toks.add(new Token(pv.getName() + "_interface"));
			toks.add(new Token(" := "));
			toks.add(new Token("range "));
			toks.add(new FunctionCall("Iter", new Vector<>(), se));

			For loop = new For(new SimpleExpression(toks), new Vector<>());
			main.add(loop);
			// we need to cast the interface value to int
			Vector<Expression> cast = new Vector<>();
			cast.add(new Token(pv.getName()));
			cast.add(new Token(" = "));
			cast.add(new TypeAssertion(new Token(pv.getName() + "_interface"), PGoType.inferFromGoTypeName("int")));
			loop.getThen().add(new SimpleExpression(cast));
			main = loop.getThen();
			// we set the rest of the main to go in here
		}

		for (PGoVariable pv : this.data.globals.values()) {
			if (!pv.getIsSimpleAssignInit()) {
				// already did var \in set
				continue;
			}
			Logger.getGlobal().info("Generating go variable \"" + pv.getName() + "\"");

			if (!pv.getGoVal().isEmpty()) {
				// If we have a specifieVector<E>ang value for the variable,
				// use it
				Vector<Expression> exp = new Vector<>();
				exp.add(new Token(pv.getGoVal()));
				SimpleExpression s = new SimpleExpression(exp);

				go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), s,
						pv.getIsConstant()));
				continue;
			} else if (pv.getArgInfo() != null) {
				go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), null,
						pv.getIsConstant()));
				// generateMain will fill the main function
			} else {
				// being part of the rhs, the parsed result should just be
				// one coherent expression
				TLAExprParser parser = new TLAExprParser(pv.getPcalInitBlock(), pv.getLine());
				Vector<PGoTLA> ptla = parser.getResult();
				assert (ptla.size() == 1);
				Expression stmt = new TLAExprToGo(ptla.get(0), go.getImports(), new PGoTempData(data), pv)
						.toExpression();
				SimpleExpression se = new SimpleExpression(new Vector<Expression>() {
					{
						add(stmt);
					}
				});

				if (pv.getIsConstant() || !delay) {
					go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), se,
							new Vector<>(), pv.getIsConstant()));
				} else {
					go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), null,
							new Vector<>(), pv.getIsConstant()));
					Vector<Expression> toks = new Vector<>();
					toks.add(new Token(pv.getName()));
					toks.add(new Token(" = "));
					toks.add(se);
					main.add(new SimpleExpression(toks));
				}
			}
		}

		// if the program contains goroutines, we need to add a waitgroup
		// (prevent early termination of main goroutine) and a dummy channel
		// (synchronize the start of the goroutines)
		if (!data.goroutines.isEmpty()) {
			go.getImports().addImport("sync");
			go.addGlobal(new VariableDeclaration("PGoWait", new PGoWaitGroup(), null, false));

			Vector<Expression> se = new Vector<>();
			se.add(new FunctionCall("make", new Vector<Expression>() {
				{
					add(new Token(PGoType.inferFromGoTypeName("chan[bool]").toGo()));
				}
			}));
			VariableDeclaration chanDecl = new VariableDeclaration("PGoStart",
					PGoType.inferFromGoTypeName("chan[bool]"), new SimpleExpression(se), false);
			go.addGlobal(chanDecl);
		}
	}

	/**
	 * Add the position based argument command line parsing code to main
	 * 
	 * @param argN
	 * @param positionalArgs
	 * @param pv
	 */
	private void addPositionalArgToMain(int argN, Vector<Statement> positionalArgs,
			PGoVariable pv) {
		if (pv.getType().equals(new PGoPrimitiveType.PGoString())) {
			// var = flag.Args()[..]
			Vector<Expression> args = new Vector<>(), exp = new Vector<>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(" = "));
			exp.add(new FunctionCall("flag.Args", args));
			exp.add(new Token("[" + argN + "]"));
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoInt())) {
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
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoNatural())) {
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
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoDecimal())) {
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
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoBool())) {
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

	private void addFlagArgToMain(PGoVariable pv) throws PGoTransException {
		// flag arguments

		Vector<Expression> args = new Vector<>();
		args.add(new Token("&" + pv.getName()));
		args.add(new Token(pv.getArgInfo().getName()));

		if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoInt().toGo())) {
			// TODO we support default value and help message. Add this
			// to annotations
			args.add(new Token("0"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flagIntVar", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoBool().toGo())) {
			args.add(new Token("false"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flagBoolVar", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoString().toGo())) {
			args.add(new Token(""));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flagStringVar", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoNatural().toGo())) {
			args.add(new Token("0"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flagUint64Var", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoDecimal().toGo())) {
			args.add(new Token("0.0"));
			args.add(new Token("\"\""));
			main.add(new FunctionCall("flagFloat64Var", args));
		} else {
			throw new PGoTransException("Unsupported go argument type \"" + pv.getType().toGo()
					+ "\" for variable \"" + pv.getName() + "\"", pv.getLine());
		}
	}

}
