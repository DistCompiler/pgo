package pgo.trans.intermediate;

import java.util.Collection;
import java.util.Map.Entry;
import java.util.Vector;
import java.util.logging.Logger;

import pcal.AST;
import pcal.AST.Assert;
import pcal.AST.Assign;
import pcal.AST.Call;
import pcal.AST.CallReturn;
import pcal.AST.Clause;
import pcal.AST.Either;
import pcal.AST.Goto;
import pcal.AST.If;
import pcal.AST.LabelEither;
import pcal.AST.LabelIf;
import pcal.AST.LabeledStmt;
import pcal.AST.MacroCall;
import pcal.AST.PrintS;
import pcal.AST.Return;
import pcal.AST.SingleAssign;
import pcal.AST.Skip;
import pcal.AST.When;
import pcal.AST.While;
import pcal.AST.With;
import pgo.model.golang.*;
import pgo.model.intermediate.PGoCollectionType.PGoSet;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.*;
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
public class PGoTransStageGoGen extends PGoTransStageBase {

	// the ast
	private GoProgram go;

	// the main block pointer
	private Vector<Statement> main;

	public PGoTransStageGoGen(PGoTransStageAtomicity s1)
			throws PGoParseException, PGoTransException {
		super(s1);

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

		if (this.intermediateData.isMultiProcess) {
			main.addAll(convertGoRoutinesToGo(this.intermediateData.goroutines.values()));
		} else {
			Vector block = this.intermediateData.mainBlock;
			Vector<Statement> stmts = convertStatementToGo(block);
			main.addAll(stmts);
		}
	}

	private void generateArgParsing() throws PGoTransException {
		int argN = 0;
		boolean hasArg = false;

		Vector<Statement> positionalArgs = new Vector<Statement>();
		for (PGoVariable pv : this.intermediateData.globals.values()) {
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
		return new TLAExprToGo(tla, go.getImports(), new PGoTempData(intermediateData)).toExpression();
	}

	private Vector<Expression> TLAToGo(Vector<PGoTLA> tla) throws PGoTransException {
		Vector<Expression> ret = new Vector<>();
		for (PGoTLA ptla : tla) {
			ret.add(new TLAExprToGo(ptla, go.getImports(), new PGoTempData(intermediateData)).toExpression());
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
		return new PcalASTUtil.Walker<Vector<Statement>>() {

			@Override
			protected void init() {
				result = new Vector<Statement>();
			}

			protected void visit(LabeledStmt ls) throws PGoTransException {
				// result.add(new Label(ls.label)); TODO add cleanup for
				// non-used labels. Go compile fails on non-used labels. So scan
				// through for gotos and remove all labels that isnt used. Or
				// somehow keep track of which labels are used in preprocessing
				super.visit(ls);
			}

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
						exps.add(new Token(sa.lhs.var));
						exps.add(new Token(" = "));
						exps.add(new Token(sa.lhs.var + "_new"));
						result.add(new SimpleExpression(exps));
					}
				} else {
					// only one assign, just treat it like a single assignment
					// without temp variables
					walk(as.ass);
				}
			}

			protected void visit(SingleAssign sa) throws PGoTransException {
				Vector<Expression> exps = new Vector<>();
				exps.add(new Token(sa.lhs.var));
				// TODO parse sub for [2] etc
				exps.add(new Token(" = "));
				// TODO this is tlaexpr exps.add(sa.rhs);
				Vector<Expression> rhs = TLAToGo(new TLAExprParser(sa.rhs, sa.line).getResult());
				assert (rhs.size() == 1);
				exps.add(rhs.get(0));

				result.add(new SimpleExpression(exps));
			}

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

			protected void visit(Either ei) {
				for (Vector v : (Vector<Vector>) ei.ors) {
					// either has vector of vectors
					// walk(v);
					// TODO handle either
				}
			}

			protected void visit(With with) {
				// TODO handle
				// Select a random element of with.exp and perform with.Do on it
				go.getImports().addImport("math/rand");
				Vector<Statement> pre; // handle random selection and declaration of var
				// walk(with.Do);
			}

			protected void visit(When when) {
				// TODO handle await
			}

			protected void visit(PrintS ps) throws PGoTransException {
				// TODO parse ps.exp
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
						// TODO handle printing sets/arrays/maps if its legal in
						// plscal
					}
				}

				args.add(0, new Token("\"" + String.join(" ", strfmt) + "\\n\""));

				go.getImports().addImport("fmt");
				FunctionCall fc = new FunctionCall("fmt.Printf", args);
				result.add(fc);
			}

			protected void visit(Assert as) {
				// TODO actually do we even want this?
			}

			protected void visit(Skip s) {
				Vector<String> cmt = new Vector<>();
				cmt.add("TODO skipped from pluscal");
				result.add(new Comment(cmt, false));
			}

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

			protected void visit(LabelEither le) {
				// TODO
				// walk(le.clauses);
			}

			protected void visit(Clause c) {
				// TODO handle with either
				// walk(c.unlabOr);
				// walk(c.labOr);
			}

			protected void visit(Call c) {
				// TODO c.args is vector of tlaExpr
				Vector<Expression> args = new Vector<>();
				FunctionCall fc = new FunctionCall(c.to, args);
				result.add(fc);
			}

			protected void visit(Return r) {
				// TODO learn to get the return variable
				result.add(new pgo.model.golang.Return(null));
			}

			protected void visit(CallReturn cr) {
				// TODO c.args is vector of tlaExpr
				Vector<Expression> args = new Vector<>();
				FunctionCall fc = new FunctionCall(cr.to, args);
				result.add(fc);
			}

			protected void visit(Goto g) {
				result.add(new pgo.model.golang.GoTo(g.to));
			}

			protected void visit(MacroCall m) {
				// TODO
			}
		}.getResult(stmts);
	}

	/**
	 * Generate the go routines init blocks as statements
	 * 
	 * @param goroutines
	 */
	private Vector<Statement> convertGoRoutinesToGo(Collection<PGoRoutineInit> goroutines) {
		return null;
		// TODO (issue #10) Auto-generated method stub

	}

	/**
	 * Create declarations for all functions
	 * 
	 * @throws PGoTransException
	 */
	private void generateFunctions() throws PGoTransException {
		for (PGoFunction pf : this.intermediateData.funcs.values()) {

			Vector<ParameterDeclaration> params = new Vector<ParameterDeclaration>();
			for (PGoVariable param : pf.getParams()) {
				params.add(new ParameterDeclaration(param.getName(), param.getType()));
			}
			Vector<VariableDeclaration> locals = new Vector<VariableDeclaration>();
			for (PGoVariable local : pf.getVariables()) {
				SimpleExpression e = null; // TODO (issue #14) from tla
				Vector<Statement> init = new Vector<>(); // TODO from
															// tla
				locals.add(new VariableDeclaration(local.getName(), local.getType(), e, init,
						local.getIsConstant()));
			}

			Vector<Statement> body = new Vector<>();
			body.addAll(convertStatementToGo(pf.getBody()));

			Function f = new Function(pf.getName(), pf.getReturnType(), params, locals, body);

			go.addFunction(f);
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
		for (PGoVariable pv : this.intermediateData.globals.values()) {
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
			SimpleExpression se = null;
			assert (stmt.size() == 1);

			if (stmt.get(0) instanceof SimpleExpression) {
				se = (SimpleExpression) stmt.remove(0);
			} else {
				se = new SimpleExpression(new Vector<Expression>() {
					{
						add((Expression) stmt.remove(0));
					}
				});
			}

			go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), null,
					new Vector<>(), pv.getIsConstant()));
			Vector<Expression> toks = new Vector<>();
			toks.add(new Token("_, " + pv.getName()));
			toks.add(new Token(" = "));
			toks.add(new Token("range "));
			toks.add(se);

			For loop = new For(new SimpleExpression(toks), new Vector<>());
			main.add(loop);
			main = loop.getThen();
			// we set the rest of the main to go in here
		}

		for (PGoVariable pv : this.intermediateData.globals.values()) {
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
				Vector<Expression> stmt = TLAToGo(ptla);
				SimpleExpression se = null;
				assert (stmt.size() == 1);

				if (stmt.get(0) instanceof SimpleExpression) {
					se = (SimpleExpression) stmt.remove(0);
				} else {
					se = new SimpleExpression(new Vector<Expression>() {
						{
							add((Expression) stmt.remove(0));
						}
					});
				}

				if (pv.getIsConstant() || !delay) {
					go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), se,
							new Vector<>(), pv.getIsConstant()));

					if (stmt.size() > 0) {
						// complex initializations go into main
						main.addAll(stmt);
					}
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
			exp.add(new Token(",_"));
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
			exp.add(new Token(",_"));
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
			exp.add(new Token(",_"));
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
			exp.add(new Token(",_"));
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
