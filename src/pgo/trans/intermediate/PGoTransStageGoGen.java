package pgo.trans.intermediate;

import java.util.Collection;
import java.util.Map.Entry;
import java.util.Vector;
import java.util.logging.Logger;

import pcal.AST;
import pcal.AST.Assert;
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
import pgo.model.golang.Comment;
import pgo.model.golang.Expression;
import pgo.model.golang.For;
import pgo.model.golang.Function;
import pgo.model.golang.FunctionCall;
import pgo.model.golang.GoProgram;
import pgo.model.golang.Label;
import pgo.model.golang.ParameterDeclaration;
import pgo.model.golang.SimpleExpression;
import pgo.model.golang.Statement;
import pgo.model.golang.Token;
import pgo.model.golang.VariableDeclaration;
import pgo.model.intermediate.PGoFunction;
import pgo.model.intermediate.PGoPrimitiveType;
import pgo.model.intermediate.PGoRoutineInit;
import pgo.model.intermediate.PGoVariable;
import pgo.model.tla.PGoTLA;
import pgo.parser.PGoParseException;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;
import pgo.util.PcalASTUtil;

/**
 * The last stage of the translation. Takes given intermediate data and converts
 * it to a Go AST, properly
 *
 */
public class PGoTransStageGoGen extends PGoTransStageBase {

	// the ast
	private GoProgram go;

	public PGoTransStageGoGen(PGoTransStageAtomicity s1) throws PGoParseException, PGoTransException {
		super(s1);

		go = new GoProgram("main");

		generateGlobalVariables();
		generateFunctions();
		generateMain();
	}

	public GoProgram getGo() {
		return go;
	}

	private void generateMain() throws PGoTransException {
		// TODO Auto-generated method stub
		Logger.getGlobal().info("Generating Main Function");

		int argN = 0;
		boolean hasArg = false;
		
		Vector<Statement> positionalArgs = new Vector<Statement>();
		for (PGoVariable pv : this.intermediateData.globals.values()) {
			// Add flags as necessary
			if (pv.getArgInfo() != null) {
				Logger.getGlobal().info("Generating command line argument code for variable \"" + pv.getName() + "\"");
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

		Function main = go.getMain();
		Vector<Statement> body = main.getBody();
		if (hasArg) {
			body.add(new FunctionCall("flag.Parse", new Vector<Expression>()));
			body.addAll(positionalArgs);
			body.add(new Token(""));
		}
		
		if (this.intermediateData.isMultiProcess) {
			body.addAll(convertGoRoutinesToGo(this.intermediateData.goroutines.values()));
		} else {
			Vector block = this.intermediateData.mainBlock;
			Vector<Statement> stmts = convertStatementToGo(block);
			body.addAll(stmts);
		}
	}

	/**
	 * Converts a given code black into Go code. Given code block should not
	 * have function definitions and such in pluscal
	 * 
	 * @param stmts
	 * @return
	 */
	private Vector<Statement> convertStatementToGo(Vector<AST> stmts) {
		return new PcalASTUtil.Walker<Vector<Statement>>() {

			@Override
			protected void init() {
				result = new Vector<Statement>();
			}

			protected void visit(LabeledStmt ls) {
				result.add(new Label(ls.label));
				super.visit(ls);
			}

			protected void visit(While w) {
				// TODO w.test is the condition
				Vector<Expression> exps = new Vector<Expression>();
				Expression se = new SimpleExpression(exps);
				Vector<Statement> loopBody = new Vector<Statement>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = loopBody; // we send the loop body to be filled
				super.visit(w); // visit the loop body
				For loopAst = new For(se, result);
				result = tempRes;
				result.add(loopAst);
			}

			protected void visit(SingleAssign sa) {
				Vector<Expression> exps = new Vector<Expression>();
				exps.add(new Token(sa.lhs.var));
				// TODO parse sub for [2] etc
				exps.add(new Token(" = "));
				// TODO this is tlaexpr exps.add(sa.rhs);
				result.add(new SimpleExpression(exps));

			}

			protected void visit(If ifast) {
				// TODO w.test is the condition
				Vector<Expression> exps = new Vector<Expression>();
				Expression se = new SimpleExpression(exps);

				Vector<Statement> thenS = new Vector<Statement>();
				Vector<Statement> elseS = new Vector<Statement>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = thenS; // we send the loop body to be filled
				walk(ifast.Then);
				result = elseS;
				walk(ifast.Else);

				pgo.model.golang.If ifAst = new pgo.model.golang.If(se, thenS, elseS);

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
				// walk(with.Do);
			}

			protected void visit(When when) {
				// TODO handle await
			}

			protected void visit(PrintS ps) {
				// TODO parse ps.exp
				Vector<Expression> args = new Vector<Expression>();
				go.getImports().addImport("fmt");
				FunctionCall fc = new FunctionCall("fmt.Println", args);
				result.add(fc);
			}

			protected void visit(Assert as) {
				// TODO actually do we even want this?
			}

			protected void visit(Skip s) {
				Vector<String> cmt = new Vector<String>();
				cmt.add("TODO skipped from pluscal");
				result.add(new Comment(cmt, false));
			}

			protected void visit(LabelIf lif) {
				// TODO w.test is the condition
				Vector<Expression> exps = new Vector<Expression>();
				Expression se = new SimpleExpression(exps);

				Vector<Statement> thenS = new Vector<Statement>();
				Vector<Statement> elseS = new Vector<Statement>();

				// Store the result so far temporarily
				Vector<Statement> tempRes = result;
				result = thenS; // we send the loop body to be filled
				walk(lif.unlabThen);
				walk(lif.labThen);
				result = elseS;
				walk(lif.unlabElse);
				walk(lif.labElse);

				pgo.model.golang.If ifAst = new pgo.model.golang.If(se, thenS, elseS);

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
				Vector<Expression> args = new Vector<Expression>();
				FunctionCall fc = new FunctionCall(c.to, args);
				result.add(fc);
			}

			protected void visit(Return r) {
				// TODO learn to get the return variable
				result.add(new pgo.model.golang.Return(null));
			}

			protected void visit(CallReturn cr) {
				// TODO c.args is vector of tlaExpr
				Vector<Expression> args = new Vector<Expression>();
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
		// TODO Auto-generated method stub

	}

	/**
	 * Create declarations for all functions
	 */
	private void generateFunctions() {
		for (PGoFunction pf : this.intermediateData.funcs.values()) {
			
			Vector<ParameterDeclaration> params = new Vector<ParameterDeclaration>();
			for (PGoVariable param : pf.getParams()) {
				params.add(new ParameterDeclaration(param.getName(), param.getType()));
			}
			Vector<VariableDeclaration> locals = new Vector<VariableDeclaration>();
			for (PGoVariable local : pf.getVariables()) {
				SimpleExpression e = null; // TODO from tla
				Vector<Statement> init = new Vector<Statement>(); // TODO from tla
				locals.add(new VariableDeclaration(local.getName(), local.getType(), e, init, local.getIsConstant()));
			}
			
			Vector<Statement> body = new Vector<Statement>();
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
		for (PGoVariable pv : this.intermediateData.globals.values()) {
			Logger.getGlobal().info("Generating go variable \"" + pv.getName() + "\"");
			if (pv.getIsSimpleAssignInit()) {
				if (!pv.getGoVal().isEmpty()) {
					// If we have a specifieVector<E>ang value for the variable,
					// use it
					Vector<Expression> exp = new Vector<Expression>();
					exp.add(new Token(pv.getGoVal()));
					SimpleExpression s = new SimpleExpression(exp);

					go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), s, pv.getIsConstant()));
					continue;
				} else if (pv.getArgInfo() != null) {
					go.addGlobal(new VariableDeclaration(pv.getName(), pv.getType(), null, pv.getIsConstant()));
					// generateMain will fill the main function
				} else {
					// being part of the rhs, the parsed result should just be
					// one coherent expression
					TLAExprParser parser = new TLAExprParser(pv.getPcalInitBlock(), pv.getLine());
					Vector<PGoTLA> ptla = parser.getResult();
					assert (ptla.size() == 1);
					// Vector<Statement> stmt = tlaTokenToStatement(ptla);
					// Map.Entry<SimpleExpression, Vector<Statement>> value =
					// getGoValue(pv, ptla.get(0));
					// go.addGlobal(new VariableDeclaration(pv.getName(),
					// pv.getType(), value.getKey(), value.getValue(),
					// pv.getIsConstant()));
				}
			}

		}
	}

	/**
	 * Given a tla ast, converts it to a Go value equivalent to assign to v
	 * 
	 * @param pGoTLA
	 * @return
	 */
	private Entry<SimpleExpression, Vector<Statement>> getGoValue(PGoVariable v, PGoTLA pGoTLA) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Add the position based argument command line parsing code to main
	 * 
	 * @param argN
	 * @param positionalArgs
	 * @param pv
	 */
	private void addPositionalArgToMain(int argN, Vector<Statement> positionalArgs, PGoVariable pv) {
		if (pv.getType().equals(new PGoPrimitiveType.PGoString())) {
			// var = flag.Args()[..]
			Vector<Expression> args = new Vector<Expression>();
			Vector<Expression> exp = new Vector<Expression>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(" = "));
			exp.add(new FunctionCall("flag.Args", args));
			exp.add(new Token("[" + argN + "]"));
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoInt())) {
			// var,_ =  strconv.Atoi(flag.Args()[..])
			Vector<Expression> args = new Vector<Expression>();
			Vector<Expression> argExp = new Vector<Expression>();
			FunctionCall fc = new FunctionCall("flag.Args", args);
			
			args = new Vector<Expression>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			FunctionCall convert = new FunctionCall("strconv.Atoi", args);
			go.getImports().addImport("strconv");
			
			Vector<Expression> exp = new Vector<Expression>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(",_"));
			exp.add(new Token(" = "));
			exp.add(convert);
			
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoNatural())) {
			// var,_ =  strconv.ParseUint(flag.Args()[..], 10, 64)
			Vector<Expression> args = new Vector<Expression>();
			Vector<Expression> argExp = new Vector<Expression>();
			FunctionCall fc = new FunctionCall("flag.Args", args);
			
			args = new Vector<Expression>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			args.add(new Token("10"));
			args.add(new Token("64"));
			FunctionCall convert = new FunctionCall("strconv.ParseUint", args);
			go.getImports().addImport("strconv");
			
			Vector<Expression> exp = new Vector<Expression>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(",_"));
			exp.add(new Token(" = "));
			exp.add(convert);
			
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoDecimal())) {
			// var =  strconv.ParseFloat64(flag.Args()[..], 10, 64)
			Vector<Expression> args = new Vector<Expression>();
			Vector<Expression> argExp = new Vector<Expression>();
			FunctionCall fc = new FunctionCall("flag.Args", args);
			
			args = new Vector<Expression>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			args.add(new Token("10"));
			args.add(new Token("64"));
			FunctionCall convert = new FunctionCall("strconv.ParseFloat64", args);
			go.getImports().addImport("strconv");
			
			Vector<Expression> exp = new Vector<Expression>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(",_"));
			exp.add(new Token(" = "));
			exp.add(convert);
			
			positionalArgs.add(new SimpleExpression(exp));
		} else if (pv.getType().equals(new PGoPrimitiveType.PGoBool())) {
			// var =  strconv.ParseBool(flag.Args()[..])
			Vector<Expression> args = new Vector<Expression>();
			Vector<Expression> argExp = new Vector<Expression>();
			FunctionCall fc = new FunctionCall("flag.Args", args);
			
			args = new Vector<Expression>();
			argExp.add(fc);
			argExp.add(new Token("[" + argN + "]"));
			args.add(new SimpleExpression(argExp));
			FunctionCall convert = new FunctionCall("strconv.ParseBool", args);
			go.getImports().addImport("strconv");
			
			Vector<Expression> exp = new Vector<Expression>();
			exp.add(new Token(pv.getName()));
			exp.add(new Token(",_"));
			exp.add(new Token(" = "));
			exp.add(convert);
			
			positionalArgs.add(new SimpleExpression(exp));
		}
	}

	private void addFlagArgToMain(PGoVariable pv) throws PGoTransException {
		// flag arguments
		Function main = go.getMain();
		Vector<Statement> body = main.getBody();
	
		Vector<Expression> args = new Vector<Expression>();
		args.add(new Token("&" + pv.getName()));
		args.add(new Token(pv.getArgInfo().getName()));
	
		if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoInt())) {
			// TODO we support default value and help message. Add this
			// to annotations
			args.add(new Token("0"));
			args.add(new Token("\"\""));
			body.add(new FunctionCall("flagIntVar", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoBool())) {
			args.add(new Token("false"));
			args.add(new Token("\"\""));
			body.add(new FunctionCall("flagBoolVar", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoString())) {
			args.add(new Token(""));
			args.add(new Token("\"\""));
			body.add(new FunctionCall("flagStringVar", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoNatural())) {
			args.add(new Token("0"));
			args.add(new Token("\"\""));
			body.add(new FunctionCall("flagUint64Var", args));
		} else if (pv.getType().toGo().equals(new PGoPrimitiveType.PGoDecimal())) {
			args.add(new Token("0.0"));
			args.add(new Token("\"\""));
			body.add(new FunctionCall("flagFloat64Var", args));
		} else {
			throw new PGoTransException("Unsupported go argument type \"" + pv.getType().toGo()
					+ "\" for variable \"" + pv.getName() + "\"", pv.getLine());
		}
	}

}
