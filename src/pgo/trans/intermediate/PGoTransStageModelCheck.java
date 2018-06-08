package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;

import pcal.AST;
import pcal.AST.*;
import pcal.AST.Process;
import pcal.PCalTLAGenerator;
import pcal.PcalTranslate;
import pcal.Region;
import pcal.TLAExpr;
import pcal.TLAToken;
import pcal.exception.RemoveNameConflictsException;
import pcal.exception.StringVectorToFileException;
import pgo.model.tla.PGoTLAExpression;
import pgo.model.tla.PGoTLAVariable;
import pgo.trans.PGoTransException;
import pgo.util.IOUtil;
import pgo.util.Pair;
import pgo.util.PcalASTUtil;

/**
 * Uses TLC to infer potentially useful invariants in the specification.
 * This stage modifies the data.ast object.
 *
 */
public class PGoTransStageModelCheck {

	PGoTransIntermediateData data;
	// The path to the generated TLA+ file to model check.
	private static final String TLA_PATH = "temp/";

	public PGoTransStageModelCheck(PGoTransStageTLAParse s) throws PGoTransException {
		this.data = s.data;
		// Remove naming conflicts, since the AST modifications rely on names.
		try {
			new PCalTLAGenerator(data.ast).removeNameConflicts();
		} catch (RemoveNameConflictsException e) {
			throw new PGoTransException("Error removing naming conflicts in model checking stage");
		}
		modifyAST();
		generateTLA();
	}

	/**
	 * Transforms the PlusCal AST as follows:
	 * - Adds the globals "pgo_read", "pgo_write"
	 * where pgo_read[var_name, label_name] represents the number of processes
	 * in the step label_name reading the variable var_name and correspondingly
	 * for pgo_write
	 * - In each labeled statement, fill the pgo_read and pgo_write variables
	 * with the correct information, and add a
	 * labeled statement after each labeled statement which resets the pgo_read
	 * and pgo_write variables.
	 * 
	 * @throws PGoTransException
	 */
	private void modifyAST() throws PGoTransException {
		new PcalASTUtil.Walker<Void>() {
			// The top of the stack is the sequence of LabeledStmts which we
			// will insert. The pair represents (statement, position in the
			// sequence).
			Stack<Vector<Pair<LabeledStmt, Integer>>> toFill;
			// The current index of the statement in the sequence of statements
			// we are walking.
			int pos;

			// Fill the sequence of LabeledStmts with the statements to be
			// inserted.
			private void recurse(Vector<AST> stmts) throws PGoTransException {
				toFill.push(new Vector<>());
				walk(stmts);
				Vector<Pair<LabeledStmt, Integer>> toInsert = toFill.pop();
				// for correct insertion position, fill in reverse order
				for (int i = toInsert.size() - 1; i >= 0; i--) {
					stmts.add(toInsert.get(i).second, toInsert.get(i).first);
				}
			}

			@Override
			protected void init() {
				toFill = new Stack<>();
				pos = 0;
			}

			// Maintain the pos variable correctly.
			@Override
			protected void walk(Vector<AST> ast) throws PGoTransException {
				if (ast == null || earlyTerm) {
					return;
				}
				for (int i = 0; i < ast.size(); i++) {
					pos = i;
					if (earlyTerm) {
						break;
					}
					walk(ast.get(i));
				}
			}

			// Helpers to generate AST nodes, since anonymous types cause issues
			// with the PCalTLAGenerator.
			private VarDecl makeVarDecl(String var, boolean isEq, TLAExpr val) {
				VarDecl ret = new VarDecl();
				ret.var = var;
				ret.isEq = isEq;
				ret.val = val;
				ret.setOrigin(new Region(0, 0, 1));
				return ret;
			}

			private SingleAssign makeSingleAssign(Lhs lhs, TLAExpr rhs) {
				SingleAssign ret = new SingleAssign();
				ret.lhs = lhs;
				ret.rhs = rhs;
				ret.setOrigin(new Region(0, 0, 1));
				return ret;
			}

			private Assign makeAssign(Vector<SingleAssign> ass) {
				Assign ret = new Assign();
				ret.ass = ass;
				ret.setOrigin(new Region(0, 0, 1));
				return ret;
			}

			private LabeledStmt makeLabeledStmt(String label, AST... asts) {
				LabeledStmt ret = new LabeledStmt();
				ret.label = label;
				ret.stmts = new Vector<>();
				for (AST ast : asts) {
					ret.stmts.add(ast);
				}
				ret.setOrigin(new Region(0, 0, 1));
				return ret;
			}

			@Override
			protected void visit(Uniprocess ua) throws PGoTransException {
				// add globals
				// cheat by adding a big super token
				String init = new StringBuilder()
						.append("[ << var, lab >> \\in ")
						.append(getVarNames())
						.append(" \\X ")
						.append(getLabNames())
						.append(" |-> 0 ]").toString();
				Vector<TLAToken> toks = new Vector<>();
				toks.add(new TLAToken(init, 0, 0, TLAToken.BUILTIN));
				Vector<Vector<TLAToken>> expr = new Vector<>();
				expr.add(toks);
				ua.decls.add(makeVarDecl("pgo_read", true, PcalTranslate.MakeExpr(expr)));
				ua.decls.add(makeVarDecl("pgo_write", true, PcalTranslate.MakeExpr(expr)));

				walk(ua.prcds);

				recurse(ua.body);
			}

			@Override
			protected void visit(Multiprocess ma) throws PGoTransException {
				// add globals
				// cheat by adding a big super token
				String init = new StringBuilder()
						.append("[ << var, lab >> \\in ")
						.append(getVarNames())
						.append(" \\X ")
						.append(getLabNames())
						.append(" |-> 0 ]").toString();
				Vector<TLAToken> toks = new Vector<>();
				toks.add(new TLAToken(init, 0, 0, TLAToken.BUILTIN));
				Vector<Vector<TLAToken>> expr = new Vector<>();
				expr.add(toks);
				ma.decls.add(makeVarDecl("pgo_read", true, PcalTranslate.MakeExpr(expr)));
				ma.decls.add(makeVarDecl("pgo_write", true, PcalTranslate.MakeExpr(expr)));

				super.visit(ma);
			}

			@Override
			protected void visit(Procedure p) throws PGoTransException {
				recurse(p.body);
			}

			@Override
			protected void visit(Process p) throws PGoTransException {
				recurse(p.body);
			}

			// Return a list of assignments for each variable name in vars of
			// the form
			// map[varname, label] := map[varname, label] modifier
			private Assign assignStmts(Set<String> vars, String map, String label, String modifier) {
				Vector<SingleAssign> ret = new Vector<>();
				for (String var : vars) {
					Lhs l = new Lhs();
					l.var = map;
					Vector<Vector<TLAToken>> sub = new Vector<>();
					sub.add(new Vector<>());
					sub.get(0).add(new TLAToken("[ \"" + var + "\", \"" + label + "\" ]", 0, 0, TLAToken.BUILTIN));
					l.sub = PcalTranslate.MakeExpr(sub);

					Vector<Vector<TLAToken>> r = new Vector<>();
					r.add(new Vector<>());
					r.get(0).add(new TLAToken(map + "[ \"" + var + "\", \"" + label + "\" ]" + modifier, 0, 0,
							TLAToken.BUILTIN));
					ret.add(makeSingleAssign(l, PcalTranslate.MakeExpr(r)));
				}
				return makeAssign(ret);
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				Set<String> read = findReadVars(ls), write = findWriteVars(ls);
				// variables written to are also "read"
				read.addAll(write);
				if (!read.isEmpty()) {
					// deal with unlab parts of the statement
					if (ls.stmts.get(0) instanceof LabelIf) {
						// need to put the statements inside the if, since
						// otherwise the AST is invalid
						LabelIf li = (LabelIf) ls.stmts.get(0);
						li.unlabThen.add(assignStmts(read, "pgo_read", ls.label, " + 1"));
						li.unlabThen.add(assignStmts(write, "pgo_write", ls.label, " + 1"));
						li.unlabElse.add(assignStmts(read, "pgo_read", ls.label, " + 1"));
						li.unlabElse.add(assignStmts(write, "pgo_write", ls.label, " + 1"));
						// add statements resetting state afterwards, since we
						// don't want to walk them
						recurse(ls.stmts);

						li.labThen.add(0, makeLabeledStmt(
								"pgo_" + ls.label + "_then",
								assignStmts(read, "pgo_read", ls.label, " - 1"),
								assignStmts(write, "pgo_write", ls.label, " - 1")));
						li.labElse.add(0, makeLabeledStmt(
								"pgo_ " + ls.label + "_else",
								assignStmts(read, "pgo_read", ls.label, " - 1"),
								assignStmts(write, "pgo_write", ls.label, " - 1")));
					} else if (ls.stmts.get(0) instanceof While) {
						While w = (While) ls.stmts.get(0);
						w.unlabDo.add(assignStmts(read, "pgo_read", ls.label, " + 1"));
						w.unlabDo.add(assignStmts(write, "pgo_write", ls.label, " + 1"));

						recurse(ls.stmts);

						w.labDo.add(0, makeLabeledStmt(
								"pgo_" + ls.label,
								assignStmts(read, "pgo_read", ls.label, " - 1"),
								assignStmts(write, "pgo_write", ls.label, " - 1")));
					} else if (ls.stmts.get(0) instanceof LabelEither) {
						LabelEither le = (LabelEither) ls.stmts.get(0);
						for (Clause c : (Vector<Clause>) le.clauses) {
							c.unlabOr.add(assignStmts(read, "pgo_read", ls.label, " + 1"));
							c.unlabOr.add(assignStmts(write, "pgo_write", ls.label, " + 1"));
						}

						recurse(ls.stmts);

						for (Clause c : (Vector<Clause>) le.clauses) {
							c.labOr.add(0, makeLabeledStmt(
									"pgo_" + ls.label,
									assignStmts(read, "pgo_read", ls.label, " - 1"),
									assignStmts(write, "pgo_write", ls.label, " - 1")));
						}
					} else {
						// normal; no labels inside ls.stmts

						// add statements to end of current statement
						ls.stmts.add(assignStmts(read, "pgo_read", ls.label, " + 1"));
						ls.stmts.add(assignStmts(write, "pgo_write", ls.label, " + 1"));

						// add new statements resetting the state
						toFill.peek().add(new Pair<>(
								makeLabeledStmt(
										"pgo_" + ls.label,
										assignStmts(read, "pgo_read", ls.label, " - 1"),
										assignStmts(write, "pgo_write", ls.label, " - 1")),
								pos + 1));
						recurse(ls.stmts);
					}
				} else {
					recurse(ls.stmts);
				}
			}

			// we dealt with the unlab parts when visiting the corresponding
			// LabeledStmt
			@Override
			protected void visit(LabelIf li) throws PGoTransException {
				recurse(li.labThen);
				recurse(li.labElse);
			}

			@Override
			protected void visit(Clause c) throws PGoTransException {
				recurse(c.labOr);
			}

			@Override
			protected void visit(While w) throws PGoTransException {
				recurse(w.labDo);
			}
		}.getResult(data.ast);
	}

	/**
	 * Generate the TLA+ file corresponding to the PlusCal AST.
	 * 
	 * @throws RemoveNameConflictsException
	 * @throws StringVectorToFileException
	 */
	private void generateTLA() throws PGoTransException {
		PCalTLAGenerator gen = new PCalTLAGenerator(data.ast);
		try {
			gen.removeNameConflicts();
			Vector<String> tla = gen.translate();
			IOUtil.WriteStringVectorToFile(tla, TLA_PATH + data.algName + ".tla");
		} catch (RemoveNameConflictsException e) {
			throw new PGoTransException("Error removing name conflicts when generating TLA+ in model check stage");
		} catch (StringVectorToFileException e) {
			throw new PGoTransException("Error writing TLA+ file in model check stage");
		}
	}

	/**
	 * @return the set of global variable names accessed in the statement
	 * @throws PGoTransException
	 */
	private Set<String> findReadVars(LabeledStmt ls) throws PGoTransException {
		PGoTLAExpression.Walker<Set<String>> findVars = new PGoTLAExpression.Walker<Set<String>>() {
			@Override
			public void init() {
				result = new HashSet<>();
			}

			@Override
			public Set<String> getResult(PGoTLAExpression ast) throws PGoTransException {
				return super.getResult(ast);
			}

			@Override
			protected void visit(PGoTLAVariable v) throws PGoTransException {
				if (data.globals.containsKey(v.getName())) {
					result.add(v.getName());
				}
				super.visit(v);
			}
		};

		return new PcalASTUtil.Walker<Set<String>>() {
			// whether we have visited the first labeled statement
			boolean vis;

			@Override
			protected void init() {
				result = new HashSet<>();
				vis = false;
			}

			protected void addExpr(TLAExpr expr) throws PGoTransException {
				result.addAll(findVars.getResult(data.findPGoTLA(expr)));
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				if (vis) {
					// reached a different statement
					earlyTerm = true;
				} else {
					vis = true;
					super.visit(ls);
				}
			}

			@Override
			protected void visit(While w) throws PGoTransException {
				addExpr(w.test);
				super.visit(w);
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				addExpr(sa.rhs);
				super.visit(sa);
			}

			@Override
			protected void visit(Lhs lhs) throws PGoTransException {
				addExpr(lhs.sub);
				super.visit(lhs);
			}

			@Override
			protected void visit(If i) throws PGoTransException {
				addExpr(i.test);
				super.visit(i);
			}

			@Override
			protected void visit(With w) throws PGoTransException {
				addExpr(w.exp);
				super.visit(w);
			}

			@Override
			protected void visit(When w) throws PGoTransException {
				addExpr(w.exp);
				super.visit(w);
			}

			@Override
			protected void visit(PrintS w) throws PGoTransException {
				addExpr(w.exp);
				super.visit(w);
			}

			@Override
			protected void visit(Assert w) throws PGoTransException {
				addExpr(w.exp);
				super.visit(w);
			}

			// only walk the unlab parts
			@Override
			protected void visit(LabelIf li) throws PGoTransException {
				addExpr(li.test);
				walk(li.unlabThen);
				walk(li.unlabElse);
			}

			@Override
			protected void visit(Clause c) throws PGoTransException {
				walk(c.unlabOr);
			}

			@Override
			protected void visit(Call c) throws PGoTransException {
				for (TLAExpr expr : (Vector<TLAExpr>) c.args) {
					addExpr(expr);
				}
				super.visit(c);
			}

			@Override
			protected void visit(CallReturn cr) throws PGoTransException {
				for (TLAExpr expr : (Vector<TLAExpr>) cr.args) {
					addExpr(expr);
				}
				super.visit(cr);
			}
		}.getResult(ls);
	}

	private Set<String> findWriteVars(LabeledStmt ls) throws PGoTransException {
		return new PcalASTUtil.Walker<Set<String>>() {
			boolean vis;

			@Override
			protected void init() {
				result = new HashSet<>();
				vis = false;
			}

			@Override
			protected void visit(SingleAssign sa) throws PGoTransException {
				if (data.globals.containsKey(sa.lhs.var)) {
					result.add(sa.lhs.var);
				}
				super.visit(sa);
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				if (vis) {
					// reached a different statement
					earlyTerm = true;
				} else {
					vis = true;
					super.visit(ls);
				}
			}

			// only walk the unlab parts
			@Override
			protected void visit(LabelIf li) throws PGoTransException {
				walk(li.unlabThen);
				walk(li.unlabElse);
			}

			@Override
			protected void visit(Clause c) throws PGoTransException {
				walk(c.unlabOr);
			}
		}.getResult(ls);
	}

	/**
	 * @return the string representation of the PlusCal set of all global
	 *         variable names
	 * @throws PGoTransException
	 */
	private String getVarNames() throws PGoTransException {
		List<String> vars = new PcalASTUtil.Walker<List<String>>() {
			@Override
			protected void init() {
				result = new ArrayList<>();
			}

			@Override
			protected void visit(VarDecl v) throws PGoTransException {
				result.add("\"" + v.var + "\"");
				super.visit(v);
			}
		}.getResult(data.ast);
		return "{" + String.join(", ", vars) + "}";
	}

	/**
	 * @return the string representation of the PlusCal set of all label names
	 * @throws PGoTransException
	 */
	private String getLabNames() throws PGoTransException {
		List<String> labs = new PcalASTUtil.Walker<List<String>>() {
			@Override
			protected void init() {
				result = new ArrayList<>();
			}

			@Override
			protected void visit(LabeledStmt ls) throws PGoTransException {
				result.add("\"" + ls.label + "\"");
				super.visit(ls);
			}
		}.getResult(data.ast);
		return "{" + String.join(", ", labs) + "}";
	}
}
