package pgo.util;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

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
import pcal.AST.Lhs;
import pcal.AST.Macro;
import pcal.AST.MacroCall;
import pcal.AST.Multiprocess;
import pcal.AST.PVarDecl;
import pcal.AST.PrintS;
import pcal.AST.Procedure;
import pcal.AST.Process;
import pcal.AST.Return;
import pcal.AST.SingleAssign;
import pcal.AST.Skip;
import pcal.AST.Uniprocess;
import pcal.AST.VarDecl;
import pcal.AST.When;
import pcal.AST.While;
import pcal.AST.With;
import pgo.trans.PGoTransException;

/**
 * Utils package for PlusCal AST traversal and manipulation
 *
 */
public class PcalASTUtil {

	/**
	 * Class for arbitrary traversal through the entire AST
	 * 
	 * We can override any visit function to add special functionality at that
	 * specific node, or stop traversing at that node. Can then use super at any
	 * point to resume normal traversal after any special operations.
	 * 
	 * The ast to visit is guaranteed to never to null.
	 * 
	 * We can also override walk function to deal with any generic AST node
	 *
	 * T is the result type
	 * 
	 */
	public static abstract class Walker<T> {

		// the result storage
		protected T result;

		// whether to stop traversing
		protected boolean earlyTerm;

		protected abstract void init();

		public T getResult(Vector<AST> body) throws PGoTransException {
			walk(body);
			return result;
		}

		public T getResult(AST body) throws PGoTransException {
			walk(body);
			return result;
		}

		public Walker() {
			init();
		}

		/**
		 * Walks the ast
		 * 
		 * @param ast
		 */
		protected void walk(Vector<AST> ast) throws PGoTransException {
			if (ast == null || earlyTerm) {
				return;
			}
			for (AST a : ast) {
				if (earlyTerm) {
					break;
				}
				walk(a);
			}
		}

		protected void walk(AST a) throws PGoTransException {
			if (a == null || earlyTerm) {
				return;
			}

			if (a instanceof Uniprocess) {
				Uniprocess ua = (Uniprocess) a;
				visit(ua);
			} else if (a instanceof Multiprocess) {
				Multiprocess ma = (Multiprocess) a;
				visit(ma);
			} else if (a instanceof Procedure) {
				Procedure p = (Procedure) a;
				visit(p);
			} else if (a instanceof Process) {
				Process p = (Process) a;
				visit(p);
			} else if (a instanceof VarDecl) {
				visit((VarDecl) a);
			} else if (a instanceof PVarDecl) {
				visit((PVarDecl) a);
			} else if (a instanceof LabeledStmt) {
				LabeledStmt ls = (LabeledStmt) a;
				visit(ls);
			} else if (a instanceof While) {
				While w = (While) a;
				visit(w);
			} else if (a instanceof Assign) {
				Assign as = (Assign) a;
				visit(as);
			} else if (a instanceof SingleAssign) {
				SingleAssign sa = (SingleAssign) a;
				visit(sa);
			} else if (a instanceof Lhs) {
				visit((Lhs) a);
			} else if (a instanceof If) {
				If ifast = (If) a;
				visit(ifast);
			} else if (a instanceof Either) {
				Either ei = (Either) a;
				visit(ei);
			} else if (a instanceof With) {
				With with = (With) a;
				visit(with);
			} else if (a instanceof When) {
				visit((When) a);
			} else if (a instanceof PrintS) {
				visit((PrintS) a);
			} else if (a instanceof Assert) {
				visit((Assert) a);
			} else if (a instanceof Skip) {
				visit((Skip) a);
			} else if (a instanceof LabelIf) {
				LabelIf lif = (LabelIf) a;
				visit(lif);
			} else if (a instanceof LabelEither) {
				LabelEither le = (LabelEither) a;
				visit(le);
			} else if (a instanceof Clause) {
				Clause c = (Clause) a;
				visit(c);
			} else if (a instanceof Call) {
				visit((Call) a);
			} else if (a instanceof Return) {
				visit((Return) a);
			} else if (a instanceof CallReturn) {
				visit((CallReturn) a);
			} else if (a instanceof Goto) {
				visit((Goto) a);
			} else if (a instanceof Macro) {
				Macro m = (Macro) a;
				visit(m);
			} else if (a instanceof MacroCall) {
				visit((MacroCall) a);
			}
		}

		// =================================================
		// The below are functions to visit each individual AST node type
		// Override any of them to perform special operations at that node.
		// The argument to visit is guaranteed to not be null.

		protected void visit(Uniprocess ua) throws PGoTransException {
			walk(ua.body);
			walk(ua.decls);
			walk(ua.macros);
			walk(ua.prcds);
		}

		protected void visit(Multiprocess ma) throws PGoTransException {
			walk(ma.decls);
			walk(ma.macros);
			walk(ma.prcds);
			walk(ma.procs);
		}

		protected void visit(Procedure p) throws PGoTransException {
			walk(p.body);
			walk(p.decls);
			walk(p.params);
		}

		protected void visit(Process p) throws PGoTransException {
			walk(p.body);
			walk(p.decls);
		}

		protected void visit(PVarDecl a) throws PGoTransException {

		}

		protected void visit(VarDecl a) throws PGoTransException {

		}

		protected void visit(LabeledStmt ls) throws PGoTransException {
			walk(ls.stmts);
		}

		protected void visit(While w) throws PGoTransException {
			walk(w.unlabDo);
			walk(w.labDo);
		}

		protected void visit(Assign as) throws PGoTransException {
			walk(as.ass);
		}

		protected void visit(SingleAssign sa) throws PGoTransException {
			walk(sa.lhs);
		}

		protected void visit(Lhs lhs) throws PGoTransException {

		}

		protected void visit(If ifast) throws PGoTransException {
			walk(ifast.Then);
			walk(ifast.Else);
		}

		protected void visit(Either ei) throws PGoTransException {
			for (Vector v : (Vector<Vector>) ei.ors) {
				// either has vector of vectors
				walk(v);
			}
		}

		protected void visit(With with) throws PGoTransException {
			walk(with.Do);
		}

		protected void visit(When when) throws PGoTransException {

		}

		protected void visit(PrintS ps) throws PGoTransException {

		}

		protected void visit(Assert as) throws PGoTransException {

		}

		protected void visit(Skip s) throws PGoTransException {

		}

		protected void visit(LabelIf lif) throws PGoTransException {

			walk(lif.unlabThen);
			walk(lif.labThen);
			walk(lif.unlabElse);
			walk(lif.labElse);
		}

		protected void visit(LabelEither le) throws PGoTransException {
			walk(le.clauses);
		}

		protected void visit(Clause c) throws PGoTransException {
			walk(c.unlabOr);
			walk(c.labOr);
		}

		protected void visit(Call c) throws PGoTransException {

		}

		protected void visit(Return r) throws PGoTransException {

		}

		protected void visit(CallReturn cr) throws PGoTransException {

		}

		protected void visit(Goto g) throws PGoTransException {

		}

		protected void visit(Macro m) throws PGoTransException {
			walk(m.body);
		}

		protected void visit(MacroCall m) throws PGoTransException {

		}

	}

	/**
	 * Determines whether the given body of code contains an assignment
	 * operation to the variable of name
	 * 
	 * @param body
	 * @param name
	 * @return
	 */
	public static boolean containsAssignmentToVar(Vector<AST> body, String name) {
		Walker<Boolean> av = new Walker<Boolean>() {

			@Override
			protected void init() {
				result = false;
			}

			@Override
			public void visit(Lhs lhs) {
				if (lhs.var.equals(name)) {
					result = true;
					earlyTerm = true;
				}
			}

		};

		try {
			return av.getResult(body);
		} catch (PGoTransException e) {
			assert (false); // shouldn't throw
		}
		return false;
	}

	/**
	 * Finds all the function calls (procedure and macro calls) made in body of
	 * code
	 * 
	 * @param newBodies
	 * @return
	 */
	public static Vector<String> collectFunctionCalls(Vector<AST> body) {
		Walker<Vector<String>> av = new Walker<Vector<String>>() {

			@Override
			protected void init() {
				result = new Vector<String>();
			}

			@Override
			public void visit(Call call) {
				result.add(call.to);
			}

			@Override
			public void visit(CallReturn call) {
				result.add(call.to);
			}

			@Override
			public void visit(MacroCall mc) {
				// TODO pluscal actually already expanded the macro. we need to
				// handle it before this is useful. Right now, this will never
				// be reached as MacroCalls are replaced with the actual code
				result.add(mc.name);
			}
		};

		try {
			return av.getResult(body);
		} catch (PGoTransException e) {
			assert (false);
		}
		return null;
	}

	/**
	 * Finds all the labels that are used in goto statements.
	 */
	public static Set<String> collectUsedLabels(Vector<AST> body) {
		Walker<Set<String>> av = new Walker<Set<String>>() {

			@Override
			protected void init() {
				result = new HashSet<>();
			}

			@Override
			protected void visit(Goto g) {
				result.add(g.to);
			}

		};

		try {
			return av.getResult(body);
		} catch (PGoTransException e) {
			assert false;
		}
		return null;
	}
}
