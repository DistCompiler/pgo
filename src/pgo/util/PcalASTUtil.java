package pgo.util;

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

		// whether to terminate early
		protected boolean earlyTerm = false;
		protected T result;

		public T getResult(Vector<AST> ast) {
			walk(ast);
			return result;
		}

		public Walker() {
			init();
		}

		protected abstract void init();

		public T getResult(AST ast) {
			walk(ast);
			return result;
		}

		/**
		 * Walks the ast
		 * 
		 * @param ast
		 */
		protected void walk(Vector<AST> ast) {
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

		protected void walk(AST a) {
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

		protected void visit(Uniprocess ua) {
			walk(ua.body);
			walk(ua.decls);
			walk(ua.macros);
			walk(ua.prcds);
		}

		protected void visit(Multiprocess ma) {
			walk(ma.decls);
			walk(ma.macros);
			walk(ma.prcds);
			walk(ma.procs);
		}

		protected void visit(Procedure p) {
			walk(p.body);
			walk(p.decls);
			walk(p.params);
		}

		protected void visit(Process p) {
			walk(p.body);
			walk(p.decls);
		}

		protected void visit(PVarDecl a) {

		}

		protected void visit(VarDecl a) {

		}

		protected void visit(LabeledStmt ls) {
			walk(ls.stmts);
		}

		protected void visit(While w) {
			walk(w.unlabDo);
			walk(w.labDo);
		}

		protected void visit(Assign as) {
			walk(as.ass);
		}
		
		protected void visit(SingleAssign sa) {
			walk(sa.lhs);
		}

		protected void visit(Lhs lhs) {

		}

		protected void visit(If ifast) {
			walk(ifast.Then);
			walk(ifast.Else);
		}

		protected void visit(Either ei) {
			walk(ei.ors);
		}

		protected void visit(With with) {
			walk(with.Do);
		}

		protected void visit(When when) {

		}

		protected void visit(PrintS ps) {

		}

		protected void visit(Assert as) {

		}

		protected void visit(Skip s) {

		}

		protected void visit(LabelIf lif) {
			walk(lif.unlabElse);
			walk(lif.unlabThen);
			walk(lif.labElse);
			walk(lif.labThen);
		}

		protected void visit(LabelEither le) {
			walk(le.clauses);
		}

		protected void visit(Clause c) {
			walk(c.unlabOr);
			walk(c.labOr);
		}

		protected void visit(Call c) {

		}

		protected void visit(Return r) {

		}

		protected void visit(CallReturn cr) {

		}

		protected void visit(Goto g) {

		}

		protected void visit(Macro m) {
			walk(m.body);
		}

		protected void visit(MacroCall m) {

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
		
		return av.getResult(body);
	}

}
