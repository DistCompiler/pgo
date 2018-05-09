package pgo.util;

import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import pcal.AST;
import pcal.AST.*;
import pcal.AST.Process;
import pgo.PGoException;
import pgo.model.pcal.Algorithm;
import pgo.trans.PGoTransException;

/**
 * Utils package for PlusCal AST traversal and manipulation
 *
 */
public class PcalASTUtil {
	
	public static <T> T accept(AST a, Visitor<T> v) throws PGoException {
		if (a instanceof Uniprocess) {
			Uniprocess ua = (Uniprocess) a;
			return v.visit(ua);
		} else if (a instanceof Multiprocess) {
			Multiprocess ma = (Multiprocess) a;
			return v.visit(ma);
		} else if (a instanceof Procedure) {
			Procedure p = (Procedure) a;
			return v.visit(p);
		} else if (a instanceof Process) {
			Process p = (Process) a;
			return v.visit(p);
		} else if (a instanceof VarDecl) {
			return v.visit((VarDecl) a);
		} else if (a instanceof PVarDecl) {
			return v.visit((PVarDecl) a);
		} else if (a instanceof LabeledStmt) {
			LabeledStmt ls = (LabeledStmt) a;
			return v.visit(ls);
		} else if (a instanceof While) {
			While w = (While) a;
			return v.visit(w);
		} else if (a instanceof Assign) {
			Assign as = (Assign) a;
			return v.visit(as);
		} else if (a instanceof SingleAssign) {
			SingleAssign sa = (SingleAssign) a;
			return v.visit(sa);
		} else if (a instanceof Lhs) {
			return v.visit((Lhs) a);
		} else if (a instanceof If) {
			If ifast = (If) a;
			return v.visit(ifast);
		} else if (a instanceof Either) {
			Either ei = (Either) a;
			return v.visit(ei);
		} else if (a instanceof With) {
			With with = (With) a;
			return v.visit(with);
		} else if (a instanceof When) {
			return v.visit((When) a);
		} else if (a instanceof PrintS) {
			return v.visit((PrintS) a);
		} else if (a instanceof Assert) {
			return v.visit((Assert) a);
		} else if (a instanceof Skip) {
			return v.visit((Skip) a);
		} else if (a instanceof LabelIf) {
			LabelIf lif = (LabelIf) a;
			return v.visit(lif);
		} else if (a instanceof LabelEither) {
			LabelEither le = (LabelEither) a;
			return v.visit(le);
		} else if (a instanceof Clause) {
			Clause c = (Clause) a;
			return v.visit(c);
		} else if (a instanceof Call) {
			return v.visit((Call) a);
		} else if (a instanceof Return) {
			return v.visit((Return) a);
		} else if (a instanceof CallReturn) {
			return v.visit((CallReturn) a);
		} else if (a instanceof Goto) {
			return v.visit((Goto) a);
		} else if (a instanceof Macro) {
			Macro m = (Macro) a;
			return v.visit(m);
		} else if (a instanceof MacroCall) {
			return v.visit((MacroCall) a);
		}
		throw new RuntimeException("Encountered unrecognised PlusCal AST node "+a);
	}

	/**
	 * Class that can be passed to walk(AST, Visitor<T>) in order to process arbitrary AST nodes.
	 *
	 * T is the result type
	 * 
	 */
	public static abstract class Visitor<T> {
		// =================================================
		// The below are functions to visit each individual AST node type
		// The argument to visit is guaranteed to not be null.

		public abstract T visit(Uniprocess ua) throws PGoException;
		public abstract T visit(Multiprocess ma) throws PGoException;
		public abstract T visit(Procedure p) throws PGoException;
		public abstract T visit(Process p) throws PGoException;
		public abstract T visit(PVarDecl a) throws PGoException;
		public abstract T visit(VarDecl a) throws PGoException;
		public abstract T visit(LabeledStmt ls) throws PGoException;
		public abstract T visit(While w) throws PGoException;
		public abstract T visit(Assign as) throws PGoException;
		public abstract T visit(SingleAssign sa) throws PGoException;
		public abstract T visit(Lhs lhs) throws PGoException;
		public abstract T visit(If ifast) throws PGoException;
		public abstract T visit(Either ei) throws PGoException;
		public abstract T visit(With with) throws PGoException;
		public abstract T visit(When when) throws PGoException;
		public abstract T visit(PrintS ps) throws PGoException;
		public abstract T visit(Assert as) throws PGoException;
		public abstract T visit(Skip s) throws PGoException;
		public abstract T visit(LabelIf lif) throws PGoException;
		public abstract T visit(LabelEither le) throws PGoException;
		public abstract T visit(Clause c) throws PGoException;
		public abstract T visit(Call c) throws PGoException;
		public abstract T visit(Return r) throws PGoException;
		public abstract T visit(CallReturn cr) throws PGoException;
		public abstract T visit(Goto g) throws PGoException;
		public abstract T visit(Macro m) throws PGoException;
		public abstract T visit(MacroCall m) throws PGoException;

	}
	
	public static Algorithm convertTLCASTtoPGoAST(AST a) throws PGoException {
		TLCToPGoPCalASTConversionVisitor v = new TLCToPGoPCalASTConversionVisitor();
		accept(a, v);
		if(v.getResult() == null) {
			throw new RuntimeException("Error converting TLC PlusCal AST, no process block found?");
		}
		return v.getResult();
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
