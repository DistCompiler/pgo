package pgo.model.tla;

import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.golang.SimpleExpression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * Base TLA Expression representation
 *
 */
public abstract class PGoTLAExpression {

	// the line number
	private int line;

	public PGoTLAExpression(int line) {
		this.line = line;
	}

	public int getLine() {
		return line;
	}

	// A class representing a blank expression (equivalent to
	// "defaultInitValue" in PlusCal).
	public static final class PGoTLADefault extends PGoTLAExpression {
		public PGoTLADefault(int line) {
			super(line);
		}

		@Override
		protected Expression convert(TLAExprToGo trans) throws PGoTransException {
			return new SimpleExpression(new Vector<>());
		}

		@Override
		protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
			return trans.type(this);
		}
	}

	/**
	 * Convert the TLA expression into its GoAST representation using the
	 * translator passed in.
	 * 
	 * @throws PGoTransException
	 *             if there is a type contradiction
	 */
	protected abstract Expression convert(TLAExprToGo trans) throws PGoTransException;

	/**
	 * Infer the type of the TLA expression using the translator passed in.
	 * 
	 * @throws PGoTransException
	 *             if there is a type contradiction
	 */
	protected abstract PGoType inferType(TLAExprToType trans) throws PGoTransException;

	/**
	 * Walks the TLA AST, similarly to the PcalASTUtil.Walker. Override visit()
	 * methods for special functionality.
	 */
	public static abstract class Walker<T> {
		// whether to terminate early
		protected boolean earlyTerm = false;
		protected T result;

		public Walker() {
			init();
		}

		protected abstract void init();

		public T getResult(PGoTLAExpression ast) throws PGoTransException {
			return walk(ast);
		}

		protected T walk(PGoTLAExpression ast) throws PGoTransException {
			if (ast == null || earlyTerm) {
				return null;
			}
			if (ast instanceof PGoTLAArray) {
				return visit((PGoTLAArray) ast);
			} else if (ast instanceof PGoTLABool) {
				return visit((PGoTLABool) ast);
			} else if (ast instanceof PGoTLABoolOp) {
				return visit((PGoTLABoolOp) ast);
			} else if (ast instanceof PGoTLAFunctionCall) {
				return visit((PGoTLAFunctionCall) ast);
			} else if (ast instanceof PGoTLAGroup) {
				return visit((PGoTLAGroup) ast);
			} else if (ast instanceof PGoTLANumber) {
				return visit((PGoTLANumber) ast);
			} else if (ast instanceof PGoTLASequence) {
				return visit((PGoTLASequence) ast);
			} else if (ast instanceof PGoTLASet) {
				return visit((PGoTLASet) ast);
			} else if (ast instanceof PGoTLASetOp) {
				return visit((PGoTLASetOp) ast);
			} else if (ast instanceof PGoTLASimpleArithmetic) {
				return visit((PGoTLASimpleArithmetic) ast);
			} else if (ast instanceof PGoTLAString) {
				return visit((PGoTLAString) ast);
			} else if (ast instanceof PGoTLAUnary) {
				return visit((PGoTLAUnary) ast);
			} else if (ast instanceof PGoTLAVariable) {
				return visit((PGoTLAVariable) ast);
			} else if (ast instanceof PGoTLAVariadic) {
				return visit((PGoTLAVariadic) ast);
			} else {
				assert false;
				return null;
			}
		}

		protected T visit(PGoTLAArray a) throws PGoTransException {
			for (PGoTLAExpression tla : a.getContents()) {
				walk(tla);
			}
			return null;
		}

		protected T visit(PGoTLABool b) throws PGoTransException {
			return null;
		}

		protected T visit(PGoTLABoolOp bo) throws PGoTransException {
			walk(bo.getLeft());
			walk(bo.getRight());
			return null;
		}

		protected T visit(PGoTLAFunctionCall fc) throws PGoTransException {
			for (PGoTLAExpression tla : fc.getParams()) {
				walk(tla);
			}
			return null;
		}

		protected T visit(PGoTLAGroup g) throws PGoTransException {
			walk(g.getInner());
			return null;
		}

		protected T visit(PGoTLANumber num) throws PGoTransException {
			return null;
		}

		protected T visit(PGoTLASequence seq) throws PGoTransException {
			walk(seq.getStart());
			walk(seq.getEnd());
			return null;
		}

		protected T visit(PGoTLASet set) throws PGoTransException {
			for (PGoTLAExpression tla : set.getContents()) {
				walk(tla);
			}
			return null;
		}

		protected T visit(PGoTLASetOp so) throws PGoTransException {
			walk(so.getLeft());
			walk(so.getRight());
			return null;
		}

		protected T visit(PGoTLASimpleArithmetic sa) throws PGoTransException {
			walk(sa.getLeft());
			walk(sa.getRight());
			return null;
		}

		protected T visit(PGoTLAString s) throws PGoTransException {
			return null;
		}

		protected T visit(PGoTLAUnary u) throws PGoTransException {
			walk(u.getArg());
			return null;
		}

		protected T visit(PGoTLAVariable v) throws PGoTransException {
			return null;
		}

		protected T visit(PGoTLAVariadic v) throws PGoTransException {
			walk(v.getExpr());
			for (PGoTLAExpression tla : v.getArgs()) {
				walk(tla);
			}
			return null;
		}
	}
}
