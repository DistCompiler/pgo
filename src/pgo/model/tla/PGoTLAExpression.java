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

	public abstract <Result> Result walk(PGoTLAExpressionVisitor<Result> v);

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

		@Override
		public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
			return v.visit(this);
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
			init();
			walk(ast);
			return result;
		}

		protected void walk(PGoTLAExpression ast) throws PGoTransException {
			if (ast == null || earlyTerm) {
				return;
			}
			if (ast instanceof PGoTLAArray) {
				visit((PGoTLAArray) ast);
			} else if (ast instanceof PGoTLABool) {
				visit((PGoTLABool) ast);
			} else if (ast instanceof PGoTLABoolOp) {
				visit((PGoTLABoolOp) ast);
			} else if (ast instanceof PGoTLAFunctionCall) {
				visit((PGoTLAFunctionCall) ast);
			} else if (ast instanceof PGoTLAGroup) {
				visit((PGoTLAGroup) ast);
			} else if (ast instanceof PGoTLANumber) {
				visit((PGoTLANumber) ast);
			} else if (ast instanceof PGoTLASequence) {
				visit((PGoTLASequence) ast);
			} else if (ast instanceof PGoTLASet) {
				visit((PGoTLASet) ast);
			} else if (ast instanceof PGoTLASetOp) {
				visit((PGoTLASetOp) ast);
			} else if (ast instanceof PGoTLASimpleArithmetic) {
				visit((PGoTLASimpleArithmetic) ast);
			} else if (ast instanceof PGoTLAString) {
				visit((PGoTLAString) ast);
			} else if (ast instanceof PGoTLAUnary) {
				visit((PGoTLAUnary) ast);
			} else if (ast instanceof PGoTLAVariable) {
				visit((PGoTLAVariable) ast);
			} else if (ast instanceof PGoTLAVariadic) {
				visit((PGoTLAVariadic) ast);
			} else if (ast instanceof PGoTLADefault) {
				visit((PGoTLADefault) ast);
			} else {
				assert false;
			}
		}

		protected void visit(PGoTLAArray a) throws PGoTransException {
			for (PGoTLAExpression tla : a.getContents()) {
				walk(tla);
			}
		}

		protected void visit(PGoTLABool b) throws PGoTransException {
		}

		protected void visit(PGoTLABoolOp bo) throws PGoTransException {
			walk(bo.getLeft());
			walk(bo.getRight());
		}

		protected void visit(PGoTLAFunctionCall fc) throws PGoTransException {
			for (PGoTLAExpression tla : fc.getParams()) {
				walk(tla);
			}
		}

		protected void visit(PGoTLAGroup g) throws PGoTransException {
			walk(g.getInner());
		}

		protected void visit(PGoTLANumber num) throws PGoTransException {
		}

		protected void visit(PGoTLASequence seq) throws PGoTransException {
			walk(seq.getStart());
			walk(seq.getEnd());
		}

		protected void visit(PGoTLASet set) throws PGoTransException {
			for (PGoTLAExpression tla : set.getContents()) {
				walk(tla);
			}
		}

		protected void visit(PGoTLASetOp so) throws PGoTransException {
			walk(so.getLeft());
			walk(so.getRight());
		}

		protected void visit(PGoTLASimpleArithmetic sa) throws PGoTransException {
			walk(sa.getLeft());
			walk(sa.getRight());
		}

		protected void visit(PGoTLAString s) throws PGoTransException {
		}

		protected void visit(PGoTLAUnary u) throws PGoTransException {
			walk(u.getArg());
		}

		protected void visit(PGoTLAVariable v) throws PGoTransException {
		}

		protected void visit(PGoTLAVariadic v) throws PGoTransException {
			walk(v.getExpr());
			for (PGoTLAExpression tla : v.getArgs()) {
				walk(tla);
			}
		}

		private void visit(PGoTLADefault ast) {
		}
	}
}
