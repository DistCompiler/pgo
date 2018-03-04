package pgo.model.tla;

import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * Represents a TLA operator which can take multiple comma-separated arguments
 * on one side: the such-that operator ":", which the maps-to operator "|->",
 * and the EXCEPT operator. The such-that operator is used with set
 * constructor/image notation and with predicate operations. The sets are on the
 * right side if this is a set image, and on the left otherwise. The maps-to
 * operator can take several sets on the left side, and the EXCEPT operator can
 * take several assignments on the right side.
 *
 */
public class PGoTLAVariadic extends PGoTLAExpression {
	private String tok;
	// the multi-argument side
	private Vector<PGoTLAExpression> multiArgs;
	// the expression on the other side
	private PGoTLAExpression expr;
	// true if the multi-argument side is the right one
	private boolean rightSide;

	public PGoTLAVariadic(String token, Vector<PGoTLAExpression> left, Vector<TLAToken> right, int line)
			throws PGoTransException {
		super(line);
		multiArgs = new Vector<>();
		Vector<PGoTLAExpression> r = new TLAExprParser(right, line).getResult();
		this.tok = token;
		
		switch (tok) {
		case ":":
			// If both sides are set ops, the left side is defined to be the
			// "set" side. The only legal set ops (for direct children of this
			// node) are "\in" and "\notin"
			// The side with the sets has >1 elt, or the "\in" set op
			if (r.size() > 1 || r.get(0) instanceof PGoTLASetOp) {
				rightSide = ((PGoTLASetOp) r.get(0)).getToken().equals("\\in");
			} else {
				rightSide = false;
			}

			if (rightSide) {
				for (PGoTLAExpression tla : r) {
					assert (tla instanceof PGoTLASetOp);
					assert ((PGoTLASetOp) tla).getToken().equals("\\in");
				}
				multiArgs = r;
				assert (left.size() == 1);
				expr = left.get(0);
			} else {
				for (PGoTLAExpression tla : left) {
					assert (tla instanceof PGoTLASetOp);
					assert ((PGoTLASetOp) tla).getToken().equals("\\in");
				}
				multiArgs = left;
				assert (r.size() == 1);
				expr = r.get(0);
			}
			break;
		case "|->":
			rightSide = false;
			this.multiArgs = left;
			assert (r.size() == 1);
			this.expr = r.get(0);
			break;
		case "EXCEPT":
			rightSide = true;
			this.multiArgs = r;
			assert (left.size() == 1);
			this.expr = left.get(0);
			break;
		default:
			assert false;
		}
	}
	
	public String getToken() {
		return tok;
	}

	public Vector<PGoTLAExpression> getArgs() {
		return multiArgs;
	}

	public PGoTLAExpression getExpr() {
		return expr;
	}

	public boolean isRightSide() {
		return rightSide;
	}

	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}

	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLAVariadic) not implemented");
	}

}
