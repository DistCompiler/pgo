package pgo.model.tla;

import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Statement;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * Represents the "such that" operator ":". This is used with the set
 * constructor/image notation, and also with predicate operations. Multiple
 * variables \in sets can be declared, in the case of set image, exists, and
 * forall.
 *
 */
public class PGoTLASuchThat extends PGoTLA {
	// the var \in set declarations
	private Vector<PGoTLASetOp> sets;
	// the expression on the other side: either a predicate (in the case of
	// predicate ops and set constructor) or a function (for set image).
	private PGoTLA expr;
	// true if this is a set image: then the sets are on the rhs
	private boolean isSetImage;

	public PGoTLASuchThat(Vector<PGoTLA> left, Vector<TLAToken> right, int line) throws PGoTransException {
		// If both sides are set ops, it doesn't matter which one we pick to be
		// the "set" side so we arbitrarily choose the left one. The only legal
		// set ops (for direct children of this node) are "\in" and "\notin"
		super(line);
		sets = new Vector<>();
		Vector<PGoTLA> r = new TLAExprParser(right, line).getResult();
		// The side with the sets has >1 elt, or the "\in" set op
		if (r.size() > 1 || r.get(0) instanceof PGoTLASetOp) {
			isSetImage = ((PGoTLASetOp) r.get(0)).getToken().equals("\\in");
		} else {
			isSetImage = false;
		}

		if (isSetImage) {
			for (PGoTLA tla : r) {
				assert (tla instanceof PGoTLASetOp);
				assert ((PGoTLASetOp) tla).getToken().equals("\\in");
				sets.add((PGoTLASetOp) tla);
			}
			assert (left.size() == 1);
			expr = left.get(0);
		} else {
			for (PGoTLA tla : left) {
				assert (tla instanceof PGoTLASetOp);
				assert ((PGoTLASetOp) tla).getToken().equals("\\in");
				sets.add((PGoTLASetOp) tla);
			}
			assert (r.size() == 1);
			expr = r.get(0);
		}
	}

	public Vector<PGoTLASetOp> getSets() {
		return sets;
	}

	public PGoTLA getExpr() {
		return expr;
	}

	public boolean isSetImage() {
		return isSetImage;
	}

	protected Vector<Statement> convert(TLAExprToGo trans) {
		return trans.translate(this);
	}

	/*
	 * This returns the contained type in the context of a set (i.e. the type of
	 * the outer set in set constructor, or the return type of the function in
	 * set image).
	 */
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

}
