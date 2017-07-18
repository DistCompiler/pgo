package pcal;

/**
 * A wrapper class for the PlusCal tools TLAExpr class. Contains equals() and
 * hashCode() methods so that these can be used as map keys.
 *
 */
public class TLAExprPgo extends TLAExpr {
	public TLAExprPgo(TLAExpr t) {
		this.tokens = t.tokens;
	}

	@Override
	public boolean equals(Object other) {
		if (other == null || !(other instanceof TLAExprPgo)) {
			return false;
		}
		if (other == this) {
			return true;
		}
		TLAExprPgo t = (TLAExprPgo) other;
		return this.toString().equals(t.toString());
	}

	@Override
	public int hashCode() {
		return this.toString().hashCode();
	}
}
