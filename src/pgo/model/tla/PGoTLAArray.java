package pgo.model.tla;

import java.util.List;
import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * An array "[ ... ]" or tuple "<< ... >>" declared in TLA. These contain the
 * contents of the array.
 *
 */
public class PGoTLAArray extends PGoTLAExpression {

	private Vector<PGoTLAExpression> contents;

	public PGoTLAArray(Vector<TLAToken> between, int line) throws PGoTransException {
		super(line);
		contents = new TLAExprParser(between, line).getResult();
	}
	
	public PGoTLAArray(List<PGoTLAExpression> contents, int line) {
		super(line);
		this.contents = new Vector<>();
		this.contents.addAll(contents);
	}

	public Vector<PGoTLAExpression> getContents() {
		return contents;
	}

	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}

	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	public String toString() {
		String ret = "PGoTLAArray (" + this.getLine() + "): [";
		for (PGoTLAExpression p : contents) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + "]";
	}

	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLAArray) not implemented");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((contents == null) ? 0 : contents.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLAArray other = (PGoTLAArray) obj;
		if (contents == null) {
			if (other.contents != null)
				return false;
		} else if (!contents.equals(other.contents))
			return false;
		return true;
	}
	
}
