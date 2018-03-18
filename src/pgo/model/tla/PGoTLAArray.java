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
}
