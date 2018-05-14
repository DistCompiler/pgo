package pgo.model.tla;

import java.util.List;
import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.type.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * An array "[ ... ]" or tuple "<< ... >>" declared in TLA. These contain the
 * contents of the array.
 *
 */
public class PGoTLAArray extends PGoTLAExpression {

	private List<PGoTLAExpression> contents;

	public PGoTLAArray(Vector<TLAToken> between, int line) throws PGoTransException {
		super(line);
		contents = new TLAExprParser(between, line).getResult();
	}
	
	public PGoTLAArray(List<PGoTLAExpression> contents, int line) {
		super(line);
		this.contents = new Vector<>();
		this.contents.addAll(contents);
	}

	public List<PGoTLAExpression> getContents() {
		return contents;
	}

	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}

	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	public String toString() {
		StringBuilder ret = new StringBuilder("PGoTLAArray (").append(this.getLine()).append("): [");
		for (PGoTLAExpression p : contents) {
			ret.append("(").append(p.toString()).append("), ");
		}
		return ret.append("]").toString();
	}

	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		throw new RuntimeException("walk(PGoTLAArray) not implemented");
	}
}
