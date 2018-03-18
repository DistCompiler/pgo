package pgo.model.tla;

import java.util.List;
import java.util.Vector;

import pcal.TLAToken;
import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.parser.TLAExprParser;
import pgo.trans.PGoTransException;

/**
 * Represents a set "{ ... }" in TLA. This should store what is in the set, and
 * the set notations for the set.
 * 
 * ## Note
 * 
 * With TLAParser, this will always be the result of parsing an explicit set constructor:
 * 
 * { <expr>, <expr>, ... }
 *
 */
public class PGoTLASet extends PGoTLAExpression {

	private Vector<PGoTLAExpression> contents;

	public PGoTLASet(Vector<TLAToken> between, int line) throws PGoTransException {
		super(line);
		contents = new TLAExprParser(between, line).getResult();
	}
	
	public PGoTLASet(List<PGoTLAExpression> contents, int line) {
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
		String ret = "PGoTLASet (" + this.getLine() + "): {";
		for (PGoTLAExpression p : contents) {
			ret += "(" + p.toString() + "), ";
		}
		return ret + "}";
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}
}
