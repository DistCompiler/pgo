package pgo.model.tla;

import java.util.ArrayList;
import java.util.List;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;
import pgo.trans.PGoTransException;

/**
 * Represents a TLA unary operator (negation, element union, or powerset) or a
 * predicate operation (CHOOSE, for all, exists)
 * 
 * ## Note:
 * 
 * With TLAParser, this will only ever be an actual TLA+ unary operator.
 * 
 */
public class PGoTLAUnary extends PGoTLAExpression {
	private String token;
	// The expression the operator operates on
	private PGoTLAExpression arg;
	private List<PGoTLAGeneralIdentifierPart> prefix;

	public PGoTLAUnary(String tok, List<PGoTLAGeneralIdentifierPart> prefix, PGoTLAExpression arg, int line) {
		super(line);
		this.token = tok;
		this.arg = arg;
		this.prefix = prefix;
	}
	
	@Deprecated
	public PGoTLAUnary(String tok, PGoTLAExpression arg, int line) {
		super(line);
		this.token = tok;
		this.arg = arg;
		this.prefix = new ArrayList<>();
	}

	public String getToken() {
		return token;
	}

	public PGoTLAExpression getArg() {
		return arg;
	}

	protected Expression convert(TLAExprToGo trans) throws PGoTransException {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) throws PGoTransException {
		return trans.type(this);
	}

	public String toString() {
		return "PGoTLAUnary (" + this.getLine() + "): " + token + " " + arg.toString();
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((arg == null) ? 0 : arg.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
		result = prime * result + ((token == null) ? 0 : token.hashCode());
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
		PGoTLAUnary other = (PGoTLAUnary) obj;
		if (arg == null) {
			if (other.arg != null)
				return false;
		} else if (!arg.equals(other.arg))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		if (token == null) {
			if (other.token != null)
				return false;
		} else if (!token.equals(other.token))
			return false;
		return true;
	}
}
