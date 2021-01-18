package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

/**
 * 
 * This represents a TLA+ unary operator call.
 * 
 */
public class TLAUnary extends TLAExpression {
	private final TLASymbol operation;
	private final TLAExpression operand;
	private final List<TLAGeneralIdentifierPart> prefix;
	private TLADefinitionOne refersTo;

	public TLAUnary(SourceLocation location, TLASymbol operation, List<TLAGeneralIdentifierPart> prefix, TLAExpression operand) {
		super(location);
		this.operation = operation;
		this.prefix = prefix;
		this.operand = operand;
	}

	public void setRefersTo(TLADefinitionOne refersTo) {
		this.refersTo = refersTo;
	}

	public TLADefinitionOne getRefersTo() {
		return refersTo;
	}
	
	@Override
	public TLAUnary copy() {
		return new TLAUnary(getLocation(), operation, prefix.stream().map(TLAGeneralIdentifierPart::copy).collect(Collectors.toList()), operand.copy());
	}

	public TLASymbol getOperation() {
		return operation;
	}

	public TLAExpression getOperand() {
		return operand;
	}
	
	public List<TLAGeneralIdentifierPart> getPrefix(){
		return prefix;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAExpressionVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((operand == null) ? 0 : operand.hashCode());
		result = prime * result + ((operation == null) ? 0 : operation.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
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
		TLAUnary other = (TLAUnary) obj;
		if (operand == null) {
			if (other.operand != null)
				return false;
		} else if (!operand.equals(other.operand))
			return false;
		if (operation == null) {
			if (other.operation != null)
				return false;
		} else if (!operation.equals(other.operation))
			return false;
		if (prefix == null) {
			return other.prefix == null;
		} else return prefix.equals(other.prefix);
	}
	
}
