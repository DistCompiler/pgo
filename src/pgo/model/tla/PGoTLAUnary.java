package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * This represents a TLA+ unary operator call.
 * 
 */
public class PGoTLAUnary extends PGoTLAExpression {
	private String operation;
	private PGoTLAExpression operand;
	private List<PGoTLAGeneralIdentifierPart> prefix;

	public PGoTLAUnary(SourceLocation location, String operation, List<PGoTLAGeneralIdentifierPart> prefix, PGoTLAExpression operand) {
		super(location);
		this.operation = operation;
		this.prefix = prefix;
		this.operand = operand;
	}
	
	@Override
	public PGoTLAUnary copy() {
		return new PGoTLAUnary(getLocation(), operation, prefix.stream().map(PGoTLAGeneralIdentifierPart::copy).collect(Collectors.toList()), operand.copy());
	}

	public String getOperation() {
		return operation;
	}

	public PGoTLAExpression getOperand() {
		return operand;
	}
	
	public List<PGoTLAGeneralIdentifierPart> getPrefix(){
		return prefix;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAExpressionVisitor<T, E> v) throws E {
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
		PGoTLAUnary other = (PGoTLAUnary) obj;
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
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		return true;
	}
	
}
