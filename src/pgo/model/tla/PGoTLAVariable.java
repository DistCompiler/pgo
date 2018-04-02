package pgo.model.tla;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pgo.model.golang.Expression;
import pgo.model.intermediate.PGoType;

/**
 * Variable access in TLA Expr
 *
 */
public class PGoTLAVariable extends PGoTLAExpression {

	private String name;
	private List<PGoTLAGeneralIdentifierPart> prefix;

	public PGoTLAVariable(String n, List<PGoTLAGeneralIdentifierPart> prefix, int line) {
		super(line);
		name = n;
		this.prefix = prefix;
	}
	
	@Deprecated
	public PGoTLAVariable(String n, int line) {
		super(line);
		name = n;
		this.prefix = new ArrayList<>();
	}

	public String getName() {
		return name;
	}
	
	public List<PGoTLAGeneralIdentifierPart> getGeneralIdentifierPrefix(){
		return prefix;
	}
	
	protected Expression convert(TLAExprToGo trans) {
		return trans.translate(this);
	}
	
	protected PGoType inferType(TLAExprToType trans) {
		return trans.type(this);
	}
	
	public String toString() {
		return "PGoTLAVar (" + this.getLine() + "): " + name;
	}
	
	@Override
	public <Result> Result walk(PGoTLAExpressionVisitor<Result> v) {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		PGoTLAVariable other = (PGoTLAVariable) obj;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		return true;
	}
	
}
