package pgo.model.type;

import pgo.errors.IssueContext;
import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Represents a map.
 */
public class PGoTypeMap extends PGoType {
	private PGoType keyType;
	private PGoType valueType;

	public PGoTypeMap(PGoType keyType, PGoType valueType, Origin... origins) {
		this(keyType, valueType, Arrays.asList(origins));
	}

	public PGoTypeMap(PGoType keyType, PGoType valueType, List<Origin> origins) {
		super(origins);
		this.keyType = keyType;
		this.valueType = valueType;
	}

	public PGoType getKeyType() {
		return keyType;
	}

	public PGoType getValueType() {
		return valueType;
	}

	@Override
	public boolean equals(Object p) {
		if (!(p instanceof PGoTypeMap)) {
			return false;
		}
		PGoTypeMap other = (PGoTypeMap) p;
		return keyType.equals(other.keyType) && valueType.equals(other.valueType);
	}

	@Override
	public boolean contains(PGoTypeVariable v) {
		return keyType.contains(v) || valueType.contains(v);
	}

	@Override
	public boolean containsVariables() {
		return keyType.containsVariables() || valueType.containsVariables();
	}

	@Override
	public void collectVariables(Set<PGoTypeVariable> vars) {
		keyType.collectVariables(vars);
		valueType.collectVariables(vars);
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		keyType = keyType.substitute(mapping);
		valueType = valueType.substitute(mapping);
		return this;
	}

	@Override
	public PGoType realize(IssueContext ctx) {
		keyType = keyType.realize(ctx);
		valueType = valueType.realize(ctx);
		return this;
	}

	@Override
	public String toTypeName() {
		return "Map[" + keyType.toTypeName() + "]" + valueType.toTypeName();
	}
	
	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public String toGo() {
		return "datatypes.Map";
	}
}
