package pgo.model.type;

import pgo.util.Origin;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Represents a map.
 */
public class PGoTypeMap extends PGoType {
	private PGoType keyType;
	private PGoType valueType;

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
	public boolean containsVariables() {
		return keyType.containsVariables() || valueType.containsVariables();
	}

	@Override
	public PGoType substitute(Map<PGoTypeVariable, PGoType> mapping) {
		keyType = keyType.substitute(mapping);
		valueType = valueType.substitute(mapping);
		return this;
	}

	@Override
	public String toTypeName() {
		return "Map[" + keyType.toTypeName() + "]" + valueType.toTypeName();
	}

	@Override
	public PGoType copy() {
		return new PGoTypeMap(keyType.copy(), valueType.copy(), getOrigins());
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTypeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

}
