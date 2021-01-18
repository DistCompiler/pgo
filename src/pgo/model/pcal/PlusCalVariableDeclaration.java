package pgo.model.pcal;

import pgo.model.tla.TLADefinitionOne;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAIdentifier;
import pgo.util.SourceLocation;
import scala.collection.immutable.Map;
import scala.collection.immutable.Map$;

public class PlusCalVariableDeclaration extends PlusCalNode implements TLADefinitionOne {
	private final TLAIdentifier name;
	private final boolean isRef;
	private final boolean set;
	private final TLAExpression value;

	public PlusCalVariableDeclaration(SourceLocation location, TLAIdentifier name, boolean isRef, boolean isSet, TLAExpression value) {
		super(location);
		this.name = name;
		this.isRef = isRef;
		this.set = isSet;
		this.value = value;
	}

	@Override
	public int arity() {
		return 0;
	}

	@Override
	public boolean isModuleInstance() {
		return false;
	}

	@Override
	public TLAIdentifier identifier() {
		return name;
	}

	@Override
	public Map<TLAIdentifier, TLADefinitionOne> scope() {
		return Map$.MODULE$.empty();
	}

	@Override
	public PlusCalVariableDeclaration copy() {
		throw new RuntimeException("bad");
		//return new PlusCalVariableDeclaration(getLocation(), name, isRef, set, value.copy());
	}

	public TLAIdentifier getName() {
		return name;
	}

	public boolean isRef() {
		return isRef;
	}

	public boolean isSet() {
		return set;
	}

	public TLAExpression getValue(){
		return value;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (set ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((value == null) ? 0 : value.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		PlusCalVariableDeclaration that = (PlusCalVariableDeclaration) obj;
		return set == that.set &&
				((name == null && that.name == null) ||
						(name != null && name.equals(that.name))) &&
				((value == null && that.value != null) ||
						(value != null && value.equals(that.value)));
	}
}
