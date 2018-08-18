package pgo.model.tla;

import pgo.util.SourceLocation;

import java.util.List;
import java.util.stream.Collectors;

public class TLAModuleDefinition extends TLAUnit {
	
	private TLAIdentifier name;
	private List<TLAOpDecl> args;
	private TLAInstance instance;
	private boolean local;

	public TLAModuleDefinition(SourceLocation location, TLAIdentifier name, List<TLAOpDecl> args, TLAInstance instance, boolean isLocal) {
		super(location);
		this.name = name;
		this.args = args;
		this.instance = instance;
		this.local = isLocal;
	}
	
	@Override
	public TLAModuleDefinition copy() {
		return new TLAModuleDefinition(getLocation(), name.copy(), args.stream().map(TLAOpDecl::copy).collect(Collectors.toList()), instance.copy(), local);
	}

	public TLAIdentifier getName() {
		return name;
	}
	
	public List<TLAOpDecl> getArgs(){
		return args;
	}

	public TLAInstance getInstance() {
		return instance;
	}
	
	public boolean isLocal() {
		return local;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((args == null) ? 0 : args.hashCode());
		result = prime * result + ((instance == null) ? 0 : instance.hashCode());
		result = prime * result + (local ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
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
		TLAModuleDefinition other = (TLAModuleDefinition) obj;
		if (args == null) {
			if (other.args != null)
				return false;
		} else if (!args.equals(other.args))
			return false;
		if (instance == null) {
			if (other.instance != null)
				return false;
		} else if (!instance.equals(other.instance))
			return false;
		if (local != other.local)
			return false;
		if (name == null) {
			return other.name == null;
		} else return name.equals(other.name);
	}

}
