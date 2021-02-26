package pgo.model.pcal;

import pgo.model.mpcal.ModularPlusCalBlockVisitor;
import pgo.model.tla.TLAIdentifier;
import pgo.util.SourceLocation;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class PlusCalMacro extends PlusCalNode {
	private final String name;
	private final List<TLAIdentifier> params;
	private final List<PlusCalStatement> body;

	public PlusCalMacro(SourceLocation location, String name, List<TLAIdentifier> params, List<PlusCalStatement> body) {
		super(location);
		this.name = name;
		this.params = params;
		this.body = body;
	}

	@Override
	public PlusCalMacro copy() {
		return new PlusCalMacro(
				getLocation(),
				name,
				new ArrayList<>(params),
				body.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	public String getName() {
		return name;
	}

	public List<TLAIdentifier> getParams() {
		return params;
	}

	public List<String> getParamIds(){
		return params.stream()
				.map(TLAIdentifier::getId)
				.collect(Collectors.toList());
	}

	public List<PlusCalStatement> getBody(){
		return body;
	}

	@Override
	public <T, E extends Throwable> T accept(PlusCalNodeVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	public <T, E extends Throwable> T accept(ModularPlusCalBlockVisitor<T, E> v) throws E{
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((body == null) ? 0 : body.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((params == null) ? 0 : params.hashCode());
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
		PlusCalMacro other = (PlusCalMacro) obj;
		if (body == null) {
			if (other.body != null)
				return false;
		} else if (!body.equals(other.body))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (params == null) {
			return other.params == null;
		} else return params.equals(other.params);
	}

}
