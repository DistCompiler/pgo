package pgo.model.mpcal;

import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class ModularPlusCalBlock extends ModularPlusCalNode {
	private Located<String> name;
	private List<ModularPlusCalMappingMacro> mappingMacros;
	private List<ModularPlusCalArchetype> archetypes;

	public ModularPlusCalBlock(SourceLocation location, Located<String> name,
	                           List<ModularPlusCalMappingMacro> mappingMacros,
	                           List<ModularPlusCalArchetype> archetypes) {
		super(location);
		this.name = name;
		this.mappingMacros = mappingMacros;
		this.archetypes = archetypes;
	}

	@Override
	public ModularPlusCalBlock copy() {
		return new ModularPlusCalBlock(
				getLocation(),
				name,
				mappingMacros.stream().map(ModularPlusCalMappingMacro::copy).collect(Collectors.toList()),
				archetypes.stream().map(ModularPlusCalArchetype::copy).collect(Collectors.toList()));
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, mappingMacros, archetypes);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		ModularPlusCalBlock that = (ModularPlusCalBlock) obj;
		return name.getValue().equals(that.name.getValue()) &&
				Objects.equals(mappingMacros, that.mappingMacros) &&
				Objects.equals(archetypes, that.archetypes);
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Located<String> getName() {
		return name;
	}

	public List<ModularPlusCalMappingMacro> getMappingMacros() {
		return Collections.unmodifiableList(mappingMacros);
	}

	public List<ModularPlusCalArchetype> getArchetypes() {
		return Collections.unmodifiableList(archetypes);
	}
}
