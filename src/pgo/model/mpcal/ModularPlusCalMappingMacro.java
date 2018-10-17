package pgo.model.mpcal;

import pgo.model.pcal.PlusCalStatement;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 * Modular PlusCal mapping macro node
 *
 * mapping macro MappingMacro {
 *     read {
 *         readBody;
 *     }
 *     write {
 *         writeBody;
 *     }
 * }
 */
public class ModularPlusCalMappingMacro extends ModularPlusCalUnit {
	private final String name;
	private final List<PlusCalStatement> readBody;
	private final List<PlusCalStatement> writeBody;
	private final UID specialVariableValueUID;

	public ModularPlusCalMappingMacro(SourceLocation location, String name, List<PlusCalStatement> readBody,
	                                  List<PlusCalStatement> writeBody) {
		super(location);
		this.name = name;
		this.readBody = readBody;
		this.writeBody = writeBody;
		this.specialVariableValueUID = new UID();
		this.specialVariableValueUID.addOrigin(this);
	}

	@Override
	public ModularPlusCalMappingMacro copy() {
		return new ModularPlusCalMappingMacro(
				getLocation(),
				name,
				readBody.stream().map(PlusCalStatement::copy).collect(Collectors.toList()),
				writeBody.stream().map(PlusCalStatement::copy).collect(Collectors.toList()));
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, readBody, writeBody);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || obj.getClass() != getClass()) {
			return false;
		}
		ModularPlusCalMappingMacro that = (ModularPlusCalMappingMacro) obj;
		return name.equals(that.name) &&
				Objects.equals(readBody, that.readBody) &&
				Objects.equals(writeBody, that.writeBody);
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public <T, E extends Throwable> T accept(ModularPlusCalBlockVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public String getName() {
		return name;
	}

	public List<PlusCalStatement> getReadBody() {
		return Collections.unmodifiableList(readBody);
	}

	public List<PlusCalStatement> getWriteBody() {
		return Collections.unmodifiableList(writeBody);
	}

	public UID getSpecialVariableValueUID() {
		return specialVariableValueUID;
	}
}
