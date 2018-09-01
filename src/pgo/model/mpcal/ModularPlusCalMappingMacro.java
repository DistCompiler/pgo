package pgo.model.mpcal;

import pgo.TODO;
import pgo.model.pcal.PlusCalStatement;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.util.Collections;
import java.util.List;

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
public class ModularPlusCalMappingMacro extends ModularPlusCalNode {
	private Located<String> name;
	private List<PlusCalStatement> readBody;
	private List<PlusCalStatement> writeBody;

	public ModularPlusCalMappingMacro(SourceLocation location, Located<String> name, List<PlusCalStatement> readBody, List<PlusCalStatement> writeBody) {
		super(location);
		this.name = name;
		this.readBody = readBody;
		this.writeBody = writeBody;
	}

	@Override
	public ModularPlusCalNode copy() {
		throw new TODO();
	}

	@Override
	public int hashCode() {
		throw new TODO();
	}

	@Override
	public boolean equals(Object obj) {
		throw new TODO();
	}

	@Override
	public <T, E extends Throwable> T accept(ModularPlusCalNodeVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	public Located<String> getName() {
		return name;
	}

	public List<PlusCalStatement> getReadBody() {
		return Collections.unmodifiableList(readBody);
	}

	public List<PlusCalStatement> getWriteBody() {
		return Collections.unmodifiableList(writeBody);
	}
}
