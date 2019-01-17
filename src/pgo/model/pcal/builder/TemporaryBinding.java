package pgo.model.pcal.builder;

import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLAIdentifier;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.util.SourceLocation;

import java.util.*;

public class TemporaryBinding {
	private NameCleaner nameCleaner;
	private Map<UID, TLAGeneralIdentifier> temporaries;
	private List<PlusCalVariableDeclaration> declarations;
	private Set<UID> reusables;

	public TemporaryBinding(NameCleaner nameCleaner, List<PlusCalVariableDeclaration> declarations) {
		this.nameCleaner = nameCleaner;
		this.temporaries = new HashMap<>();
		this.declarations = declarations;
		this.reusables = new HashSet<>();
	}

	public TLAGeneralIdentifier freshVariable(SourceLocation location, UID varUID, String nameHint) {
		String uniqueName = nameCleaner.cleanName(nameHint);
		TLAGeneralIdentifier variableReference = new TLAGeneralIdentifier(
				location,
				new TLAIdentifier(location, uniqueName),
				Collections.emptyList());
		temporaries.put(varUID, variableReference);
		return variableReference;
	}

	public TLAGeneralIdentifier declare(SourceLocation location, UID varUID, String nameHint) {
		if (reusables.contains(varUID) && temporaries.containsKey(varUID)) {
			reusables.remove(varUID);
			return temporaries.get(varUID);
		} else {
			TLAGeneralIdentifier fresh = freshVariable(location, varUID, nameHint);
			PlusCalVariableDeclaration declaration = new PlusCalVariableDeclaration(
					location,
					new Located<>(location, fresh.getName().getId()),
					false,
					false,
					new PlusCalDefaultInitValue(location));
			declarations.add(declaration);
			return fresh;
		}
	}

	public Optional<TLAGeneralIdentifier> lookup(UID varUID) {
		return Optional.ofNullable(temporaries.get(varUID));
	}

	public void reuse(UID varUID) {
		if (temporaries.containsKey(varUID)) {
			reusables.add(varUID);
		}
	}
}
