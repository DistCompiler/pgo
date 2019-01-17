package pgo.trans.passes.codegen;

import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLAIdentifier;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.util.SourceLocation;

import java.util.*;

public class TemporaryBinding {
	private NameCleaner nameCleaner;
	private Map<UID, Recycling<TLAGeneralIdentifier>> temporaries;
	private List<PlusCalVariableDeclaration> declarations;

	public TemporaryBinding(NameCleaner nameCleaner, List<PlusCalVariableDeclaration> declarations) {
		this.nameCleaner = nameCleaner;
		this.temporaries = new HashMap<>();
		this.declarations = declarations;
	}

	public TLAGeneralIdentifier freshVariable(SourceLocation location, UID varUID, String nameHint) {
		String uniqueName = nameCleaner.cleanName(nameHint);
		TLAGeneralIdentifier variableReference = new TLAGeneralIdentifier(
				location,
				new TLAIdentifier(location, uniqueName),
				Collections.emptyList());
		if (temporaries.containsKey(varUID)) {
			temporaries.get(varUID).add(variableReference);
		} else {
			temporaries.put(varUID, new Recycling<>(variableReference));
		}
		return variableReference;
	}

	private TLAGeneralIdentifier declareHelper(SourceLocation location, UID varUID, String nameHint,
	                                           TLAExpression value) {
		TLAGeneralIdentifier fresh = freshVariable(location, varUID, nameHint);
		PlusCalVariableDeclaration declaration = new PlusCalVariableDeclaration(
				location, new Located<>(location, fresh.getName().getId()), false, false, value);
		declarations.add(declaration);
		return fresh;
	}

	public TLAGeneralIdentifier declare(SourceLocation location, UID varUID, String nameHint, TLAExpression value) {
		if (temporaries.containsKey(varUID)) {
			Optional<TLAGeneralIdentifier> recycled = temporaries.get(varUID).use();
			if (recycled.isPresent()) {
				return recycled.get();
			}
			TLAGeneralIdentifier fresh = declareHelper(location, varUID, nameHint, value);
			temporaries.get(varUID).add(fresh);
			return fresh;
		} else {
			TLAGeneralIdentifier fresh = declareHelper(location, varUID, nameHint, value);
			temporaries.put(varUID, new Recycling<>(fresh));
			return fresh;
		}
	}

	public TLAGeneralIdentifier declare(SourceLocation location, UID varUID, String nameHint) {
		return declare(location, varUID, nameHint, new PlusCalDefaultInitValue(location));
	}

	public Optional<TLAGeneralIdentifier> lookup(UID varUID) {
		return Optional.ofNullable(temporaries.get(varUID)).flatMap(Recycling::fetch);
	}

	public void reuse(UID varUID) {
		if (temporaries.containsKey(varUID)) {
			temporaries.get(varUID).reuse();
		}
	}
}
