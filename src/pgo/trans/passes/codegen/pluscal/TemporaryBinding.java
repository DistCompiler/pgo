package pgo.trans.passes.codegen.pluscal;

import pgo.model.pcal.PlusCalVariableDeclaration;
import pgo.model.tla.PlusCalDefaultInitValue;
import pgo.model.tla.TLAExpression;
import pgo.model.tla.TLAGeneralIdentifier;
import pgo.model.tla.TLAIdentifier;
import pgo.parser.Located;
import pgo.scope.UID;
import pgo.trans.passes.codegen.NameCleaner;
import pgo.trans.passes.codegen.Recycling;
import pgo.util.SourceLocation;

import java.util.*;

public class TemporaryBinding {
	private final NameCleaner nameCleaner;
	private final Map<UID, Recycling<TLAGeneralIdentifier>> temporaries;
	private final List<PlusCalVariableDeclaration> declarations;
	private Set<UID> touchedVars;
	private boolean recording;

	public TemporaryBinding(NameCleaner nameCleaner, List<PlusCalVariableDeclaration> declarations) {
		this.nameCleaner = nameCleaner;
		this.temporaries = new HashMap<>();
		this.declarations = declarations;
		this.touchedVars = new LinkedHashSet<>();
		this.recording = false;
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

	public TLAGeneralIdentifier forceDeclare(SourceLocation location, UID varUID, String nameHint,
	                                         TLAExpression value) {
		if (recording) {
			touchedVars.add(varUID);
		}
		TLAGeneralIdentifier fresh = freshVariable(location, varUID, nameHint);
		PlusCalVariableDeclaration declaration = new PlusCalVariableDeclaration(
				location, new Located<>(location, fresh.getName().getId()), false, false, value);
		declarations.add(declaration);
		return fresh;
	}

	public TLAGeneralIdentifier forceDeclare(SourceLocation location, UID varUID, String nameHint) {
		return forceDeclare(location, varUID, nameHint, new PlusCalDefaultInitValue(location));
	}

	public TLAGeneralIdentifier declare(SourceLocation location, UID varUID, String nameHint, TLAExpression value) {
		if (recording) {
			touchedVars.add(varUID);
		}
		if (temporaries.containsKey(varUID)) {
			return temporaries.get(varUID).use().orElseGet(() -> forceDeclare(location, varUID, nameHint, value));
		}
		return forceDeclare(location, varUID, nameHint, value);
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

	public void startRecording() {
		touchedVars = new LinkedHashSet<>();
		recording = true;
	}

	public Set<UID> stopRecording() {
		Set<UID> result = touchedVars;
		touchedVars = new LinkedHashSet<>();
		recording = false;
		return result;
	}
}
