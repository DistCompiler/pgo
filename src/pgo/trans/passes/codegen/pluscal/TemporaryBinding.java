package pgo.trans.passes.codegen.pluscal;

import pgo.InternalCompilerError;
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
	public static class Checkpoint {
		private final TemporaryBinding from;
		private final Map<UID, Recycling.Checkpoint<TLAGeneralIdentifier>> checkpoints;

		private Checkpoint(TemporaryBinding from, Map<UID, Recycling<TLAGeneralIdentifier>> temporaries) {
			this.from = from;
			this.checkpoints = new HashMap<>();
			temporaries.forEach((k, v) -> this.checkpoints.put(k, v.checkpoint()));
		}
	}

	private final NameCleaner nameCleaner;
	private final Map<UID, Recycling<TLAGeneralIdentifier>> temporaries;
	private final List<PlusCalVariableDeclaration> declarations;
	private ArrayDeque<LinkedHashMap<UID, TLAGeneralIdentifier>> touchedVarsStack;
	private LinkedHashMap<UID, TLAGeneralIdentifier> touchedVars;

	public TemporaryBinding(NameCleaner nameCleaner, List<PlusCalVariableDeclaration> declarations) {
		this.nameCleaner = nameCleaner;
		this.temporaries = new HashMap<>();
		this.declarations = declarations;
		this.touchedVarsStack = new ArrayDeque<>();
		this.touchedVarsStack.push(new LinkedHashMap<>());
		this.touchedVars = touchedVarsStack.peek();
	}

	public Checkpoint checkpoint() {
		return new Checkpoint(this, temporaries);
	}

	public void restore(Checkpoint checkpoint) {
		if (checkpoint.from != this) {
			throw new InternalCompilerError();
		}
		temporaries.forEach((k, v) -> {
			if (checkpoint.checkpoints.containsKey(k)) {
				v.restore(checkpoint.checkpoints.get(k));
			} else {
				v.reuse();
			}
		});
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
		TLAGeneralIdentifier fresh = freshVariable(location, varUID, nameHint);
		PlusCalVariableDeclaration declaration = new PlusCalVariableDeclaration(
				location, new Located<>(location, fresh.getName().getId()), false, false, value);
		declarations.add(declaration);
		if (touchedVarsStack.size() > 1) {
			touchedVars.put(varUID, fresh);
		}
		return fresh;
	}

	public TLAGeneralIdentifier forceDeclare(SourceLocation location, UID varUID, String nameHint) {
		return forceDeclare(location, varUID, nameHint, new PlusCalDefaultInitValue(location));
	}

	public TLAGeneralIdentifier declare(SourceLocation location, UID varUID, String nameHint, TLAExpression value) {
		if (temporaries.containsKey(varUID)) {
			Optional<TLAGeneralIdentifier> optionalResult = temporaries.get(varUID).use();
			if (optionalResult.isPresent()) {
				if (touchedVarsStack.size() > 1) {
					touchedVars.put(varUID, optionalResult.get());
				}
				return optionalResult.get();
			}
			return forceDeclare(location, varUID, nameHint, value);
		}
		return forceDeclare(location, varUID, nameHint, value);
	}

	public TLAGeneralIdentifier declare(SourceLocation location, UID varUID, String nameHint) {
		return declare(location, varUID, nameHint, new PlusCalDefaultInitValue(location));
	}

	public Optional<TLAGeneralIdentifier> lookup(UID varUID) {
		return Optional.ofNullable(temporaries.get(varUID)).flatMap(Recycling::fetch);
	}

	public void reuseAll() {
		for (Recycling<TLAGeneralIdentifier> value : temporaries.values()) {
			value.reuse();
		}
	}

	public void reuse(UID varUID) {
		if (temporaries.containsKey(varUID)) {
			temporaries.get(varUID).reuse();
		}
		// once a variable is reused, it should not be reported back
		touchedVars.remove(varUID);
	}

	public LinkedHashMap<UID, TLAGeneralIdentifier> startRecording() {
		touchedVars = new LinkedHashMap<>();
		touchedVarsStack.push(touchedVars);
		return touchedVars;
	}

	public void stopRecording() {
		touchedVarsStack.pop();
		touchedVars = touchedVarsStack.peek();
	}
}
