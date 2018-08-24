package pgo.trans.passes.tlagen;

import pgo.InternalCompilerError;
import pgo.model.pcal.PlusCalAssignmentPair;
import pgo.model.pcal.PlusCalLHS;
import pgo.model.pcal.PlusCalLHSPart;
import pgo.model.tla.*;
import pgo.model.tla.builder.TLAConjunctBuilder;
import pgo.model.tla.builder.TLAOperatorBuilder;
import pgo.scope.UID;
import pgo.trans.intermediate.DefinitionRegistry;
import pgo.util.SourceLocation;

import java.util.*;
import java.util.stream.Collectors;

public class TranslationContext {

	public interface WriteMacro {
		void perform(TLAConjunctBuilder builder, TranslationContext translationContext, TLAExpression value);
	}

	public interface ReadMacro {
		TLAExpression perform(TLAConjunctBuilder builder, TranslationContext translationContext);
	}

	private final TLAExpression pcLHS;
	private final DefinitionRegistry definitionRegistry;
	private final List<String> labelOperatorArguments;
	private final List<UID> allVariables;
	private final List<UID> unchangedVariables;
	private final Map<UID, String> renamingMap;
	private final Map<UID, TLAExpression> variableReadAccessors;
	private final Map<UID, ReadMacro> readMacros;
	private final Map<UID, WriteMacro> writeMacros;

	public TranslationContext(TLAExpression pcLHS, DefinitionRegistry definitionRegistry,
							  List<String> labelOperatorArguments, List<UID> allVariables,
							  List<UID> unchangedVariables, Map<UID, String> renamingMap,
							  Map<UID, TLAExpression> variableReadAccessors, Map<UID, ReadMacro> readMacros,
							  Map<UID, WriteMacro> writeMacros) {
		this.pcLHS = pcLHS;
		this.definitionRegistry = definitionRegistry;
		this.labelOperatorArguments = labelOperatorArguments;
		this.allVariables = allVariables;
		this.unchangedVariables = unchangedVariables;
		this.renamingMap = renamingMap;
		this.variableReadAccessors = variableReadAccessors;
		this.readMacros = readMacros;
		this.writeMacros = writeMacros;
	}

	public TLAExpression getPCLHS() {
		return pcLHS;
	}

	public TranslationContext getLabelTranslationContext() {
		return new TranslationContext(pcLHS, definitionRegistry, labelOperatorArguments, allVariables,
				new ArrayList<>(allVariables), renamingMap, new HashMap<>(), readMacros, writeMacros);
	}

	public TranslationContext getChild() {
		return new TranslationContext(pcLHS, definitionRegistry, labelOperatorArguments, allVariables,
				new ArrayList<>(unchangedVariables), renamingMap, new HashMap<>(variableReadAccessors),
				readMacros, writeMacros);
	}

	public TLAExpression getRelativeUNCHANGED(TranslationContext lChild) {
		List<UID> relativeUnchanged = new ArrayList<>();
		for(UID v : unchangedVariables) {
			if(!lChild.unchangedVariables.contains(v)){
				relativeUnchanged.add(v);
			}
		}
		return getUNCHANGED(relativeUnchanged);
	}

	private TLAExpression getUNCHANGED(List<UID> vars) {
		return new TLAUnary(
				SourceLocation.unknown(),
				new TLASymbol(SourceLocation.unknown(), "UNCHANGED"),
				Collections.emptyList(),
				new TLATuple(
						SourceLocation.unknown(),
						vars
								.stream()
								.map(renamingMap::get)
								.map(name -> new TLAGeneralIdentifier(
										SourceLocation.unknown(),
										new TLAIdentifier(SourceLocation.unknown(), name),
										Collections.emptyList()))
								.collect(Collectors.toList())));
	}

	public TLAExpression getUNCHANGED() {
		return getUNCHANGED(unchangedVariables);
	}

	public void mergeUNCHANGED(TranslationContext other) {
		// ensure that we have the minimum unchanged variables between the two sets
		unchangedVariables.removeIf(v -> !other.unchangedVariables.contains(v));
	}

	public PlusCalStatementTranslationVisitor.PrevStatementType buildVariableWrite(TLAConjunctBuilder builder,
																				   PlusCalAssignmentPair pair,
																				   PlusCalStatementTranslationVisitor.PrevStatementType prevStatementType,
																				   PlusCalStatementTranslationVisitor.Continuation continuation) {
		if(prevStatementType.requiresLabel()) throw new InternalCompilerError();

		PlusCalLHS lhs = pair.getLhs();
		UID ref = definitionRegistry.followReference(lhs.getUID());

		TLAExpression value = pair.getRhs();
		// we compile a.b["c"] := d to a' = [a EXCEPT !.b["c] = d]
		if(!lhs.getParts().isEmpty()) {
			List<TLASubstitutionKey> keys = new ArrayList<>();
			for (PlusCalLHSPart part : lhs.getParts()) {
				switch(part.getType()){
					case INDEX:
						keys.add(new TLASubstitutionKey(SourceLocation.unknown(), part.getArguments()));
						break;
					case DOT:
						keys.add(new TLASubstitutionKey(
								SourceLocation.unknown(),
								Collections.singletonList(new TLAGeneralIdentifier(
										SourceLocation.unknown(),
										part.getId(),
										Collections.emptyList()))));
						break;
				}
			}
			value = new TLAFunctionSubstitution(
					SourceLocation.unknown(),
					variableReadAccessors.get(ref),
					Collections.singletonList(
							new TLAFunctionSubstitutionPair(SourceLocation.unknown(), keys, value)));
		}

		if(!writeMacros.containsKey(ref)) {
			TLAGeneralIdentifier asIdentifier = new TLAGeneralIdentifier(
					SourceLocation.unknown(),
					new TLAIdentifier(SourceLocation.unknown(), renamingMap.get(ref)),
					Collections.emptyList());

			builder.addExpression(new TLABinOp(
					SourceLocation.unknown(),
					new TLASymbol(SourceLocation.unknown(), "="),
					Collections.emptyList(),
					new TLAUnary(
							SourceLocation.unknown(),
							new TLASymbol(SourceLocation.unknown(), "'"),
							Collections.emptyList(),
							asIdentifier),
					value));
			// this variable should now no longer show up in the eventual UNCHANGED section
			if(unchangedVariables.contains(ref)) {
				unchangedVariables.remove(ref);
			}else{
				throw new InternalCompilerError();
			}
			// make sure future references to this variable will be primed
			variableReadAccessors.put(definitionRegistry.followReference(lhs.getUID()), new TLAUnary(
					SourceLocation.unknown(),
					new TLASymbol(SourceLocation.unknown(), "'"),
					Collections.emptyList(),
					asIdentifier));
		}else{
			// inject the code for the write macro (will modify arbitrary set of other variables)
			// this will recursively generate
			writeMacros.get(ref).perform(builder, this, value);
		}
		// write any further code
		return continuation.perform(builder, this, new PlusCalStatementTranslationVisitor.PrevStatementType(
				false,
				false,
				false,
				prevStatementType.containsLabelCallReturnOrGoto()));
	}

	public void addLabelOperatorArguments(TLAOperatorBuilder def) {
		for(String argument : labelOperatorArguments) {
			def.addArgument(argument); // these arguments should never have naming conflicts
		}
	}

	public TLAExpression buildVariableRead(TLAConjunctBuilder builder,
										   TLAGeneralIdentifier name) {
		// if this involves namespaces, don't mess with it. PlusCal doesn't use those.
		UID ref = definitionRegistry.followReference(name.getUID());

		if(definitionRegistry.isLocalVariable(ref) || definitionRegistry.isGlobalVariable(ref)) {
			TLAExpression accessor;
			if((accessor = variableReadAccessors.get(ref)) != null) {
				return accessor;
			}else if(readMacros.containsKey(ref)){
				accessor = readMacros.get(ref).perform(builder, this);
				variableReadAccessors.put(ref, accessor);
				return accessor;
			}else{
				return new TLAGeneralIdentifier(
						SourceLocation.unknown(),
						new TLAIdentifier(SourceLocation.unknown(), renamingMap.get(ref)),
						Collections.emptyList());
			}
		}else{
			return name;
		}
	}
}
