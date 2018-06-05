package pgo.trans.intermediate;

import java.util.List;
import java.util.Map;

import pgo.model.golang.*;
import pgo.model.pcal.PcalProcess;
import pgo.model.pcal.VariableDeclaration;
import pgo.model.type.PGoType;
import pgo.scope.UID;
import pgo.trans.passes.codegen.CriticalSection;

public abstract class GlobalVariableStrategy implements CriticalSection {
	public abstract void initPostlude(ModuleBuilder moduleBuilder, BlockBuilder initBuilder);

	public abstract void processPrelude(BlockBuilder processBody, PcalProcess process, String processName, VariableName self, Type selfType);

	public abstract void mainPrelude(BlockBuilder builder);

	public abstract List<FunctionArgument> getExtraProcessArguments();

	@Override
	public abstract void startCriticalSection(BlockBuilder builder, int lockGroup, UID labelUID, LabelName labelName);

	@Override
	public abstract void abortCriticalSection(BlockBuilder builder, int lockGroup, UID labelUID, LabelName labelName);

	@Override
	public abstract void endCriticalSection(BlockBuilder builder, int lockGroup, UID labelUID, LabelName labelName);

	public abstract Expression readGlobalVariable(BlockBuilder builder, UID uid);

	public interface GlobalVariableWrite {
		Expression getValueSink(BlockBuilder builder);
		void writeAfter(BlockBuilder builder);
	}

	public abstract GlobalVariableWrite writeGlobalVariable(UID uid);

	// map global variables to locals
	// commit on success
	// rollback on failure
	// inputs to strategy:
	// - variables to read
	// - variables to write
	// - when a section starts
	// - when a section ends
	// - when a section rolls back
	// - ability to inform global var lookups and sets

	protected void generateLocalVariableDefinitions(DefinitionRegistry registry, Map<UID, PGoType> typeMap,
	                                                BlockBuilder processBody,
	                                                List<VariableDeclaration> variableDeclarations) {
		for (VariableDeclaration variableDeclaration : variableDeclarations) {
			Expression value = variableDeclaration.getValue().accept(
					new TLAExpressionCodeGenVisitor(processBody, registry, typeMap, this));
			if (variableDeclaration.isSet()) {
				value = new Index(value, new IntLiteral(0));
			}
			VariableName name = processBody.varDecl(variableDeclaration.getName(), value);
			processBody.linkUID(variableDeclaration.getUID(), name);
		}
	}
}
