package pgo.trans.intermediate;

import pgo.model.pcal.*;
import pgo.scope.UID;

import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.function.Function;

public class PlusCalProcessesAtomicityInferenceVisitor extends ProcessesVisitor<Void, RuntimeException> {
	protected BiConsumer<UID, UID> captureLabel;
	protected Function<UID, Consumer<UID>> captureLabelRead;
	protected Function<UID, Consumer<UID>> captureLabelWrite;

	public PlusCalProcessesAtomicityInferenceVisitor(BiConsumer<UID, UID> captureLabel,
	                                                 Function<UID, Consumer<UID>> captureLabelRead,
	                                                 Function<UID, Consumer<UID>> captureLabelWrite) {
		this.captureLabel = captureLabel;
		this.captureLabelRead = captureLabelRead;
		this.captureLabelWrite = captureLabelWrite;
	}

	@Override
	public Void visit(SingleProcess singleProcess) throws RuntimeException {
		// nothing to do
		return null;
	}

	@Override
	public Void visit(MultiProcess multiProcess) throws RuntimeException {
		for (PcalProcess p : multiProcess.getProcesses()) {
			for (LabeledStatements statements : p.getLabeledStatements()) {
				UID labelUID = statements.getLabel().getUID();
				captureLabel.accept(p.getUID(), labelUID);
				statements.accept(new PlusCalStatementAtomicityInferenceVisitor(
						captureLabelRead.apply(labelUID), captureLabelWrite.apply(labelUID)));
			}
		}
		return null;
	}
}
