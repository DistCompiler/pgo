package pgo.trans.passes.codegen;

import pgo.InternalCompilerError;
import pgo.model.golang.BlockBuilder;
import pgo.model.golang.LabelName;
import pgo.scope.UID;

import java.util.Map;
import java.util.function.BiConsumer;

public class CriticalSectionTracker {
	private Map<UID, Integer> labelsToLockGroups;
	private CriticalSection criticalSection;
	private int currentLockGroup;
	private UID currentLabelUID;
	private LabelName currentLabelName;

	private CriticalSectionTracker(Map<UID, Integer> labelsToLockGroups, CriticalSection criticalSection,
	                               int currentLockGroup, UID currentLabelUID, LabelName currentLabelName) {
		this.labelsToLockGroups = labelsToLockGroups;
		this.criticalSection = criticalSection;
		this.currentLockGroup = currentLockGroup;
		this.currentLabelUID = currentLabelUID;
		this.currentLabelName = currentLabelName;
	}

	public CriticalSectionTracker(Map<UID, Integer> labelsToLockGroups, CriticalSection criticalSection) {
		this(labelsToLockGroups, criticalSection, -1, null, null);
	}

	public void start(BlockBuilder builder, UID labelUID, LabelName labelName) {
		int lockGroup = labelsToLockGroups.getOrDefault(labelUID, -1);
		if (currentLockGroup != -1 && currentLockGroup != lockGroup) {
			// FIXME this is VERY WRONG
			end(builder);
		}
		if (currentLockGroup == lockGroup) {
			// FIXME recursive lock
			return;
		}
		builder.labelIsUnique(labelName.getName());
		criticalSection.startCriticalSection(builder, lockGroup, labelUID, labelName);
		currentLockGroup = lockGroup;
		currentLabelUID = labelUID;
		currentLabelName = labelName;
	}

	public void abort(BlockBuilder builder) {
		if (currentLockGroup == -1) {
			// nothing to do
			return;
		}
		criticalSection.abortCriticalSection(builder, currentLockGroup, currentLabelUID, currentLabelName);
	}

	public void end(BlockBuilder builder) {
		if (currentLockGroup == -1) {
			// nothing to do
			return;
		}
		criticalSection.endCriticalSection(builder, currentLockGroup, currentLabelUID, currentLabelName);
		currentLockGroup = -1;
		currentLabelUID = null;
		currentLabelName = null;
	}

	public void beginIfStatement(BiConsumer<CriticalSectionTracker, CriticalSectionTracker> consumer) {
		CriticalSectionTracker yesTracker = copy();
		CriticalSectionTracker noTracker = copy();
		consumer.accept(yesTracker, noTracker);
		currentLockGroup = -1;
		currentLabelUID = null;
		currentLabelName = null;
	}

	public CriticalSectionTracker copy() {
		return new CriticalSectionTracker(labelsToLockGroups, criticalSection, currentLockGroup, currentLabelUID,
				currentLabelName);
	}
}
