package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents distsys.AcquireSet.
 */
public class PGoTypeAcquireSet extends PGoMiscellaneousType {
	public PGoTypeAcquireSet(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeAcquireSet(List<Origin> origins) {
		super(origins);
		goType = "distsys.AcquireSet";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeAcquireSet;
	}
}
