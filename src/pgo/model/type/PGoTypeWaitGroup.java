package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents sync.WaitGroup.
 */
public class PGoTypeWaitGroup extends PGoMiscellaneousType {
	public PGoTypeWaitGroup(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeWaitGroup(List<Origin> origins) {
		super(origins);
		goType = "sync.WaitGroup";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeWaitGroup;
	}
}
