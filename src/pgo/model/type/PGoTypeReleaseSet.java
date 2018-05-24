package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents *distsys.ReleaseSet.
 */
public class PGoTypeReleaseSet extends PGoMiscellaneousType {
	public PGoTypeReleaseSet(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeReleaseSet(List<Origin> origins) {
		super(origins);
		goType = "*distsys.ReleaseSet";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeReleaseSet;
	}
}
