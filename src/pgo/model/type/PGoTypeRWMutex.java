package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents sync.RWMutex.
 */
public class PGoTypeRWMutex extends PGoMiscellaneousType {
	public PGoTypeRWMutex(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeRWMutex(List<Origin> origins) {
		super(origins);
		goType = "sync.RWMutex";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeRWMutex;
	}
}
