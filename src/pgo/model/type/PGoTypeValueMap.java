package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents a value map.
 */
public class PGoTypeValueMap extends PGoMiscellaneousType {
	public PGoTypeValueMap(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeValueMap(List<Origin> origins) {
		super(origins);
		goType = "map[string]interface{}";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeValueMap;
	}
}
