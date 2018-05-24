package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents *distsys.EtcdState.
 */
public class PGoTypeEtcdState extends PGoMiscellaneousType {
	public PGoTypeEtcdState(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeEtcdState(List<Origin> origins) {
		super(origins);
		goType = "*distsys.EtcdState";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeEtcdState;
	}
}
