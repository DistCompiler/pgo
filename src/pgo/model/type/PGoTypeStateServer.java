package pgo.model.type;

import pgo.util.Origin;

import java.util.Arrays;
import java.util.List;

/**
 * Represents distsys.StateServer.
 */
public class PGoTypeStateServer extends PGoMiscellaneousType {
	public PGoTypeStateServer(Origin... origins) {
		this(Arrays.asList(origins));
	}

	public PGoTypeStateServer(List<Origin> origins) {
		super(origins);
		goType = "distsys.StateServer";
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof PGoTypeStateServer;
	}
}
