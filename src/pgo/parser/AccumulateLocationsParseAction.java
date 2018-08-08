package pgo.parser;

import java.util.List;

public class AccumulateLocationsParseAction extends ParseAction {

	private int destinationLocation;
	private List<Integer> partLocations;

	public AccumulateLocationsParseAction(List<Integer> partResultLocations, int destinationLocation) {
		this.partLocations = partResultLocations;
		this.destinationLocation = destinationLocation;
	}

	public int getDestinationLocation() { return destinationLocation; }
	public List<Integer> getPartLocations() { return partLocations; }

	@Override
	public boolean isDecidable() {
		return true;
	}

	@Override
	public boolean accept(ParseActionExecutor exec) {
		return exec.visit(this);
	}
}
