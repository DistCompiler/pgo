package pgo.model.type;

/**
 * Represents a value map.
 */
public class PGoTypeValueMap extends PGoMiscellaneousType {
	private static final PGoTypeValueMap instance = new PGoTypeValueMap();
	private PGoTypeValueMap() {
		goType = "map[string]interface{}";
	}
	public static PGoTypeValueMap getInstance() {
		return instance;
	}
}
