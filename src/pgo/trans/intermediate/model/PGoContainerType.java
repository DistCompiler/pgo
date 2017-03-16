package pgo.trans.intermediate.model;

/**
 * Represents the containers from pluscal converted to Go. Containers are types
 * like arrays, queues, maps, sets that hold a collection of primitives
 *
 */
public abstract class PGoContainerType extends PGoType {

	/**
	 * Represents an Array of elements in pluscal, which converts to array in go
	 * 
	 */
	public static class PGoArray extends PGoContainerType {

		@Override
		public String toGo() {
			// TODO Auto-generated method stub
			return null;
		}

	}

	/**
	 * Represents a queue or channel in pluscal, which converts to channels in
	 * go
	 * 
	 */
	public static class PGoQueue extends PGoContainerType {

		@Override
		public String toGo() {
			// TODO Auto-generated method stub
			return null;
		}

	}

	/**
	 * Represents a set in pluscal, which converts to some custom set type in go
	 * 
	 */
	public static class PGoSet extends PGoContainerType {

		@Override
		public String toGo() {
			// TODO Auto-generated method stub
			return null;
		}

	}

	/**
	 * Represents a map in pluscal (array indexed by non-numbers), which
	 * converts to map in go
	 * 
	 */
	public static class PGoMap extends PGoContainerType {

		@Override
		public String toGo() {
			// TODO Auto-generated method stub
			return null;
		}

	}
}
