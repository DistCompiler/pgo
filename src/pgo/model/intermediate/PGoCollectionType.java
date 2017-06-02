package pgo.model.intermediate;

import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Represents the collections from pluscal converted to Go. Collections are
 * types like arrays/slice, queues/chan, maps, sets that hold a collection of primitives
 *
 * The following types in go correspond to the following type names
 * arrays/slices - [<#elem>]<etype>, channels - chan <etype>,
 * sets - set[]<etype>, maps - map[<keyType>]<etype>
 * 
 */
public abstract class PGoCollectionType extends PGoType {
	
	// The type of an empty set. The empty set is compatible with all set types.
	public static final PGoSet EMPTY_SET = new PGoSet("");

	// The contained type
	protected PGoType eType;

	protected PGoCollectionType() {
	}

	protected PGoCollectionType(String eTypeS) {
		eType = PGoType.inferFromGoTypeName(eTypeS);
		if (eType.isUndetermined()) {
			this.isUndetermined = true;
		}
	}

	public PGoType getElementType() {
		return eType;
	}

	/**
	 * Represents a slice in Go lang, which is just a specialized array of elements in pluscal
	 *
	 */
	public static class PGoSlice extends PGoCollectionType {

		private String initCap;

		public PGoSlice(String eType) {
			super(eType);
			initCap = "";
		}

		public PGoSlice(String initCap, String eType) {
			super(eType);
			this.initCap = initCap;
		}

		public String getInitCap() {
			return initCap;
		}

		@Override
		public String toTypeName() {
			if (!initCap.isEmpty()) {
				return "[" + initCap + "]" + eType.toTypeName();
			} else {
				return "[]" + eType.toTypeName();
			}
		}

		@Override
		public String toGo() {
			if (!initCap.isEmpty()) {
				return "[" + initCap + "]" + eType.toGo();
			} else {
				return "[]" + eType.toGo();
			}
		}
	}

	/**
	 * Represents a queue or channel in pluscal, which converts to channels in go
	 * 
	 */
	public static class PGoChan extends PGoCollectionType {

		public PGoChan(String eTypeS) {
			super(eTypeS);
		}

		@Override
		public String toTypeName() {
			return "chan[" + eType.toTypeName() + "]";
		}

		@Override
		public String toGo() {
			return "chan " + eType.toGo();
		}
	}

	/**
	 * Represents a set in pluscal, which converts to some custom set type in go
	 * 
	 */
	public static class PGoSet extends PGoCollectionType {

		public PGoSet(String eTypeS) {
			super(eTypeS);
		}

		@Override
		public String toTypeName() {
			return "set[" + eType.toTypeName() + "]";
		}

		@Override
		public String toGo() {
			return "mapset.Set";
		}
	}

	/**
	 * Represents a map in pluscal (array indexed by non-numbers), which converts to map in go
	 * 
	 */
	public static class PGoMap extends PGoCollectionType {

		private PGoType kType;

		public PGoMap(String ktype, String etype) {
			super(etype);
			kType = PGoType.inferFromGoTypeName(ktype);
			if (kType.isUndetermined()) {
				this.isUndetermined = true;
			}
		}

		public PGoType getKeyType() {
			return kType;
		}

		@Override
		public String toTypeName() {
			return "map[" + kType.toTypeName() + "]" + eType.toTypeName();
		}

		public String toGo() {
			return "map[" + kType.toGo() + "]" + eType.toGo();
		}
	}

	/**
	 * Represents a pointer to something
	 * 
	 */
	public static class PGoPointer extends PGoCollectionType {

		protected PGoPointer(String eTypeS) {
			super(eTypeS);
		}

		@Override
		public String toTypeName() {
			return eType.toTypeName() + "*";
		}

		public String toGo() {
			return eType.toGo() + "*";
		}
	}

	/**
	 * Represents an anonymous function
	 * 
	 */
	public static class PGoAnonymousFunction extends PGoCollectionType {
		private static final String goType = "func()";

		// the paramer types
		private Vector<PGoType> paramType;
		// TODO support multiple return values. but is this needed?
		private PGoType retType;

		public PGoAnonymousFunction(Vector<PGoType> params, PGoType ret) {
			paramType = params;
			retType = ret;
		}

		public Vector<PGoType> getParamType() {
			return paramType;
		}

		public PGoType getReturnType() {
			return retType;
		}

		@Override
		public String toTypeName() {
			Vector<String> pstrings = new Vector<String>();
			for (PGoType t : paramType) {
				pstrings.add(t.toTypeName());
			}

			return "func(" + String.join(", ", pstrings) + ") " + retType.toTypeName();
		}

		@Override
		public String toGo() {
			Vector<String> pstrings = new Vector<String>();
			for (PGoType t : paramType) {
				pstrings.add(t.toGo());
			}

			return ("func(" + String.join(" ", pstrings) + ") " + retType.toGo()).trim();
		}

	}

	/**
	 * Infers the PGo container type from given string
	 * 
	 * @param s
	 *            the go type
	 * @return
	 */
	public static PGoType inferContainerFromGoTypeName(String s) {
		PGoType ret;

		// matches [<number>?]<type>
		Pattern rgex = Pattern.compile("\\[(\\d*)\\](.+)");
		Matcher m = rgex.matcher(s);
		if (m.matches()) {
			if (m.group(1) != null && !m.group(1).isEmpty()) {
				ret = new PGoSlice(m.group(1), m.group(2));
			} else {
				ret = new PGoSlice(m.group(2));
			}
			if (!ret.isUndetermined()) {
				return ret;
			}
		}

		// matches chan[<type>]
		rgex = Pattern.compile("(?i)chan\\[(.+)\\]");
		m = rgex.matcher(s);
		if (m.matches()) {
			ret = new PGoChan(m.group(1));
			if (!ret.isUndetermined()) {
				return ret;
			}
		}

		// matches set[<type>]
		rgex = Pattern.compile("(?i)set\\[(.+)\\]");
		m = rgex.matcher(s);
		if (m.matches()) {
			ret = new PGoSet(m.group(1));
			if (!ret.isUndetermined()) {
				return ret;
			}
		}

		// matches map[<type>]<type>
		rgex = Pattern.compile("(?i)map\\[(.+?)\\](.+)");
		m = rgex.matcher(s);
		if (m.matches()) {
			ret = new PGoMap(m.group(1), m.group(2));
			if (!ret.isUndetermined()) {
				return ret;
			}
		}
		return new PGoUndetermined();
	}
}
