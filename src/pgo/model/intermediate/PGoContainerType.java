package pgo.model.intermediate;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Represents the containers from pluscal converted to Go. Containers are types
 * like arrays/slice, queues/chan, maps, sets that hold a collection of
 * primitives
 *
 * The following types in go correspond to the following type names
 * arrays/slices - [<#elem>]<etype>, channels - chan <etype>, sets -
 * set[]<etype>, maps - map[<keyType>]<etype>
 * 
 */
public abstract class PGoContainerType extends PGoType {

	// The contained type
	protected PGoType eType;

	protected PGoContainerType(String eTypeS) {
		eType = PGoType.inferFromGoTypeName(eTypeS);
		if (eType.isUndetermined()) {
			this.isUndetermined = true;
		}
	}

	public PGoType getElementType() {
		return eType;
	}

	/**
	 * Represents a slice in Go lang, which is just a specialized array of
	 * elements in pluscal
	 *
	 */
	public static class PGoSlice extends PGoContainerType {

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
		public String toGoTypeName() {
			if (!initCap.isEmpty()) {
				return "[" + initCap + "]" + eType.toGoTypeName();
			} else {
				return "[]" + eType.toGoTypeName();
			}
		}
	}

	/**
	 * Represents a queue or channel in pluscal, which converts to channels in
	 * go
	 * 
	 */
	public static class PGoChan extends PGoContainerType {

		public PGoChan(String eTypeS) {
			super(eTypeS);
		}

		@Override
		public String toGoTypeName() {
			return "chan[" + eType.toGoTypeName() + "]";
		}

	}

	/**
	 * Represents a set in pluscal, which converts to some custom set type in go
	 * 
	 */
	public static class PGoSet extends PGoContainerType {

		public PGoSet(String eTypeS) {
			super(eTypeS);
		}

		@Override
		public String toGoTypeName() {
			return "set[]" + eType.toGoTypeName();
		}

	}

	/**
	 * Represents a map in pluscal (array indexed by non-numbers), which
	 * converts to map in go
	 * 
	 */
	public static class PGoMap extends PGoContainerType {

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
		public String toGoTypeName() {
			return "map[" + kType.toGoTypeName() + "]" + eType.toGoTypeName();
		}

	}

	/**
	 * Infers the PGo container type from given string
	 * 
	 * @param s the go type
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
		rgex = Pattern.compile("chan\\[(.+)\\]");
		m = rgex.matcher(s);
		if (m.matches()) {
			ret = new PGoChan(m.group(1));
			if (!ret.isUndetermined()) {
				return ret;
			}
		}
		
		// matches set[]<type>
		rgex = Pattern.compile("set\\[\\](.+)");
		m = rgex.matcher(s);
		if (m.matches()) {
			ret = new PGoSet(m.group(1));
			if (!ret.isUndetermined()) {
				return ret;
			}
		}

		// matches map[<type>]<type>
		rgex = Pattern.compile("map\\[(.+?)\\](.+)");
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
