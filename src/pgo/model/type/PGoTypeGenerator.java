package pgo.model.type;

import pgo.scope.UID;
import pgo.trans.PGoTransException;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Generates fresh PGoTypeVariables and infers types from Go type names.
 */
public class PGoTypeGenerator implements Supplier<PGoTypeVariable> {
	private AtomicLong current = new AtomicLong(0);
	private String prefix;

	public PGoTypeGenerator(String prefix) {
		this.prefix = prefix;
	}

	@Override
	public PGoTypeVariable get() {
		long c = current.addAndGet(1);
		return new PGoTypeVariable(prefix + Long.toString(c));
	}

	/**
	 * Generates fresh type variables while preserving the constraints
	 * within the type
	 */
	public PGoType freshNamesFor(PGoType ty) {
		HashSet<PGoTypeVariable> vars = new HashSet<>();
		ty.collectVariables(vars);
		HashMap<PGoTypeVariable, PGoType> m = new HashMap<>();
		for (PGoTypeVariable v : vars) {
			m.put(v, get());
		}
		return ty.substitute(m);
	}

	public PGoType inferFrom(String s) throws PGoTransException {
		return inferFrom(s, new HashMap<>());
	}

	private PGoType inferFrom(String s, Map<String, PGoTypeVariable> nameToTypeVar) throws PGoTransException {
		// FIXME deal with this
		UID dummyUID = new UID();
		// infer primitive types
		String lowered = s.toLowerCase();
		switch (lowered) {
			case "int":
			case "integer":
				return new PGoTypeInt(dummyUID);
			case "bool":
			case "boolean":
				return new PGoTypeBool(dummyUID);
			case "natural":
			case "uint64":
				return new PGoTypeNatural(dummyUID);
			case "decimal":
			case "float64":
				return new PGoTypeDecimal(dummyUID);
			case "string":
				return new PGoTypeString(dummyUID);
			case "interface":
			case "interface{}":
				return new PGoTypeInterface(dummyUID);
			case "error":
				return new PGoTypeError(dummyUID);
		}

		// infer miscellaneous types
		switch (s) {
			case "sync.WaitGroup":
				return new PGoTypeWaitGroup(dummyUID);
			case "sync.RWMutex":
				return new PGoTypeRWMutex(dummyUID);
			case "distsys.EtcdState":
				return new PGoTypeEtcdState(dummyUID);
			case "distsys.StateServer":
				return new PGoTypeEtcdState(dummyUID);
			case "distsys.ReleaseSet":
				return new PGoTypeReleaseSet(dummyUID);
			case "distsys.AcquireSet":
				return new PGoTypeAcquireSet(dummyUID);
			case "distsys.ValueMap":
				return new PGoTypeValueMap(dummyUID);
		}

		// infer container types
		// matches []<type>
		Pattern rgex = Pattern.compile("\\[](.+)");
		Matcher m = rgex.matcher(s);
		if (m.matches()) {
			return new PGoTypeSlice(inferFrom(m.group(1), nameToTypeVar), dummyUID);
		}

		// matches chan[<type>]
		rgex = Pattern.compile("(?i)chan\\[(.+)]");
		m = rgex.matcher(s);
		if (m.matches()) {
			return new PGoTypeChan(inferFrom(m.group(1), nameToTypeVar), dummyUID);
		}

		// matches set[<type>]
		rgex = Pattern.compile("(?i)set\\[(.+)]");
		m = rgex.matcher(s);
		if (m.matches()) {
			return new PGoTypeSet(inferFrom(m.group(1), nameToTypeVar), dummyUID);
		}

		// matches map[<type>]<type>
		rgex = Pattern.compile("(?i)map(.+)");
		m = rgex.matcher(s);
		if (m.matches()) {
			// match key type brackets
			StringBuilder key = new StringBuilder();
			String val = "";
			int depth = 0;
			for (int i = 1; i < m.group(1).length(); i++) {
				char cur = m.group(1).charAt(i);
				if (cur == '[') {
					depth++;
				} else if (cur == ']') {
					depth--;
					if (depth < 0) {
						// cur is closing bracket for key type
						val = m.group(1).substring(i + 1);
						break;
					}
				}
				key.append(cur);
			}
			if (key.toString().equals(val)) {
				PGoType tn = inferFrom(val, nameToTypeVar);
				return new PGoTypeMap(tn, tn, dummyUID);
			}
			return new PGoTypeMap(inferFrom(key.toString(), nameToTypeVar), inferFrom(val, nameToTypeVar), dummyUID);
		}

		// matches tuple[type1, type2, ..., typeN] or tuple[]
		rgex = Pattern.compile("(?i)tuple\\[(.*)]");
		m = rgex.matcher(s);
		if (m.matches()) {
			String inner = m.group(1);
			// parse comma separated list of types
			// ignore commas in nested types
			StringBuilder cur = new StringBuilder();
			List<PGoType> types = new ArrayList<>();
			for (int i = 0; i < inner.length(); i++) {
				switch (inner.charAt(i)) {
					case ',':
						String t = cur.toString().trim();
						cur = new StringBuilder();
						types.add(inferFrom(t, nameToTypeVar));
						break;
					case '[':
						// advance until matching close bracket
						int depth = 0;
						for (; i < inner.length(); i++) {
							cur.append(inner.charAt(i));
							if (inner.charAt(i) == ']') {
								depth--;
								if (depth == 0) {
									break;
								}
							} else if (inner.charAt(i) == '[') {
								depth++;
							}
						}
						break;
					default:
						cur.append(inner.charAt(i));
				}
			}
			String t = cur.toString().trim();
			if (!t.equals("")) {
				types.add(inferFrom(t, nameToTypeVar));
			}
			return new PGoTypeTuple(types, dummyUID);
		}

		if (s.length() == 1 && 'A' <= s.charAt(0) && s.charAt(0) <= 'Z') {
			if (nameToTypeVar.containsKey(s)) {
				return nameToTypeVar.get(s);
			}
			PGoTypeVariable tn = get();
			nameToTypeVar.put(s, tn);
			return tn;
		}

		throw new PGoTransException("Invalid type " + s);
	}
}
