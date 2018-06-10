package pgo.trans.intermediate;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import pgo.model.tla.PGoTLAGeneralIdentifierPart;

public class QualifiedName {
	String base;
	List<String> prefix;
	
	public QualifiedName(List<String> prefix, String base) {
		this.base = base;
		this.prefix = prefix;
	}
	
	public QualifiedName(String base) {
		this.base = base;
		this.prefix = Collections.emptyList();
	}
	
	public static QualifiedName fromTLAPrefix(List<PGoTLAGeneralIdentifierPart> prefix, String base) {
		return new QualifiedName(prefix.stream().map(p -> p.getIdentifier().getId()).collect(Collectors.toList()), base);
	}
	
	public QualifiedName withPrefix(String pfx) {
		List<String> newPrefix = new ArrayList<>(prefix);
		newPrefix.add(0, pfx);
		return new QualifiedName(newPrefix, base);
	}

	public String getBase() {
		return base;
	}

	public List<String> getPrefix() {
		return prefix;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((base == null) ? 0 : base.hashCode());
		result = prime * result + ((prefix == null) ? 0 : prefix.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		QualifiedName other = (QualifiedName) obj;
		if (base == null) {
			if (other.base != null)
				return false;
		} else if (!base.equals(other.base))
			return false;
		if (prefix == null) {
			if (other.prefix != null)
				return false;
		} else if (!prefix.equals(other.prefix))
			return false;
		return true;
	}
	
}
