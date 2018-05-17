package pgo.trans.intermediate;

import pgo.scope.UID;

public class ScopeConflict {
	QualifiedName name;
	UID first;
	UID second;
	
	public ScopeConflict(QualifiedName name, UID first, UID second) {
		super();
		this.name = name;
		this.first = first;
		this.second = second;
	}
	
	public ScopeConflict(String name, UID first, UID second) {
		this.name = new QualifiedName(name);
		this.first = first;
		this.second = second;
	}
	
	public QualifiedName getName() {
		return name;
	}

	public UID getFirst() {
		return first;
	}

	public UID getSecond() {
		return second;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((first == null) ? 0 : first.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((second == null) ? 0 : second.hashCode());
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
		ScopeConflict other = (ScopeConflict) obj;
		if (first == null) {
			if (other.first != null)
				return false;
		} else if (!first.equals(other.first))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (second == null) {
			if (other.second != null)
				return false;
		} else if (!second.equals(other.second))
			return false;
		return true;
	}
}
