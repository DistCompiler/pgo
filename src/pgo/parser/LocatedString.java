package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class LocatedString extends SourceLocatable {
	
	String value;
	SourceLocation location;
	
	public LocatedString(String value, SourceLocation location) {
		this.value = value;
		this.location = location;
	}

	public String getValue() {
		return value;
	}

	public SourceLocation getLocation() {
		return location;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((location == null) ? 0 : location.hashCode());
		result = prime * result + ((value == null) ? 0 : value.hashCode());
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
		LocatedString other = (LocatedString) obj;
		if (location == null) {
			if (other.location != null)
				return false;
		} else if (!location.equals(other.location))
			return false;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}
