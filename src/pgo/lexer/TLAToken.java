package pgo.lexer;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

public class TLAToken extends SourceLocatable {
	
	String value;
	TLATokenType type;
	SourceLocation location;

	public TLAToken(String value, TLATokenType type, SourceLocation location) {
		this.value = value;
		this.type = type;
		this.location = location;
	}
	
	@Override
	public SourceLocation getLocation() {
		return location;
	}

	public String getValue() {
		return value;
	}

	public TLATokenType getType() {
		return type;
	}

	@Override
	public String toString() {
		return "TLAToken [value=" + value + ", type=" + type + ", location=" + location + "]";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((location == null) ? 0 : location.hashCode());
		result = prime * result + ((type == null) ? 0 : type.hashCode());
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
		TLAToken other = (TLAToken) obj;
		if (location == null) {
			if (other.location != null)
				return false;
		} else if (!location.equals(other.location))
			return false;
		if (type != other.type)
			return false;
		if (value == null) {
			if (other.value != null)
				return false;
		} else if (!value.equals(other.value))
			return false;
		return true;
	}

}
