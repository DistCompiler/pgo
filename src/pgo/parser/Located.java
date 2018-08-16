package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

import java.util.Objects;

public class Located<T> extends SourceLocatable {

	private final SourceLocation location;
	private final T value;

	public Located(SourceLocation location, T value){
		this.location = location;
		this.value = value;
	}

	@Override
	public String toString() {
		return ""+value+" at "+location;
	}

	@Override
	public SourceLocation getLocation() {
		return location;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (o == null || getClass() != o.getClass()) return false;
		Located<?> located = (Located<?>) o;
		return Objects.equals(location, located.location) &&
				Objects.equals(value, located.value);
	}

	@Override
	public int hashCode() {
		return Objects.hash(location, value);
	}

	public T getValue(){
		return value;
	}
}
