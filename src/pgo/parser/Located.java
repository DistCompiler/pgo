package pgo.parser;

import pgo.util.SourceLocatable;
import pgo.util.SourceLocation;

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

	public T getValue(){
		return value;
	}
}
