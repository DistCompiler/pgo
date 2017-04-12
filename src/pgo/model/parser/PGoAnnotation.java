package pgo.model.parser;

/**
 * Represents a single annotation of PGo, with the annotation string and the
 * line number
 * 
 */
public class PGoAnnotation {

	// The annotation string
	String annotation;
	// The line number
	int line;

	public PGoAnnotation(String s, int l) {
		annotation = s.trim();
		line = l;
	}

	public String getString() {
		return annotation;
	}

	public int getLine() {
		return line;
	}
}
