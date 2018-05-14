package pgo.trans;

public class PGoAnnotationWrongNameException extends IllegalArgumentException {
	public PGoAnnotationWrongNameException(String intended, String annotationName, int line) {
		super("Trying to apply annotation intended for " + intended + " on " + annotationName + " at line " + line);
	}
}
