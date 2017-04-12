package pgo.trans.intermediate.model;

import pgo.parser.PGoParseException;

/**
 * Represents the information of a variable from annotations
 * The AnnotatedVariable class is jsut the 
 */
public abstract class AnnotatedVariable {

	public static final String CONST = "const";
	public static final String ARG = "arg";
	public static final String VAR = "var";
	
	private String name;
	private PGoType type;

	public AnnotatedVariable(String[] parts) {
		if (parts.length >= 3) {
			type = PGoPrimitiveType.inferPrimitiveFromGoTypeName(parts[1]);
			name = parts[2];
		}
	}

	public static AnnotatedVariable parse(String[] parts, int line) throws PGoParseException {
		switch(parts[0].toLowerCase()) {
		case CONST:
			return new ConstAnnotatedVariable(parts, line);
		case ARG:
			return new ArgAnnotatedVariable(parts, line);
		case VAR:
			return new VarAnnotatedVariable(parts, line);
		default:
		}
		assert (false);
		return null;
	}

	public String getName() {
		return name;
	}

	// Add the information from annotation to the variable
	public abstract void fillVariable(PGoVariable var);

	/**
	 * An annotated variable that is to be a constant in Go
	 *
	 */
	public static class ConstAnnotatedVariable extends AnnotatedVariable {

		private String val;

		public ConstAnnotatedVariable(String[] parts, int line) throws PGoParseException {
			super(parts);
			if (parts.length != 4) {
				throw new PGoParseException("Annotation of \"const\" expects " + "<type> <varname> <val>. Got only "
						+ (parts.length - 1) + " arguments instead", line);
			}
			val = parts[3];
		}

		@Override
		public void fillVariable(PGoVariable var) {
			// TODO Auto-generated method stub

		}
		
	}
	
	public static class ArgAnnotatedVariable extends AnnotatedVariable {

		private boolean positional;
		private String argname;

		public ArgAnnotatedVariable(String[] parts, int line) throws PGoParseException {
			super(parts);
			if (parts.length <= 3 || parts.length >= 4) {
				throw new PGoParseException("Annotation of \"arg\" expects "
						+ "<type> <varname> (<flagname>)?. Got only "
						+ (parts.length - 1) + " arguments instead", line);
			}
			if (parts.length == 4) {
				positional = false;
				argname = parts[3];
			} else {
				positional = true;
			}
		}

		@Override
		public void fillVariable(PGoVariable var) {
			// TODO Auto-generated method stub

		}
		
	}
	
	public static class VarAnnotatedVariable extends AnnotatedVariable {

		public VarAnnotatedVariable(String[] parts, int line) throws PGoParseException {
			super(parts);
			if (parts.length != 3) {
				throw new PGoParseException("Annotation of \"var\" expects <type> <varname>. Got only "
						+ (parts.length - 1) + " arguments instead", line);
			}
		}

		@Override
		public void fillVariable(PGoVariable var) {
			// TODO Auto-generated method stub

		}
	}
}
