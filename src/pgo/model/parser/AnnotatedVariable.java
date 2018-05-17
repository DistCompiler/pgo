package pgo.model.parser;

import java.util.logging.Level;
import java.util.logging.Logger;

import pgo.model.intermediate.PGoVariable;
import pgo.model.type.PGoType;
import pgo.model.type.PGoTypeGenerator;
import pgo.parser.PGoParseException;
import pgo.trans.PGoAnnotationWrongNameException;
import pgo.trans.PGoTransException;

/**
 * Represents the information of a variable from annotations The
 * AnnotatedVariable class is the base class
 * 
 */
public abstract class AnnotatedVariable {
	public static final String CONST = "const";
	public static final String ARG = "arg";
	public static final String VAR = "var";

	// name of variable
	protected String name;

	// type of variable
	protected PGoType type;

	// the line number of annotation
	protected int line;

	protected AnnotatedVariable(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
		if (parts.length >= 3) {
			type = generator.inferFrom(parts[2]);
			name = parts[1];
			this.line = line;
		}
	}

	// parses a const, arg, or var annotation for a variable
	public static AnnotatedVariable parse(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
		switch (parts[0].toLowerCase()) {
		case CONST:
			return new ConstAnnotatedVariable(line, parts, generator);
		case ARG:
			return new ArgAnnotatedVariable(line, parts, generator);
		case VAR:
			return new VarAnnotatedVariable(line, parts, generator);
		default:
			throw new PGoParseException("Unknown annotation", line);
		}
	}

	public String getName() {
		return name;
	}

	public PGoType getType() {
		return type;
	}

	public int getLine() {
		return line;
	}

	// Add the information from annotation to the variable
	public abstract void applyAnnotationOnVariable(PGoVariable var);

	/**
	 * An annotated variable that is to be a constant in Go
	 *
	 */
	public static class ConstAnnotatedVariable extends AnnotatedVariable {

		private String val;

		public ConstAnnotatedVariable(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
			super(line, parts, generator);
			if (parts.length != 4) {
				throw new PGoParseException("Annotation of \"const\" expects " + "<type> <varname> <val>. Got only "
						+ parts.length + " arguments instead", line);
			}
			val = parts[3];
		}

		@Override
		public void applyAnnotationOnVariable(PGoVariable var) {
			if (!var.getName().equals(this.name)) {
				throw new PGoAnnotationWrongNameException(name, var.getName(), line);
			}
			var.setType(this.getType());
			var.setIsSimpleAssign(true);
			var.setGoVal(this.getVal());
			var.setIsConstant(true);

			Logger.getLogger("PGo Stage Typing").log(Level.INFO, "filling in variable \"" + var.getName()
					+ "\" based on annotation as a constant from line: " + this.getLine());
		}

		public String getVal() {
			return val;
		}

	}

	/**
	 * Annotated variable that will become a command line argument in go
	 *
	 */
	public static class ArgAnnotatedVariable extends AnnotatedVariable {

		private boolean positional;
		private String argname;

		public ArgAnnotatedVariable(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
			super(line, parts, generator);
			if (parts.length < 3 || parts.length > 4) {
				throw new PGoParseException("Annotation of \"arg\" expects "
						+ "<type> <varname> (<flagname>)?. Got only "
						+ parts.length + " arguments instead", line);
			}
			if (parts.length == 4) {
				positional = false;
				argname = parts[3];
			} else {
				positional = true;
				argname = "";
			}
		}

		@Override
		public void applyAnnotationOnVariable(PGoVariable var) {
			if (!var.getName().equals(this.name)) {
				throw new PGoAnnotationWrongNameException(name, var.getName(), line);
			}
			var.setType(this.getType());
			var.setArgInfo(this);

			Logger.getLogger("PGo Stage Typing").log(Level.INFO, "filling in variable \"" + var.getName()
					+ "\" based on annotation as an command line argument from line: " + this.getLine());
		}

		public String getArgName() {
			return argname;
		}

		public boolean isPositionalArg() {
			return positional;
		}
	}

	/**
	 * Annotated variable for any non-special variable in Go
	 *
	 */
	public static class VarAnnotatedVariable extends AnnotatedVariable {

		public VarAnnotatedVariable(int line, String[] parts, PGoTypeGenerator generator) throws PGoParseException, PGoTransException {
			super(line, parts, generator);
			if (parts.length != 3) {
				throw new PGoParseException("Annotation of \"var\" expects <type> <varname>. Got only "
						+ parts.length + " arguments instead", line);
			}
		}

		@Override
		public void applyAnnotationOnVariable(PGoVariable var) {
			if (!var.getName().equals(this.name) && !this.name.split("\\.")[1].equals(var.getName())) {
				throw new PGoAnnotationWrongNameException(name, var.getName(), line);
			}
			var.setType(this.getType());
			Logger.getLogger("PGo Stage Typing").log(Level.INFO, "filling in variable \"" + var.getName()
					+ "\" based on annotation as a standard variable from line: " + this.getLine());
		}
	}
}
