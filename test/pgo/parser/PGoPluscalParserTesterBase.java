package pgo.parser;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import org.apache.commons.io.IOUtils;

import pgo.PGoPluscalTesterBase;
import pgo.model.type.PGoType;
import pgo.model.parser.PGoAnnotation;

/**
 * Abstract class for testing parsing of real pluscal algorithms. This class
 * will store the data of the expected parsed result to test them.
 *
 */
public abstract class PGoPluscalParserTesterBase extends PGoPluscalTesterBase {

	/**
	 * Gets the expected lines of annotation to be parsed
	 * 
	 * @return
	 */
	public abstract Vector<PGoAnnotation> getAnnotations();

	/**
	 * Gets the expected AST as a string
	 * 
	 * @return
	 * @throws IOException
	 */
	public String getASTString() throws IOException {
		FileInputStream inputStream = new FileInputStream("./test/pluscal/ast/" + getAlg());
		return IOUtils.toString(inputStream);
	}

	// get the constant, arg, and normal variable data respectively
	public List<ConstAnnotatedVariableData> getConstAnnotatedVariables() {
		return new ArrayList<ConstAnnotatedVariableData>();
	}

	public List<ArgAnnotatedVariableData> getArgAnnotatedVariables() {
		return new ArrayList<ArgAnnotatedVariableData>();
	}

	public List<VarAnnotatedVariableData> getVarAnnotatedVariables() {
		return new ArrayList<VarAnnotatedVariableData>();
	}

	// get total number of annotated variables
	public int getNumberAnnotatedVariables() {
		return getConstAnnotatedVariables().size() + getArgAnnotatedVariables().size()
				+ getVarAnnotatedVariables().size();
	}

	// Stores the expected annotation const ariable data for testing
	public static class ConstAnnotatedVariableData {

		// the type of the variable
		public final PGoType type;

		// the variable name
		public final String name;

		// the line number of the annotation
		public final int line;

		// the value of the constant
		public final String val;

		public ConstAnnotatedVariableData(PGoType type, String name, int line, String val) {
			this.type = type;
			this.name = name;
			this.line = line;
			this.val = val;
		}
	}

	// Stores the expected annotation arg variable data for testing
	public static class ArgAnnotatedVariableData {

		// the type of the variable
		public final PGoType type;

		// the variable name
		public final String name;

		// the line number of annotation
		public final int line;

		// whether this is a flag or a positional argument
		public final boolean isPositional;

		// the flag argument name
		public final String argName;

		public ArgAnnotatedVariableData(PGoType type, String name, int line, boolean isPositional, String argName) {
				this.type = type;
				this.name = name;
				this.line = line;
			this.isPositional = isPositional;
			this.argName = argName;
			}
	}

	// Stores the expected annotation normal variable data for testing
	public static class VarAnnotatedVariableData {

		// the type of the variable
		public final PGoType type;

		// the variable name
		public final String name;

		// the line number of the variable
		public final int line;

		public VarAnnotatedVariableData(PGoType type, String name, int line) {
				this.type = type;
				this.name = name;
				this.line = line;
			}
	}

	// Gets the number of annotated functions for the algorithm
	public int getNumberAnnotatedFunctions() {
		return getAnnotatedFunctions().size();
	}

	// Gets the list of annotated functions we expect
	public List<AnnotatedFunctionData> getAnnotatedFunctions() {
		return new ArrayList<AnnotatedFunctionData>();
	}

	/**
	 * Stores the expected data of annotated functions
	 *
	 */
	public static class AnnotatedFunctionData {

		// the name of the function
		public final String name;

		// the line number of the annotation
		public final int line;

		// the return type of function
		public final PGoType rType;

		// the types of arguments to the function
		public final Vector<PGoType> argTypes;

		public AnnotatedFunctionData(String name, int line, PGoType rType, Vector<PGoType> argTypes) {
			this.name = name;
			this.line = line;
			this.rType = rType;
			this.argTypes = argTypes;
		}

	}

	// get the number of global variables used for function return in pluscal
	// algorithm
	public int getNumberReturnVariables() {
		return getReturnVariables().size();
	}

	// get list of all expected variables used for function return value in
	// pluscal algorithm
	public List<ReturnVariableData> getReturnVariables() {
		return new ArrayList<ReturnVariableData>();
	}

	/**
	 * Stores the expected data of annotated variables used for function return
	 * 
	 */
	public static class ReturnVariableData {

		// the name of the variable
		public final String name;
		// the line number of the annotation
		public final int line;

		public ReturnVariableData(String name, int line) {
			this.name = name;
			this.line = line;
		}

	}

	// get the number of processes annotated in pluscal algorithm
	public int getNumberAnnotatedProcesses() {
		return getAnnotatedProcesses().size();
	}

	// get the expected process annotation data
	public List<AnnotatedProcessData> getAnnotatedProcesses() {
		return new ArrayList<AnnotatedProcessData>();
	}

	/**
	 * Stores the expected data of annotated processes
	 * 
	 */
	public static class AnnotatedProcessData {

		// the name of the process
		public final String name;
		// the line number of the annotation
		public final int line;
		// the PGoType of the id of the process
		public final PGoType idType;

		public AnnotatedProcessData(String name, int line, PGoType idType) {
			this.name = name;
			this.line = line;
			this.idType = idType;
		}

	}
}
