package pgo.model.parser;

import java.util.Arrays;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import pcal.PcalCharReaderPgo;
import pcal.TLAExpr;
import pcal.Tokenize;
import pcal.exception.TokenizerException;
import pgo.model.intermediate.PGoType;
import pgo.model.intermediate.PGoVariable;
import pgo.parser.PGoParseException;
import pgo.parser.PcalParser;

/**
 * Represents an annotated TLA definition of a macro which is called in the
 * PlusCal algorithm. This definition has the form
 * "macro <name>(<params>) == <TLA expression>".
 *
 */
public class AnnotatedTLADefinition {
	// the macro name
	private String name;
	// the definition
	private TLAExpr expr;
	// the parameters, of the form "name <type>"
	private Vector<PGoVariable> params;

	private int line;

	protected AnnotatedTLADefinition(String name, Vector<PGoVariable> params, TLAExpr expr, int l) {
		this.name = name;
		this.params = params;
		this.expr = expr;
		this.line = l;
	}

	public static AnnotatedTLADefinition parse(String s, int l) throws PGoParseException {
		// of the form macro <name>(<params>) == <TLA expression>
		Pattern regex = Pattern.compile("macro (.+)\\((.+)\\)\\s*==\\s*((.|\\s)+)");
		Matcher m = regex.matcher(s);
		if (!m.matches()) {
			throw new PGoParseException(
					"TLA definition annotations are of the form \"macro <name>(<params>) == <TLA expression>\"", l);
		}
		String name = m.group(1);
		String params = m.group(2);
		String expr = m.group(3);
		
		// split the params into name-type pairs
		Vector<PGoVariable> paramVars = new Vector<>();
		String[] vars = params.split(",");
		for (String var : vars) {
			// should be "name <type>"
			var = var.trim();
			String[] parts = var.split("\\s");
			if (parts.length != 2) {
				throw new PGoParseException("Expected parameter to be fo the form \"name <type>\", but found "
						+ parts.length + " parts instead.", l);
			}
			paramVars.add(PGoVariable.convert(parts[0], PGoType.inferFromGoTypeName(parts[1])));
		}
		
		// parse the expression into TLATokens
		String[] exprLines = expr.split("\\n");
		Vector<String> v = new Vector<>(Arrays.asList(exprLines));
		PcalCharReaderPgo chars = new PcalCharReaderPgo(PcalParser.removeTabs(v), 0, 0, v.size(),
				v.get(v.size() - 1).length());
		try {
			TLAExpr tla = Tokenize.TokenizeExpr(chars);
			return new AnnotatedTLADefinition(name, paramVars, tla, l);
		} catch (TokenizerException e) {
			throw new PGoParseException(
					"Encountered TokenizerException when parsing annotation for TLA definition: " + e.getMessage()
							+ " (line " + l + ")");
		}
	}

	public String getName() {
		return name;
	}
	
	public TLAExpr getExpr() {
		return expr;
	}

	public Vector<PGoVariable> getParams() {
		return new Vector<>(params);
	}
	
	public int getLine() {
		return line;
	}
}
