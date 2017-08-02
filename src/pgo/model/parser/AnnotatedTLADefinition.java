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
 * "def <name>(<params>)? <type>? == <TLA expression>".
 *
 */
public class AnnotatedTLADefinition {
	// the macro name
	private String name;
	// the definition
	private TLAExpr expr;
	// the parameters, of the form "name <type>"
	private Vector<PGoVariable> params;
	// the type that the expression should evaluate to
	private PGoType type;

	private int line;

	protected AnnotatedTLADefinition(String name, Vector<PGoVariable> params, TLAExpr expr, PGoType type, int l) {
		this.name = name;
		this.params = params;
		this.expr = expr;
		this.type = type;
		this.line = l;
	}

	public static AnnotatedTLADefinition parse(String s, int l) throws PGoParseException {
		// of the form def <name>(<params>) == <TLA expression>
		Pattern regex = Pattern.compile("def ([^(\\s]+)(\\(.+\\))?\\s*(.+)*?\\s*==\\s*([\\s\\S]+)");
		Matcher m = regex.matcher(s);
		if (!m.matches()) {
			throw new PGoParseException(
					"TLA definition annotations are of the form \"def <name>(<params>)? <type>? == <TLA expression>\"",
					l);
		}
		String name = m.group(1);
		String params = m.group(2);
		String typeString = m.group(3);
		String expr = m.group(4);

		Vector<PGoVariable> paramVars = new Vector<>();
		if (params != null) {
			// trim the surrounding parens
			params = params.substring(1, params.length() - 1);
			// split the params into name-type pairs
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
		}

		PGoType type = null;

		if (typeString != null) {
			typeString = typeString.trim();
			type = PGoType.inferFromGoTypeName(typeString);
			if (type.isUndetermined()) {
				throw new PGoParseException(
						"Unknown type annotation " + typeString + " encountered in annotation for TLA definition", l);
			}
		}

		// parse the expression into TLATokens
		String[] exprLines = expr.split("\\n");
		Vector<String> v = new Vector<>(Arrays.asList(exprLines));
		PcalCharReaderPgo chars = new PcalCharReaderPgo(PcalParser.removeTabs(v), 0, 0, v.size(),
				v.get(v.size() - 1).length());
		try {
			// TODO parse indentation of lists
			// Precedence of boolean logic lists depends on indentation level.
			// We can add parentheses before tokenizing to solve this.
			TLAExpr tla = Tokenize.TokenizeExpr(chars);
			return new AnnotatedTLADefinition(name, paramVars, tla, type, l);
		} catch (TokenizerException e) {
			throw new PGoParseException(
					"Encountered TokenizerException when parsing annotation for TLA definition: " + e.getMessage(), l);
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

	public PGoType getType() {
		return type;
	}

	public int getLine() {
		return line;
	}
}
