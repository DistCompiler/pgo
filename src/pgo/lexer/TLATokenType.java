package pgo.lexer;

public enum TLATokenType {
	STRING,
	IDENT,
	NUMBER,
	BUILTIN,
	// These tokens delimit the TLA+ translated from PlusCal
	// we need these to know the precise scoping of the PlusCal
	// code (i.e operators declared after this section are not available, but those before are)
	// It also helps us not warn the user about double variable declarations when a variable is in
	// the PlusCal and the generated TLA+
	BEGIN_TRANSLATION,
	END_TRANSLATION,
}
