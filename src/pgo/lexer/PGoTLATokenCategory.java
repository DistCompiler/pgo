package pgo.lexer;

/**
 * An enumeration for extending the TLAToken.type field with custom PGo
 * information such as annotations, since we cannot modify the existing TLAToken
 * class. Treat as an extension to the constants declared there.
 */
public class PGoTLATokenCategory {
	private PGoTLATokenCategory() {}
	
	public static int PGO_ANNOTATION = 0xFFFF;
}
