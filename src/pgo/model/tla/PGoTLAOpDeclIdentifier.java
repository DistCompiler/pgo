package pgo.model.tla;

/**
 * 
 * In the simplest case, an operator argument is just an identifier, i.e :
 * 
 * fn(a) == ...
 *
 */
public class PGoTLAOpDeclIdentifier extends PGoTLAOpDecl {
	private String name;
	public PGoTLAOpDeclIdentifier(String name) {
		this.name = name;
	}
	@Override
	public String toString() {
		return "PGoTLAOpDeclIdentifier [name=" + name + "]";
	}
}
