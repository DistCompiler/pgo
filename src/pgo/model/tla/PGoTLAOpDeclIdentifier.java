package pgo.model.tla;

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
