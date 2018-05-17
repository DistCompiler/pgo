package pgo.model.tla;

import java.util.List;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST Node:
 * 
 * ---- ModuleName ----
 * EXTENDS ModuleA, ModuleB
 * ...
 * ====
 *
 */
public class PGoTLAModule extends PGoTLAUnit {
	
	PGoTLAIdentifier name;
	List<PGoTLAIdentifier> exts;
	List<PGoTLAUnit> preTranslationUnits;
	List<PGoTLAUnit> translatedUnits;
	List<PGoTLAUnit> postTranslationUnits;

	public PGoTLAModule(SourceLocation location, PGoTLAIdentifier name, List<PGoTLAIdentifier> exts,
			List<PGoTLAUnit> preTranslationUnits, List<PGoTLAUnit> translatedUnits, List<PGoTLAUnit> postTranslationUnits) {
		super(location);
		this.name = name;
		this.exts = exts;
		this.preTranslationUnits = preTranslationUnits;
		this.translatedUnits = translatedUnits;
		this.postTranslationUnits = postTranslationUnits;
	}
	
	public PGoTLAIdentifier getName() {
		return name;
	}
	
	public List<PGoTLAIdentifier> getExtends(){
		return exts;
	}

	public List<PGoTLAUnit> getPreTranslationUnits() {
		return preTranslationUnits;
	}

	public List<PGoTLAUnit> getTranslatedUnits() {
		return translatedUnits;
	}

	public List<PGoTLAUnit> getPostTranslationUnits() {
		return postTranslationUnits;
	}

	@Override
	public <T, E extends Throwable> T accept(PGoTLAUnitVisitor<T, E> v) throws E {
		return v.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((exts == null) ? 0 : exts.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((postTranslationUnits == null) ? 0 : postTranslationUnits.hashCode());
		result = prime * result + ((preTranslationUnits == null) ? 0 : preTranslationUnits.hashCode());
		result = prime * result + ((translatedUnits == null) ? 0 : translatedUnits.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		PGoTLAModule other = (PGoTLAModule) obj;
		if (exts == null) {
			if (other.exts != null)
				return false;
		} else if (!exts.equals(other.exts))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (postTranslationUnits == null) {
			if (other.postTranslationUnits != null)
				return false;
		} else if (!postTranslationUnits.equals(other.postTranslationUnits))
			return false;
		if (preTranslationUnits == null) {
			if (other.preTranslationUnits != null)
				return false;
		} else if (!preTranslationUnits.equals(other.preTranslationUnits))
			return false;
		if (translatedUnits == null) {
			if (other.translatedUnits != null)
				return false;
		} else if (!translatedUnits.equals(other.translatedUnits))
			return false;
		return true;
	}
	
}
