package pgo.model.tla;

import java.util.List;
import java.util.stream.Collectors;

import pgo.util.SourceLocation;

/**
 * 
 * TLA AST PlusCalNode:
 * 
 * ---- ModuleName ----
 * EXTENDS ModuleA, ModuleB
 * ...
 * ====
 *
 */
public class TLAModule extends TLAUnit {
	
	private TLAIdentifier name;
	private List<TLAIdentifier> exts;
	private List<TLAUnit> preTranslationUnits;
	private List<TLAUnit> translatedUnits;
	private List<TLAUnit> postTranslationUnits;

	public TLAModule(SourceLocation location, TLAIdentifier name, List<TLAIdentifier> exts,
					 List<TLAUnit> preTranslationUnits, List<TLAUnit> translatedUnits, List<TLAUnit> postTranslationUnits) {
		super(location);
		this.name = name;
		this.exts = exts;
		this.preTranslationUnits = preTranslationUnits;
		this.translatedUnits = translatedUnits;
		this.postTranslationUnits = postTranslationUnits;
	}
	
	@Override
	public TLAModule copy() {
		return new TLAModule(getLocation(), name.copy(),
				exts.stream().map(TLAIdentifier::copy).collect(Collectors.toList()),
				preTranslationUnits.stream().map(TLAUnit::copy).collect(Collectors.toList()),
				translatedUnits.stream().map(TLAUnit::copy).collect(Collectors.toList()),
				postTranslationUnits.stream().map(TLAUnit::copy).collect(Collectors.toList()));
	}
	
	public TLAIdentifier getName() {
		return name;
	}
	
	public List<TLAIdentifier> getExtends(){
		return exts;
	}

	public List<TLAUnit> getPreTranslationUnits() {
		return preTranslationUnits;
	}

	public List<TLAUnit> getTranslatedUnits() {
		return translatedUnits;
	}

	public List<TLAUnit> getPostTranslationUnits() {
		return postTranslationUnits;
	}

	@Override
	public <T, E extends Throwable> T accept(TLAUnitVisitor<T, E> v) throws E {
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
		TLAModule other = (TLAModule) obj;
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
