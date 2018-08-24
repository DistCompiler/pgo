package pgo.model.tla.builder;

import pgo.util.NameCleaner;
import pgo.model.tla.TLAUnit;

import java.util.ArrayList;
import java.util.List;

public class TLAModuleBuilder {

	private final List<TLAUnit> units;
	private final NameCleaner nameCleaner;

	public TLAModuleBuilder() {
		this.units = new ArrayList<>();
		this.nameCleaner = new NameCleaner();
	}

	public NameCleaner getNameCleaner() { return nameCleaner; }

	public TLAOperatorBuilder defineOperator(String nameHint) {
		String name = nameCleaner.cleanName(nameHint);
		return new TLAOperatorBuilder(this, nameCleaner.child(), name, units::add);
	}

	public List<TLAUnit> getUnits() { return units; }

}
