package pgo.model.golang;

import java.util.HashSet;
import java.util.Set;

import pgo.scope.ChainSet;

public class NameCleaner {

	private Set<String> existingNames;

	public NameCleaner() {
		this(new HashSet<>());
	}

	public NameCleaner(Set<String> existingNames) {
		this.existingNames = existingNames;
	}

	public String cleanName(String nameHint) {
		if (nameHint.equals("_")) {
			return nameHint;
		}
		String actualName = nameHint;
		int count = 0;
		while(existingNames.contains(actualName)) {
			actualName = nameHint + count;
			++count;
		}
		existingNames.add(actualName);
		return actualName;
	}

	public String requireCleanName(String requiredName) {
		if (existingNames.contains(requiredName)) {
			throw new RuntimeException("internal compiler error");
		}
		return requiredName;
	}

	public NameCleaner child() {
		return new NameCleaner(new ChainSet<>(existingNames));
	}

}
