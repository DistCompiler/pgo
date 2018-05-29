package pgo.model.golang;

import java.util.Set;

import pgo.scope.ChainSet;

public class NameCleaner {
	
	private Set<String> existingNames;

	public NameCleaner(Set<String> existingNames) {
		this.existingNames = existingNames;
	}
	
	public String cleanName(String nameHint) {
		String actualName = nameHint;
		int count = 0;
		while(existingNames.contains(nameHint)) {
			actualName = nameHint + count;
			++count;
		}
		existingNames.add(actualName);
		return actualName;
	}
	
	public NameCleaner child() {
		return new NameCleaner(new ChainSet<>(existingNames));
	}

}
