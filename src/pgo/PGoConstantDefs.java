package pgo;

import org.json.JSONObject;
import pgo.util.SourceLocation;

import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

public class PGoConstantDefs {
	
	private Map<String, PGoConstantDef> defs;
	
	public PGoConstantDefs(JSONObject config, String configFilePath) {
		defs = new HashMap<>();
		if (config.has("constants")) {
			JSONObject constants = config.getJSONObject("constants");
			for (String name : constants.keySet()) {
				String val = constants.getString(name);
				defs.put(name, new PGoConstantDef(
						new SourceLocation(Paths.get(configFilePath), 0, 0, 1, 1, 1, val.length()+1),
						val));
			}
		}
	}
	
	public Map<String, PGoConstantDef> getConstants(){
		return defs;
	}

}
