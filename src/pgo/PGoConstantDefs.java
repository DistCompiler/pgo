package pgo;

import org.json.JSONObject;
import pgo.parser.Located;
import pgo.util.SourceLocation;

import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

public class PGoConstantDefs {
	
	private Map<String, Located<String>> defs;
	
	public PGoConstantDefs(JSONObject config, String configFilePath) {
		defs = new HashMap<>();
		if(config.has("constants")){
			JSONObject constants = config.getJSONObject("constants");
			for(String name : constants.keySet()) {
				String val = constants.getString(name);
				defs.put(name, new Located<String>(
						new SourceLocation(Paths.get(configFilePath), 1, 1, 1, val.length()+1),
						val));
			}
		}
	}
	
	public Map<String, Located<String>> getConstants(){
		return defs;
	}

}
