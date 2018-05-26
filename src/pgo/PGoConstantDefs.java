package pgo;

import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import org.json.JSONObject;

import pgo.parser.LocatedString;
import pgo.util.SourceLocation;

public class PGoConstantDefs {
	
	private Map<String, LocatedString> defs;
	
	public PGoConstantDefs(JSONObject config, String configFilePath) {
		defs = new HashMap<>();
		if(config.has("constants")){
			JSONObject constants = config.getJSONObject("constants");
			for(String name : constants.keySet()) {
				String val = constants.getString(name);
				defs.put(name, new LocatedString(val, new SourceLocation(Paths.get(configFilePath), 1, 1, 1, val.length()+1)));
			}
		}
	}
	
	public Map<String, LocatedString> getConstants(){
		return defs;
	}

}
