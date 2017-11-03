package pgo;

import org.json.JSONArray;
import org.json.JSONObject;

import java.util.Arrays;
import java.util.HashMap;

// wraps options related to networking in the generated Go code.
// Networking related options are defined in the JSON configuration
// file and specify details about message channels (e.g., IP addresses
// and ports. See the +sample.json+ file included in this repository
// for an example of how to define these properties.

// This class is initialized in PGoOptions. If there is any configuration
// error in the JSON file provided, an exception will be thrown and the
// user will be notified.
public class PGoNetOptions {
	private class Process {
		public String id;
		public String role;
		public String host;
		public int port;

		public Process(JSONObject config) throws PGoOptionException {
			this.id = config.getString("id");
			this.role = config.getString("role");
			this.host = config.getString("host");
			this.port = config.getInt("port");

			validate();
		}

		public void validate() throws PGoOptionException {
			if (id.isEmpty()) {
				throw new PGoOptionException("all processes need to have an ID");
			}
		}

	}

	private class StateOptions {
		private static final String STATE_CENTRALIZED = "centralized";
		private final String[] STATE_STRATEGIES = {
				STATE_CENTRALIZED
		};

		private static final String DEFAULT_STATE_STRATEGY = STATE_CENTRALIZED;

		public String strategy;
		public String host;
		public int port;

		public StateOptions(JSONObject config) throws PGoOptionException {
			this.strategy = config.getString("strategy");
			if (this.strategy == null) {
				this.strategy = DEFAULT_STATE_STRATEGY;
			}

			this.host = config.getString("host");
			this.port = config.getInt("port");

			validate();
		}

		private void validate() throws PGoOptionException {
			if (!Arrays.asList(STATE_STRATEGIES).contains(this.strategy)) {
				throw new PGoOptionException("Invalid state strategy: " + this.strategy);
			}
		}
	}

	private class Channel {
		public String name;
		public Process[] processes;

		// channels connect two processes
		private static final int PROCESSES_PER_CHANNEL = 2;

		public Channel(JSONObject config) throws PGoOptionException {
			this.name = config.getString("name");
			JSONArray p = config.getJSONArray("processes");
			int i;

			if (p.length() != PROCESSES_PER_CHANNEL) {
				throw new PGoOptionException("Channel \"" + name + "\": must have 2 processes");
			}


			processes = new Process[PROCESSES_PER_CHANNEL];
			for (i = 0; i < PROCESSES_PER_CHANNEL; i++) {
				processes[i] = new Process(p.getJSONObject(i));
			}

			validate();
		}

		private void validate() throws PGoOptionException {
			if (processes[0].id.equals(processes[1].id)) {
				throw new PGoOptionException("Processes should have different ids");
			}
		}
	}

	private boolean enabled = false;

	private StateOptions stateOptions;
	private HashMap<String, Channel> channels = new HashMap<String, Channel>();

	public PGoNetOptions(JSONObject config) throws PGoOptionException {
		JSONObject netConfig = config.getJSONObject("networking");
		JSONObject stateConfig = netConfig.getJSONObject("state");
		JSONArray channelsConfig = netConfig.getJSONArray("channels");
		int i;

		if (!netConfig.getBoolean("enabled")) {
			enabled = false;
			return;
		}

		enabled = true;
		stateOptions = new StateOptions(stateConfig);

		for (i = 0; i < channelsConfig.length(); i++) {
			JSONObject channel = (JSONObject) channelsConfig.get(i);
			String name = channel.getString("name");

			if (channels.get(name) != null) {
				throw new PGoOptionException("Process with name \"" + name + "\" already exists");
			}

			channels.put(name, new Channel(channel));
		}
	}

	public boolean isEnabled() {
		return this.enabled;
	}
}
