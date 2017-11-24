package pgo;

import static org.junit.Assert.*;

import org.apache.commons.io.IOUtils;
import org.json.JSONObject;
import org.junit.Before;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Vector;

public class PGoNetOptionsTest {

	// parsed JSON object for the configuration file used in the tests
	private JSONObject config;

	@Before
	public void setup() throws IOException {
		FileInputStream configIs = new FileInputStream("./config-sample.json");
		String configStr = IOUtils.toString(configIs);
		config = new JSONObject(configStr);
	}

	// networking mode is disabled if the configuration field is not present
	@Test
	public void testNoNetworking() throws PGoOptionException {
		config.remove("networking");
		assertFalse(options().isEnabled());
	}

	// networking mode is disabled if explicitly configured so in the configuration file
	@Test
	public void testNetworkingDisabled() throws PGoOptionException {
		getNetworking().put("enabled", false);
		assertFalse(options().isEnabled());
	}

	// configuration is invalid if an unknown state management strategy is used
	@Test(expected = PGoOptionException.class)
	public void testInvalidStateManagementStrategy() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "invalid");
		options();
	}

	// centralized state management is used if no strategy is declared
	@Test
	public void testDefaultStateStrategy() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).remove("strategy");
		assertEquals("centralized", options().getStateOptions().strategy);
	}

	// a channel where number of channels != 2 is invalid
	@Test(expected = PGoOptionException.class)
	public void testSingleProcessChannel() throws PGoOptionException {
		getNetworking().
				getJSONArray(PGoNetOptions.CHANNELS_FIELD).
				getJSONObject(0).
				getJSONArray("processes").
				remove(0);

		options();
	}

	// a channel where the two connected processes have the same ID is invalid
	@Test(expected = PGoOptionException.class)
	public void testSameProcessIdentifier() throws PGoOptionException {
		String firstProcessId = (String) getNetworking().
				getJSONArray(PGoNetOptions.CHANNELS_FIELD).
				getJSONObject(0).
				getJSONArray("processes").
				getJSONObject(0).
				get("id");

		getNetworking().
				getJSONArray(PGoNetOptions.CHANNELS_FIELD).
				getJSONObject(0).
				getJSONArray("processes").
				getJSONObject(1).
				put("id", firstProcessId);

		options();
	}

	// when the configuration file misses a required field (e.g., "state" or "channels"),
	// we throw a +PGoOptionException+, so that the user sees a proper error message
	// instead of a stack trace.
	@Test(expected = PGoOptionException.class)
	public void testMissingRequiredFields() throws PGoOptionException {
		getNetworking().remove(PGoNetOptions.STATE_FIELD);
		options();
	}

	// it works and parses the information correctly when the configuration file
	// is well-formed
	@Test
	public void testWellFormedConfiguration() throws PGoOptionException {
		PGoNetOptions net = options();

		assert(net.isEnabled());
		Vector<String> expectedHosts = new Vector<String>() {
			{
				add("10.0.0.1");
			}
		};

		assertEquals("centralized", net.getStateOptions().strategy);
		assertEquals(expectedHosts, net.getStateOptions().hosts);

		assertEquals(1, net.getChannels().size());

		PGoNetOptions.Channel channel = net.getChannels().get("msgC");
		assertEquals("msgC", channel.name);
		assertEquals(2, channel.processes.length);

		assertEquals("S", channel.processes[0].name);
		assertEquals(new ProcessStringArg("Sender"), channel.processes[0].arg);
		assertEquals("sender", channel.processes[0].role);
		assertEquals("10.0.0.2", channel.processes[0].host);
		assertEquals(5432, channel.processes[0].port);

		assertEquals("R", channel.processes[1].name);
		assertEquals(new ProcessStringArg("Receiver"), channel.processes[1].arg);
		assertEquals("receiver", channel.processes[1].role);
		assertEquals("10.0.0.3", channel.processes[1].host);
		assertEquals(3333, channel.processes[1].port);
	}

	private JSONObject getNetworking() {
		return config.getJSONObject(PGoNetOptions.NETWORKING_FIELD);
	}

	private PGoNetOptions options() throws PGoOptionException {
		return new PGoNetOptions(config);
	}
}
