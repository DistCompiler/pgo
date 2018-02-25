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
		assertEquals("centralized-etcd", options().getStateOptions().strategy);
	}

	// the developer is able to specify the timeout for operations on global state
	@Test
	public void testTimeout() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("timeout", 10);
		assertEquals(10, options().getStateOptions().timeout);
	}

	@Test
	public void testDefaultTimeout() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).remove("timeout");
		assertEquals(3, options().getStateOptions().timeout);
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
		assertEquals(expectedHosts, net.getStateOptions().endpoints);
	}

	private JSONObject getNetworking() {
		return config.getJSONObject(PGoNetOptions.NETWORKING_FIELD);
	}

	private PGoNetOptions options() throws PGoOptionException {
		return new PGoNetOptions(config);
	}
}
