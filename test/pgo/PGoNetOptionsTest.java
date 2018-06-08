package pgo;

import static org.junit.Assert.*;

import org.apache.commons.io.IOUtils;
import org.json.JSONObject;
import org.junit.Before;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Vector;

public class PGoNetOptionsTest {

	// parsed JSON object for the configuration file used in the tests
	private JSONObject config;

	@Before
	public void setup() throws IOException {
		FileInputStream configIs = new FileInputStream("./examples/configs/etcd.json");
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

	// centralized-etcd state management is used if no strategy is declared
	@Test
	public void testDefaultStateStrategy() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).remove("strategy");
		assertEquals(PGoNetOptions.StateOptions.STATE_ETCD, options().getStateOptions().strategy);
	}

	// having no endpoints in the centralized-etcd strategy is invalid
	@Test(expected = PGoOptionException.class)
	public void testNoEndpointsCentralizedEtcd() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "centralized-etcd");
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("endpoints", new Vector<>());
		options();
	}

	// having no endpoints in the centralized strategy is invalid
	@Test(expected = PGoOptionException.class)
	public void testNoEndpointsCentralized() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "centralized");
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("endpoints", new Vector<>());
		options();
	}

	// having more than one endpoint in the centralized strategy is invalid
	@Test(expected = PGoOptionException.class)
	public void testMoreThanOneEndpointCentralized() throws PGoOptionException {
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "centralized");
		getNetworking().getJSONObject(PGoNetOptions.STATE_FIELD).put("endpoints", new Vector<String>(Arrays.asList("10.10.0.10", "10.10.0.11")));
		options();
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
		List<String> expectedHosts = Arrays.asList("172.28.128.7:2379", "172.28.128.8:2379", "172.28.128.9:2379");
		assertEquals(PGoNetOptions.StateOptions.STATE_ETCD, net.getStateOptions().strategy);
		assertEquals(expectedHosts, net.getStateOptions().endpoints);
	}

	private JSONObject getNetworking() {
		return config.getJSONObject(PGoNetOptions.NETWORKING_FIELD);
	}

	private PGoNetOptions options() throws PGoOptionException {
		return new PGoNetOptions(config);
	}
}
