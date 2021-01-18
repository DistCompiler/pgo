package pgo

import org.json.JSONObject
import org.scalatest.funsuite.AnyFunSuite

import java.util

class PGoNetOptionsTest extends AnyFunSuite { // parsed JSON object for the configuration file used in the tests
  val configStr =
    """{
      |  "build": {
      |    "output_dir": "gen",
      |    "dest_file": "out.go"
      |  },
      |  "networking": {
      |    "enabled": true,
      |
      |    "state": {
      |      "strategy": "etcd",
      |      "peers": ["10.0.0.1:12345", "10.0.0.2:12345"],
      |      "endpoints": ["172.28.128.7:2379", "172.28.128.8:2379", "172.28.128.9:2379"],
      |      "timeout": 3
      |    }
      |  }
      |}
      |""".stripMargin

  trait OFixture {
    val config = new JSONObject(configStr)

    def getNetworking = config.getJSONObject(PGoNetOptions.NETWORKING_FIELD)

    def options = new PGoNetOptions(config)
  }

  // networking mode is disabled if the configuration field is not present
  test("testNoNetworking")(new OFixture {
    config.remove("networking")
    assert(!options.isEnabled)
  })

  // networking mode is disabled if explicitly configured so in the configuration file
  test("testNetworkingDisabled")(new OFixture {
    getNetworking.put("enabled", false)
    assert(!options.isEnabled)
  })

  // configuration is invalid if an unknown state management strategy is used
  test("testInvalidStateManagementStrategy")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "invalid")
    assertThrows[PGoOptionException] {
      options
    }
  })

  // centralized-etcd state management is used if no strategy is declared
  test("testDefaultStateStrategy")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).remove("strategy")
    assert(PGoNetOptions.StateOptions.STATE_SERVER == options.getStateOptions.strategy)
  })

  // having no endpoints in the centralized-etcd strategy is invalid
  test("testNoEndpointsCentralizedEtcd")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "centralized-etcd")
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("endpoints", new util.Vector[AnyRef])
    assertThrows[PGoOptionException] {
      options
    }
  })

  // having no endpoints in the centralized strategy is invalid
  test("testNoEndpointsCentralized")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "centralized")
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("endpoints", new util.Vector[AnyRef])
    assertThrows[PGoOptionException] {
      options
    }
  })

  // having more than one endpoint in the centralized strategy is invalid
  test("testMoreThanOneEndpointCentralized")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("strategy", "centralized")
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("endpoints", new util.Vector[String](util.Arrays.asList("10.10.0.10", "10.10.0.11")))
    assertThrows[PGoOptionException] {
      options
    }
  })

  // the developer is able to specify the timeout for operations on global state
  test("testTimeout")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).put("timeout", 10)
    assert(10 == options.getStateOptions.timeout)
  })

  test("testDefaultTimeout")(new OFixture {
    getNetworking.getJSONObject(PGoNetOptions.STATE_FIELD).remove("timeout")
    assert(3 == options.getStateOptions.timeout)
  })

  // when the configuration file misses a required field (e.g., "state" or "channels"),
  // we throw a +PGoOptionException+, so that the user sees a proper error message
  // instead of a stack trace.
  test("testMissingRequiredFields")(new OFixture {
    getNetworking.remove(PGoNetOptions.STATE_FIELD)
    assertThrows[PGoOptionException] {
      options
    }
  })

  // it works and parses the information correctly when the configuration file
  // is well-formed
  test("testWellFormedConfiguration")(new OFixture {
    val net = options
    assert(net.isEnabled)
    val expectedHosts = util.Arrays.asList("172.28.128.7:2379", "172.28.128.8:2379", "172.28.128.9:2379")
    assert(PGoNetOptions.StateOptions.STATE_ETCD == net.getStateOptions.strategy)
    assert(expectedHosts == net.getStateOptions.endpoints)
  })
}