package pgo;

import org.apache.commons.io.FilenameUtils;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;
import static pgo.IntegrationTestingUtils.testCompileMPCal;

@RunWith(Parameterized.class)
public class TestMPCalCodeGenRun {
    private String spec;
    String pack;
    private Map<String, String> constants;

    public TestMPCalCodeGenRun(String spec, String pack, Map<String, String> constants) {
        this.spec = spec;
        this.pack = pack;
        this.constants = constants;
    }

    @Parameterized.Parameters
    public static List<Object[]> data() {
        return Arrays.asList(new Object[][] {
                {
                        "load_balancer.tla",
                        "load_balancer",
                        new HashMap<String, String>() {{
                            put("BUFFER_SIZE", "3");
                            put("NUM_CLIENTS", "1");
                            put("LoadBalancerId", "0");
                            put("WEB_PAGE", "42");
                            put("GET_PAGE", "200");
                            put("NUM_SERVERS", "2");
                        }}
                }
        });
    }

    @Test
    public void test() throws IOException {
        Path source = Paths.get("test", "mpcal", "go", FilenameUtils.removeExtension(spec) + ".go");
        testCompileMPCal(Paths.get("test", "mpcal", "spec", spec), pack, constants,
                compiledPackagePath -> {
                        String compiled = String.join("\n", Files.readAllLines(compiledPackagePath));
                        String expected = String.join("\n", Files.readAllLines(source));

                        assertEquals(expected, compiled);
                });
    }
}