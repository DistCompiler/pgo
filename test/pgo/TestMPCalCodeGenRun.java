package pgo;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.filefilter.IOFileFilter;
import org.apache.commons.io.filefilter.TrueFileFilter;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertThat;
import static pgo.IntegrationTestingUtils.*;

@RunWith(Parameterized.class)
public class TestMPCalCodeGenRun {

    private String spec;
    String pack;
    private Map<String, String> constants;
    List<IntegrationTestingUtils.MPCalRunDefinition> processes;

    public TestMPCalCodeGenRun(String spec, String pack, Map<String, String> constants, List<IntegrationTestingUtils.MPCalRunDefinition> processes) {
        this.spec = spec;
        this.pack = pack;
        this.constants = constants;
        this.processes = processes;
    }

    @Parameterized.Parameters
    public static List<Object[]> data() {
        return Arrays.asList(new Object[][] {
                {
                        "load_balancer_tuples.tla",
                        "load_balancer",
                        new HashMap<String, String>() {{
                            put("NUM_CLIENTS", "1");
                            put("LoadBalancerId", "0");
                            put("GET_PAGE", "200");
                            put("NUM_SERVERS", "2");
                        }},
                        Arrays.asList(
                                mpcalRunDef(
                                        "AClient(3)",
                                        Arrays.asList("AClient(3)", "127.0.0.1:5555"),
                                        Arrays.asList(
                                                "Connected!",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>"
                                        )
                                ),
                                mpcalRunDef(
                                        "ALoadBalancer(0)",
                                        Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
                                        Collections.emptyList()
                                ),
                                mpcalRunDef(
                                        "AServer(1)",
                                        Arrays.asList("AServer(1)", "127.0.0.1:3333", "page1.html"),
                                        Collections.emptyList()
                                ),
                                mpcalRunDef(
                                        "AServer(2)",
                                        Arrays.asList("AServer(2)", "127.0.0.1:4444", "page2.html"),
                                        Collections.emptyList()
                                )
                        )
                },

                {
                        "load_balancer_record_payloads.tla",
                        "load_balancer",
                        new HashMap<String, String>() {{
                            put("NUM_CLIENTS", "1");
                            put("LoadBalancerId", "0");
                            put("GET_PAGE", "200");
                            put("NUM_SERVERS", "2");
                        }},
                        Arrays.asList(
                                mpcalRunDef(
                                        "AClient(3)",
                                        Arrays.asList("AClient(3)", "127.0.0.1:5555"),
                                        Arrays.asList(
                                                "Connected!",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>"
                                        )
                                ),
                                mpcalRunDef(
                                        "ALoadBalancer(0)",
                                        Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
                                        Collections.emptyList()
                                ),
                                mpcalRunDef(
                                        "AServer(1)",
                                        Arrays.asList("AServer(1)", "127.0.0.1:3333", "page1.html"),
                                        Collections.emptyList()
                                ),
                                mpcalRunDef(
                                        "AServer(2)",
                                        Arrays.asList("AServer(2)", "127.0.0.1:4444", "page2.html"),
                                        Collections.emptyList()
                                )
                        )
                },

                {
                        "load_balancer_file_system.tla",
                        "load_balancer",
                        new HashMap<String, String>() {{
                            put("NUM_CLIENTS", "1");
                            put("LoadBalancerId", "0");
                            put("GET_PAGE", "200");
                            put("NUM_SERVERS", "2");
                        }},
                        Arrays.asList(
                                mpcalRunDef(
                                        "AClient(3)",
                                        Arrays.asList("AClient(3)", "127.0.0.1:5555"),
                                        Arrays.asList(
                                                "Connected!",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>"
                                        )
                                ),
                                mpcalRunDef(
                                        "ALoadBalancer(0)",
                                        Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
                                        Collections.emptyList()
                                ),
                                mpcalRunDef(
                                        "AServer(1)",
                                        Arrays.asList("AServer(1)", "127.0.0.1:3333", "pages"),
                                        Collections.emptyList()
                                ),
                                mpcalRunDef(
                                        "AServer(2)",
                                        Arrays.asList("AServer(2)", "127.0.0.1:4444", "pages"),
                                        Collections.emptyList()
                                )
                        )
                }
        });
    }

    @Test
    @SuppressWarnings("unchecked")
    public void test() throws IOException {
        File goDir = Paths.get("test", "mpcal", "go", FilenameUtils.removeExtension(spec)).toFile();

        testCompileMPCal(Paths.get("test", "mpcal", "spec", spec), pack, constants,
                outputPath -> {
                    List<File> directories = new ArrayList<>();

                    // copy files and directories under test/mpcal/spec/{spec_name} to the compiled
                    // output temporary directory before we attempt to run it
                    for (Iterator<File> it = FileUtils.iterateFiles(goDir, TrueFileFilter.INSTANCE, new IOFileFilter() {
                        @Override
                        public boolean accept(File dir) {
                            if (dir.getParentFile().equals(goDir)) {
                                directories.add(dir);
                            }

                            return false;
                        }

                        @Override
                        public boolean accept(File file, String s) {
                            return accept(file);
                        }
                    }); it.hasNext(); ) {
                        File f = it.next();

                        Path destFile = outputPath.resolve(f.getName());
                        FileUtils.copyFile(f, destFile.toFile());
                    }

                    for (File directory : directories) {
                        FileUtils.copyDirectory(directory, outputPath.resolve(directory.getName()).toFile());
                    }

                    try {
                        testRunDistributedMPCal(outputPath, processes);
                    } catch (InterruptedException e) {
                        throw new RuntimeException("InterruptedException: " + e.getMessage());
                    }
                });
    }
}