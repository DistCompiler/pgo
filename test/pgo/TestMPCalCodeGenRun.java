package pgo;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.filefilter.IOFileFilter;
import org.apache.commons.io.filefilter.TrueFileFilter;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.*;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

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

    private static InputStream strInputStream(List<String> lines) {
        return new ByteArrayInputStream(String.join("\n", lines).getBytes());
    }

    private static InputStream fileInputStream(String root, String name) {
        File file = Paths.get("test", "mpcal", "go", root, name).toFile();

        try {
            return new FileInputStream(file);
        } catch (IOException ex) {
            throw new RuntimeException("IOException: " + ex.getMessage());
        }
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
                                        strInputStream(Arrays.asList(
                                                "Connected!",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>"
                                        ))
                                ),
                                mpcalRunDef(
                                        "ALoadBalancer(0)",
                                        Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "AServer(1)",
                                        Arrays.asList("AServer(1)", "127.0.0.1:3333", "page1.html"),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "AServer(2)",
                                        Arrays.asList("AServer(2)", "127.0.0.1:4444", "page2.html"),
                                        strInputStream(Collections.emptyList())
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
                                        strInputStream(Arrays.asList(
                                                "Connected!",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>"
                                        ))
                                ),
                                mpcalRunDef(
                                        "ALoadBalancer(0)",
                                        Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "AServer(1)",
                                        Arrays.asList("AServer(1)", "127.0.0.1:3333", "page1.html"),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "AServer(2)",
                                        Arrays.asList("AServer(2)", "127.0.0.1:4444", "page2.html"),
                                        strInputStream(Collections.emptyList())
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
                                        strInputStream(Arrays.asList(
                                                "Connected!",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 1!</html>",
                                                "Received page: <html>This is server 2!</html>"
                                        ))
                                ),
                                mpcalRunDef(
                                        "ALoadBalancer(0)",
                                        Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "AServer(1)",
                                        Arrays.asList("AServer(1)", "127.0.0.1:3333", "pages"),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "AServer(2)",
                                        Arrays.asList("AServer(2)", "127.0.0.1:4444", "pages"),
                                        strInputStream(Collections.emptyList())
                                )
                        )
                },

                // Simple replicated_kv tests. No concurrency to update the same
                // keys because we want to make the state of the database after
                // execution deterministic
                {
                    "replicated_kv.tla",
                    "replicated_kv",
                    new HashMap<String, String>() {{
                        put("DISCONNECT_MSG", "\"disconnect\"");
                        put("GET_MSG", "\"get\"");
                        put("PUT_MSG", "\"put\"");
                        put("NULL_MSG", "\"clock_update\"");
                        put("NUM_CLIENTS", "2");
                        put("NUM_REPLICAS", "3");
                        put("GET_RESPONSE", "\"get_response\"");
                        put("PUT_RESPONSE", "\"put_response\"");
                    }},
                    Arrays.asList(
                            mpcalRunDef(
                                    "Client(3)",
                                    Arrays.asList(
                                            "Client(3)", "Put a Client3-v1", "Put b Client3-v2",
                                            "Get x", "Put c Client3-v3", "Get b"
                                    ),
                                    strInputStream(Arrays.asList(
                                            "-- Put (a, Client3-v1): OK",
                                            "-- Put (b, Client3-v2): OK",
                                            "-- Get x: <nil>",
                                            "-- Put (c, Client3-v3): OK",
                                            "-- Get b: Client3-v2"
                                    ))
                            ),
                            mpcalRunDef(
                                    "Client(4)",
                                    Arrays.asList(
                                            "Client(4)", "Put d Client4-v1", "Put d Client4-v2",
                                            "Put e Client4-v3", "Get d", "Get e"
                                    ),
                                    strInputStream(Arrays.asList(
                                            "-- Put (d, Client4-v1): OK",
                                            "-- Put (d, Client4-v2): OK",
                                            "-- Put (e, Client4-v3): OK",
                                            "-- Get d: Client4-v2",
                                            "-- Get e: Client4-v3"
                                    ))
                            ),
                            mpcalRunDef(
                                    "Replica(0)",
                                    Collections.singletonList("Replica(0)"),
                                    strInputStream(Arrays.asList(
                                            "Replica snapshot:",
                                            "\ta -> Client3-v1",
                                            "\tb -> Client3-v2",
                                            "\tc -> Client3-v3",
                                            "\td -> Client4-v2",
                                            "\te -> Client4-v3"
                                    ))
                            ),
                            mpcalRunDef(
                                    "Replica(1)",
                                    Collections.singletonList("Replica(1)"),
                                    strInputStream(Arrays.asList(
                                            "Replica snapshot:",
                                            "\ta -> Client3-v1",
                                            "\tb -> Client3-v2",
                                            "\tc -> Client3-v3",
                                            "\td -> Client4-v2",
                                            "\te -> Client4-v3"
                                    ))
                            ),
                            mpcalRunDef(
                                    "Replica(2)",
                                    Collections.singletonList("Replica(2)"),
                                    strInputStream(Arrays.asList(
                                            "Replica snapshot:",
                                            "\ta -> Client3-v1",
                                            "\tb -> Client3-v2",
                                            "\tc -> Client3-v3",
                                            "\td -> Client4-v2",
                                            "\te -> Client4-v3"
                                    ))
                            )
                    )
                },

                // Concurrent replicated key-value store: each client is given a list of
                // operations, and they perform them concurrently (different Go routine for
                // each operation). Since the client's output is non-deterministic, we only
                // verify the output of the replica at the end of the process, guaranteeing
                // that they are all consistent and equal.
                {
                        "concurrent_replicated_kv.tla",
                        "replicated_kv",
                        new HashMap<String, String>() {{
                            put("DISCONNECT_MSG", "\"disconnect\"");
                            put("GET_MSG", "\"get\"");
                            put("PUT_MSG", "\"put\"");
                            put("NULL_MSG", "\"clock_update\"");
                            put("NUM_CLIENTS", "3");
                            put("NUM_REPLICAS", "2");
                            put("GET_RESPONSE", "\"get_response\"");
                            put("PUT_RESPONSE", "\"put_response\"");
                        }},
                        Arrays.asList(
                                mpcalRunDef(
                                        "Replica(0)",
                                        Collections.singletonList("Replica(0)"),
                                        fileInputStream("concurrent_replicated_kv", "replicas_out.txt")
                                ),
                                mpcalRunDef(
                                        "Replica(1)",
                                        Collections.singletonList("Replica(1)"),
                                        fileInputStream("concurrent_replicated_kv", "replicas_out.txt")
                                ),
                                mpcalRunDef(
                                        "Client(2)",
                                        Collections.singletonList("Client(2)"),
                                        Paths.get(
                                                "test", "mpcal", "go", "concurrent_replicated_kv", "client2_in.txt"
                                        ).toFile(),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "Client(3)",
                                        Collections.singletonList("Client(3)"),
                                        Paths.get(
                                                "test", "mpcal", "go", "concurrent_replicated_kv", "client3_in.txt"
                                        ).toFile(),
                                        strInputStream(Collections.emptyList())
                                ),
                                mpcalRunDef(
                                        "Client(4)",
                                        Collections.singletonList("Client(4)"),
                                        Paths.get(
                                                "test", "mpcal", "go", "concurrent_replicated_kv", "client4_in.txt"
                                        ).toFile(),
                                        strInputStream(Collections.emptyList())
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