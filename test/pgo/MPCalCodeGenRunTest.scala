package pgo

import org.scalatest.funsuite.AnyFunSuite
import pgo.IntegrationTestingUtils.{mpcalRunDef, testCompileMPCal, testRunDistributedMPCal}

import java.io.{ByteArrayInputStream, FileInputStream, IOException, InputStream}
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, FileVisitor, Files, Path, Paths}
import java.util
import scala.jdk.CollectionConverters._

class MPCalCodeGenRunTest extends AnyFunSuite {
  def check(tag: String)(specName: String, pack: String,
                         constants: Map[String,String],
                         processes: List[IntegrationTestingUtils.MPCalRunDefinition]): Unit =
    test(tag) {
      val goDir = Paths.get("test", "mpcal", "go", specName)

      testCompileMPCal(Paths.get("test", "mpcal", "spec", s"$specName.tla"), pack, constants.asJava, { outputPath =>
        // copy files and directories under test/go/spec/{spec_name} to the compiled
        // output temporary directory before we attempt to run it
        Files.walkFileTree(goDir, new FileVisitor[Path] {
          var currentOutputDir = outputPath

          override def preVisitDirectory(dir: Path, attrs: BasicFileAttributes): FileVisitResult = {
            if(dir != goDir) {
              Files.copy(dir, currentOutputDir.resolve(dir.getFileName))
              currentOutputDir = currentOutputDir.resolve(dir.getFileName)
            }
            FileVisitResult.CONTINUE
          }

          override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
            Files.copy(file, currentOutputDir.resolve(file.getFileName))
            FileVisitResult.CONTINUE
          }

          override def visitFileFailed(file: Path, exc: IOException): FileVisitResult =
            throw new RuntimeException(s"failed to visit file: $file", exc)

          override def postVisitDirectory(dir: Path, exc: IOException): FileVisitResult = {
            if(exc ne null) {
              throw new RuntimeException(s"failed to visit directory: $dir", exc)
            } else {
              currentOutputDir = currentOutputDir.getParent
              FileVisitResult.CONTINUE
            }
          }
        })

        // attempt to run
        try {
          testRunDistributedMPCal(outputPath, processes.asJava)
        } catch {
          case e: InterruptedException =>
            throw new RuntimeException("InterruptedException: " + e.getMessage, e)
        }
      })
    }

  def strInputStream(str: String): InputStream =
    new ByteArrayInputStream(str.getBytes())

  def fileInputStream(parts: String*): InputStream =
    new FileInputStream(
      Paths.get("test", Seq("mpcal", "go") ++ parts :_*).toFile)

  check("load_balancer_tuples")(
    specName = "load_balancer_tuples",
    pack = "load_balancer",
    constants = Map(
      "NUM_CLIENTS" -> "1",
      "LoadBalancerId" -> "0",
      "GET_PAGE" -> "200",
      "NUM_SERVERS" -> "2"),
    processes = List(
      mpcalRunDef(
        "AClient(3)",
        util.Arrays.asList("AClient(3)", "127.0.0.1:5555"),
        strInputStream {
          """Connected!
            |Received page: <html>This is server 1!</html>
            |Received page: <html>This is server 2!</html>
            |Received page: <html>This is server 1!</html>
            |Received page: <html>This is server 2!</html>""".stripMargin
        }),
      mpcalRunDef(
        "ALoadBalancer(0)",
        util.Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
        strInputStream("")),
      mpcalRunDef(
        "AServer(1)",
        util.Arrays.asList("AServer(1)", "127.0.0.1:3333", "page1.html"),
        strInputStream("")),
      mpcalRunDef(
        "AServer(2)",
        util.Arrays.asList("AServer(2)", "127.0.0.1:4444", "page2.html"),
        strInputStream(""))))

  check("load_balancer_record_payloads")(
    specName = "load_balancer_record_payloads",
    pack = "load_balancer",
    constants = Map(
      "NUM_CLIENTS" -> "1",
      "LoadBalancerId" -> "0",
      "GET_PAGE" -> "200",
      "NUM_SERVERS" -> "2"),
    List(
      mpcalRunDef(
        "AClient(3)",
        List("AClient(3)", "127.0.0.1:5555").asJava,
        strInputStream {
          """Connected!
            |Received page: <html>This is server 1!</html>
            |Received page: <html>This is server 2!</html>
            |Received page: <html>This is server 1!</html>
            |Received page: <html>This is server 2!</html>""".stripMargin
        }),
      mpcalRunDef(
        "ALoadBalancer(0)",
        util.Arrays.asList("ALoadBalancer(0)", "127.0.0.1:2222"),
        strInputStream("")),
      mpcalRunDef(
        "AServer(1)",
        List("AServer(1)", "127.0.0.1:3333", "page1.html").asJava,
        strInputStream("")),
      mpcalRunDef(
        "AServer(2)",
        List("AServer(2)", "127.0.0.1:4444", "page2.html").asJava,
        strInputStream(""))))

  check("load_balancer_file_system")(
    specName = "load_balancer_file_system",
    pack = "load_balancer",
    constants = Map(
      "NUM_CLIENTS" -> "1",
      "LoadBalancerId" -> "0",
      "GET_PAGE" -> "200",
      "NUM_SERVERS" -> "2"),
    processes = List(
      mpcalRunDef(
        "AClient(3)",
        List("AClient(3)", "127.0.0.1:5555").asJava,
        strInputStream {
          """Connected!
            |Received page: <html>This is server 1!</html>
            |Received page: <html>This is server 1!</html>
            |Received page: <html>This is server 2!</html>""".stripMargin
        }),
      mpcalRunDef(
        "ALoadBalancer(0)",
        List("ALoadBalancer(0)", "127.0.0.1:2222").asJava,
        strInputStream("")),
      mpcalRunDef(
        "AServer(1)",
        List("AServer(1)", "127.0.0.1:3333", "pages").asJava,
        strInputStream("")),
      mpcalRunDef(
        "AServer(2)",
        List("AServer(2)", "127.0.0.1:4444", "pages").asJava,
        strInputStream(""))))

  // Simple replicated_kv tests. No concurrency to update the same
  // keys because we want to make the state of the database after
  // execution deterministic
  check("replicated_kv")(
    specName = "replicated_kv",
    pack = "replicated_kv",
    constants = Map(
      "DISCONNECT_MSG" -> "\"disconnect\"",
      "GET_MSG" -> "\"get\"",
      "PUT_MSG" -> "\"put\"",
      "NULL_MSG" -> "\"clock_update\"",
      "NUM_CLIENTS" -> "2",
      "NUM_REPLICAS" -> "3",
      "GET_RESPONSE" -> "\"get_response\"",
      "PUT_RESPONSE" -> "\"put_response\""),
    processes = List(
      mpcalRunDef(
        "Client(3)",
        List(
          "Client(3)", "Put a Client3-v1", "Put b Client3-v2",
          "Get x", "Put c Client3-v3", "Get b"
        ).asJava,
        strInputStream {
          """-- Put (a, Client3-v1): OK
            |-- Put (b, Client3-v2): OK
            |-- Get x: <nil>
            |-- Put (c, Client3-v3): OK
            |-- Get b: Client3-v2""".stripMargin
        }),
      mpcalRunDef(
        "Client(4)",
        List(
          "Client(4)", "Put d Client4-v1", "Put d Client4-v2",
          "Put e Client4-v3", "Get d", "Get e"
        ).asJava,
        strInputStream {
          """-- Put (d, Client4-v1): OK
            |-- Put (d, Client4-v2): OK
            |-- Put (e, Client4-v3): OK
            |-- Get d: Client4-v2
            |-- Get e: Client4-v3""".stripMargin
        }),
      mpcalRunDef(
        "Replica(0)",
        List("Replica(0)").asJava,
        strInputStream {
          "Replica snapshot:\n" +
            "\ta -> Client3-v1\n" +
            "\tb -> Client3-v2\n" +
            "\tc -> Client3-v3\n" +
            "\td -> Client4-v2\n" +
            "\te -> Client4-v3"
        }),
      mpcalRunDef(
        "Replica(1)",
        List("Replica(1)").asJava,
        strInputStream {
          "Replica snapshot:\n" +
            "\ta -> Client3-v1\n" +
            "\tb -> Client3-v2\n" +
            "\tc -> Client3-v3\n" +
            "\td -> Client4-v2\n" +
            "\te -> Client4-v3"
        }),
      mpcalRunDef(
        "Replica(2)",
        List("Replica(2)").asJava,
        strInputStream {
          "Replica snapshot:\n" +
            "\ta -> Client3-v1\n" +
            "\tb -> Client3-v2\n" +
            "\tc -> Client3-v3\n" +
            "\td -> Client4-v2\n" +
            "\te -> Client4-v3"
        })))

  // Concurrent replicated key-value store: each client is given a list of
  // operations, and they perform them concurrently (different Go routine for
  // each operation). Since the client's output is non-deterministic, we only
  // verify the output of the replica at the end of the process, guaranteeing
  // that they are all consistent and equal.
  check("concurrent_replicated_kv")(
    specName = "concurrent_replicated_kv",
    pack = "replicated_kv",
    constants = Map(
      "DISCONNECT_MSG" -> "\"disconnect\"",
      "GET_MSG" -> "\"get\"",
      "PUT_MSG" -> "\"put\"",
      "NULL_MSG" -> "\"clock_update\"",
      "NUM_CLIENTS" -> "3",
      "NUM_REPLICAS" -> "2",
      "GET_RESPONSE" -> "\"get_response\"",
      "PUT_RESPONSE" -> "\"put_response\""),
    processes = List(
      mpcalRunDef(
        "Replica(0)",
        List("Replica(0)").asJava,
        fileInputStream("concurrent_replicated_kv", "replicas_out.txt")),
      mpcalRunDef(
        "Replica(1)",
        List("Replica(1)").asJava,
        fileInputStream("concurrent_replicated_kv", "replicas_out.txt")),
      mpcalRunDef(
        "Client(2)",
        List("Client(2)").asJava,
        Paths.get(
          "test", "mpcal", "go", "concurrent_replicated_kv", "client2_in.txt"
        ).toFile(),
        strInputStream("")),
      mpcalRunDef(
        "Client(3)",
        List("Client(3)").asJava,
        Paths.get(
          "test", "mpcal", "go", "concurrent_replicated_kv", "client3_in.txt"
        ).toFile(),
        strInputStream("")),
      mpcalRunDef(
        "Client(4)",
        List("Client(4)").asJava,
        Paths.get(
          "test", "mpcal", "go", "concurrent_replicated_kv", "client4_in.txt"
        ).toFile(),
        strInputStream(""))))
}
