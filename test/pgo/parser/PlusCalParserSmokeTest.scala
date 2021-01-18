package pgo.parser

import org.scalatest.funsuite.AnyFunSuite

import java.io.RandomAccessFile
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import java.nio.file.Paths
import scala.util.Using

class PlusCalParserSmokeTest extends AnyFunSuite{
  val fileNames = List(
    "Euclid",
    "QueensPluscal",
    "TwoPhaseCommit",
    "AltBitProtocol",
    "Sum",
    "Await",
    "FastMutex",
    "pgo2pc",
  )

  fileNames.foreach { fileName =>
    test(fileName) {
      val inputFilePath = Paths.get("test", "pluscal", s"$fileName.tla")
      Using.Manager { use =>
        val file = use(new RandomAccessFile(inputFilePath.toFile, "r"))
        val fileChannel = use(file.getChannel)
        val buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size)
        // assume UTF-8, though technically TLA+ is ASCII only according to the book
        val charSeq = StandardCharsets.UTF_8.decode(buffer)

        // basic smoke test, ensure that we at least seem to parse all our example files correctly
        val tlaModule = TLAParser.readModuleBeforeTranslation(inputFilePath, charSeq)
        PlusCalParser.readAlgorithm(inputFilePath, StandardCharsets.UTF_8.decode(buffer), tlaModule)
      }
    }
  }
}
