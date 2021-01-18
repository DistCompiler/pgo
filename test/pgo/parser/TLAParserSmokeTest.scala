package pgo.parser

import org.scalatest.funsuite.AnyFunSuite

import java.io.RandomAccessFile
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}
import scala.util.Using

trait TLAParserSmokeTestBase extends AnyFunSuite {
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
  def checkFor(path: java.nio.file.Path, charSequence: CharSequence): Unit

  fileNames.foreach { fileName =>
    test(fileName) {
      val inputFilePath = Paths.get("test", "pluscal", fileName + ".tla")
      Using.Manager { use =>
        val fileChannel = use(use(new RandomAccessFile(inputFilePath.toFile, "r")).getChannel)
        val buffer = fileChannel.map(FileChannel.MapMode.READ_ONLY, 0, fileChannel.size)
        val charSeq = StandardCharsets.UTF_8.decode(buffer)

        checkFor(inputFilePath, charSeq)
      }
    }
  }
}

class BeforeTranslationTLAParserSmokeTest extends TLAParserSmokeTestBase {
  override def checkFor(path: Path, charSequence: CharSequence): Unit =
    TLAParser.readModuleBeforeTranslation(path, charSequence)
}

class WholeModuleTLAParserSmokeTest extends TLAParserSmokeTestBase {
  override def checkFor(path: Path, charSequence: CharSequence): Unit =
    TLAParser.readModule(path, charSequence)
}
