package pgo

import mainargs.{ParserForMethods, main}
import org.scalacheck.rng.Seed
import pgo.util.TLAExpressionFuzzTestUtils

object Commands extends TLAExpressionFuzzTestUtils {
  @main
  def fuzzWithSeed(seed: String): Unit = {
    val result = runExpressionFuzzTesting(seed = Seed.fromBase64(seed).get)
    if(result.success) {
      println("passed!")
    } else {
      println("failed!")
    }
    pprint.pprintln(result)
  }

  @main
  def fuzzIndefinitely(): Unit = {

    runExpressionFuzzTesting()

  }

  def main(args: Array[String]): Unit =
    ParserForMethods(this).runOrExit(args = args)
}
