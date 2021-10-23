package pgo

import org.scalatest.funsuite.AnyFunSuite
import pgo.util.TLAExpressionFuzzTestUtils

class TLAExpressionFuzzTests extends AnyFunSuite with TLAExpressionFuzzTestUtils {
  test("TLA+ expr eval (true random ASTs)") {
    val result = runExpressionFuzzTesting()
    withClue(pprint.apply(result)) {
      assert(result.success)
    }
  }
}
