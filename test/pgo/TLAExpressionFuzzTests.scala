package pgo

import pgo.util.TLAExpressionFuzzTestUtils

class TLAExpressionFuzzTests
    extends munit.FunSuite
    with TLAExpressionFuzzTestUtils {
  // ignore: TODO, fix mismatches between lazy evaluation in interpreter vs Go
  // test("TLA+ expr eval (true random ASTs)") {
  //   val result = runExpressionFuzzTesting()
  //   withClue(pprint.apply(result)) {
  //     assert(result.success)
  //   }
  // }
}
