package pgo.formatters

import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite
import pgo.model.tla.TLABuilder._
import pgo.model.tla.TLAModule
import pgo.parser.TLAParser

import java.nio.file.{Path, Paths}
import java.util
import java.util.{Arrays, Collections}

class TLANodePrintEquivalenceTest extends AnyFunSuite {

  def check(tag: String)(tlaModule: TLAModule)(implicit pos: Position): Unit =
    test(tag) {
      val str = tlaModule.toString
      val testPath = Paths.get("TEST")
      val actual = TLAParser.readModule(testPath, str)
      assert(actual == tlaModule)
    }

  check("extends but no operators") {
    module("TEST", ids(id("Naturals"), id("TLC")), Collections.emptyList)
  }
  check("empty module") {
    module("TEST", ids(), Collections.emptyList)
  }
  check("one operator") {
    module(
      "TEST",
      ids(id("Sequences")),
      util.Arrays.asList(
        opdef(false, id("foo"), opdecls(opdecl(id("a")), opdecl(id("b"))), num(1))))
  }

}
