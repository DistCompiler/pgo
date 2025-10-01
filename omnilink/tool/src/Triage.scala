package omnilink

import scala.collection.mutable

import org.rogach.scallop.Subcommand
import pgo.util.ArgUtils.given
import pgo.util.TLAExprInterpreter
import pgo.PGo
import pgo.model.tla.TLAOperatorDefinition
import pgo.util.TLAExprInterpreter.TLAValueBool
import pgo.model.tla.*
import pgo.util.ById
import pgo.util.TLAExprInterpreter.TLAValueString

trait Triage:
  triage: Subcommand =>
  
  val mcSpecFile = trailArg[os.Path](
    descr = "the model checking spec file containing __TAG_ prefixed definitions",
    required = true,
  )
  val traceFile = trailArg[os.Path](
    descr = "the file (in binary TLC trace exploration format) to triage",
    required = true,
  )

  def run(): Unit =
    val tlaModule = PGo.parseTLA(mcSpecFile())
    val traceTLA = TLAExprInterpreter.TLAValue.parseFromTLCBinFmtGZIP(os.read.stream(traceFile()))
    val trace = traceTLA.asVector.view.reverse

    val stalledOperations = trace.head("__successors").asMap.values.toList

    val tagDefs = tlaModule.units
      .collect:
        case TLAOperatorDefinition(name, args, body, false) if name.stringRepr.startsWith("__TAG_") =>
          require(args.size == 2, s"${name.stringRepr} needs 2 argument, had ${args.size}")
          (name.stringRepr, args, body)

    val pidsToExplain = stalledOperations.map(_("pid")).to(mutable.ListBuffer)

    tagDefs
      .view
      .flatMap: tpl =>
        stalledOperations.view.map(tpl :* _)
      .filter: (tagName, args, expr, stalledOp) =>
        trace
          .takeWhile: action =>
            action("__successors").get(stalledOp("pid")) == Some(stalledOp)
          .forall: action =>
            val env: TLAExprInterpreter.Env = tlaModule
              .moduleDefinitions(captureLocal = true)
              .collect:
                case defn @ TLADefiningIdentifier(id) if action.asMap.contains(TLAValueString(id.id)) =>
                  defn.canonicalIdString -> action(id.id)
              .toMap
              ++ Map(
                args(0).canonicalIdString -> stalledOp("pid"),
                args(1).canonicalIdString -> stalledOp,
              )
            try
              TLAExprInterpreter.interpret(expr)(using env) match
                case TLAValueBool(true) =>
                  pidsToExplain.filterInPlace(_ != stalledOp("pid"))
                  true
                case TLAValueBool(false) =>
                  false
                case badVal => throw RuntimeException(s"__TAG_ definition $tagName evaluated should have produced a boolean, got $badVal")
            catch
              case exn: TLAExprInterpreter.Unsupported =>
                exn.describe.linesIterator.foreach(println)
                exn.printStackTrace()
                System.exit(1); ???
              case exn: TLAExprInterpreter.TypeError =>
                exn.describe.linesIterator.foreach(println)
                exn.printStackTrace()
                System.exit(1); ???
      .foreach: (tagName, _, _, stalledOp) =>
        println(s"$tagName(${stalledOp("pid")})")
    pidsToExplain.foreach: pid =>
      println(s"unexplained($pid)")
  end run
end Triage
