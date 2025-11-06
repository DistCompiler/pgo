package omnilink

import scala.collection.mutable

import org.rogach.scallop.Subcommand

import pgo.PGo
import pgo.model.tla.*
import pgo.model.{Definition, PGoError, SourceLocation}
import pgo.util.ArgUtils.given
import pgo.util.Description

import Description.toDescription

trait GenHPP:
  genHPP: Subcommand =>

  val specFile = trailArg[os.Path](
    descr = "the TLA+ specification to operate on",
    required = true,
  )
  val outFile =
    opt[os.Path](
      descr = "the .hpp file to generate (defaults to SpecName.hpp)",
      required = false,
      default =
        Some(specFile() / os.up / s"${specFile().last.stripSuffix(".tla")}.hpp"),
    )

  def run(): Unit =
    val tlaModule = PGo.parseTLA(specFile())
    val caseList = GenHPP.gatherCaseList(tlaModule)

    val caseStructs = caseList.view
      .map: (name, members) =>
        s"""
           |struct $name {
           |    static constexpr std::string_view _name_ = "$name";
           |    omnilink::Packable ${members.mkString(", ")};
           |    bool _did_abort = false;
           |    uint64_t _op_start = 0, _op_end = 0;
           |    omnilink::Packable _meta;
           |    MSGPACK_DEFINE_MAP(${members.mkString(
            ", ",
          )}, _did_abort, _op_start, _op_end, _meta);
           |};""".stripMargin

    val output =
      s"""
         |#pragma once
         |
         |#include <string_view>
         |#include <variant>
         |#include <msgpack.hpp>
         |#include <omnilink/workload.hpp>
         |
         |namespace ${tlaModule.name.id} {
         |${caseStructs.mkString("\n")}
         |
         |using AnyOperation = std::variant<${caseList.view
          .map(_._1)
          .mkString("\n    ", "\n    , ", "\n")}>;
         |};
         |
         |template<>
         |struct omnilink::pretty_name_of<${tlaModule.name.id}::AnyOperation> {
         |    static constexpr std::string_view value = "${tlaModule.name.id}";
         |};
         |
    """.stripMargin

    os.write.over(outFile(), output)
  end run
end GenHPP

object GenHPP:
  final case class WorkloadGenError(
      msg: String,
      sourceLocation: SourceLocation = SourceLocation.unknown,
  ) extends PGoError:
    def errors: List[PGoError.Error] =
      List(WorkloadGenError.Error(msg, sourceLocation))
  end WorkloadGenError
  object WorkloadGenError:
    final case class Error(msg: String, sourceLocation: SourceLocation)
        extends PGoError.Error:
      def description: Description = msg.toDescription
  end WorkloadGenError

  def gatherCaseList(tlaModule: TLAModule): List[(String, List[String])] =
    val nextDefn = tlaModule
      .moduleDefinitions(captureLocal = true)
      .collect:
        case defn: TLAOperatorDefinition
            if defn.identifier == Definition.ScopeIdentifierName(
              TLAIdentifier("Next"),
            ) && defn.args.isEmpty =>
          defn
      .toList match
      case List(defn) => defn
      case _          => throw WorkloadGenError("Next definition not found")

    val casesAcc = mutable.ListBuffer[(String, List[String])]()

    val builtinOr = BuiltinModules.Intrinsics.membersMap(
      Definition.ScopeIdentifierSymbol(TLASymbol(TLASymbol.LogicalOrSymbol)),
    )

    def impl(expr: TLAExpression): Unit =
      expr match
        case TLAGeneralIdentifier(name, prefix) =>
          casesAcc += ((name.id, Nil))
        case call @ TLAOperatorCall(name, Nil, arguments)
            if call.refersTo == builtinOr =>
          arguments.foreach(impl)
        case op @ TLAOperatorCall(
              name: Definition.ScopeIdentifierName,
              Nil,
              arguments,
            ) =>
          casesAcc += ((
            name.name.id,
            op.refersTo
              .asInstanceOf[TLAOperatorDefinition]
              .args
              .map(_.identifier.stringRepr),
          ))
        case TLALet(defs, body) =>
          impl(body)
        case TLAQuantifiedExistential(bounds, body) =>
          impl(body)
        case TLAQuantifiedUniversal(bounds, body) =>
          impl(body)
        case expr =>
          throw WorkloadGenError("unrecognized pattern", expr.sourceLocation)
    end impl

    impl(nextDefn.body)
    casesAcc.result()
  end gatherCaseList
end GenHPP
