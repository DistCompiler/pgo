package pgo.tracing

import pgo.model.tla.TLAModule
import pgo.model.Definition
import pgo.model.PGoError
import pgo.util.Description
import pgo.util.Description.toDescription
import pgo.model.SourceLocation
import pgo.model.tla.*

import scala.collection.mutable

object WorkloadGen:
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

  def apply(tlaFile: os.Path, tlaModule: TLAModule, outFile: os.Path): Unit =
    val caseList = gatherCaseList(tlaModule)

    val caseStructs = caseList.view
      .map: (name, members) =>
        s"""
          |struct $name {
          |    static constexpr std::string_view _name_ = "$name";
          |    msgpack::object ${members.mkString(", ")};
          |    MSGPACK_DEFINE_MAP(${members.mkString(", ")});
          |};"""

    val output = s"""
                    |#pragma once
                    |
                    |#include <string_view>
                    |#include <msgpack.hpp>
                    |
                    |namespace ${tlaModule.name.id} {
                    |${caseStructs.mkString("\n")}
                    |
                    |using AnyOperation = std::variant<${caseList.view
                     .map(_._1)
                     .mkString("\n    ", "\n    , ", "\n")}>;
                    |};
    """.stripMargin

    os.write.over(outFile, output)
  end apply
end WorkloadGen
