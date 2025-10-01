package pgo.trans

import scala.collection.View

import pgo.model.mpcal.*
import pgo.model.pcal.*
import pgo.model.tla.*
import pgo.util.{!!!, Description}

import Description.*
import TLARenderPass.*

object PCalRenderPass {
  def describeStatement(stmt: PCalStatement): Description =
    stmt match {
      case PCalExtensionStatement(MPCalCall(target, arguments)) =>
        d"call ${target.id}(${arguments.view
            .map {
              case Left(MPCalRefExpr(name, mappingCount)) =>
                d"ref ${name.id}${View.fill(mappingCount)(d"[_]").flattenDescriptions}"
              case Right(expr) => describeExpr(expr)
            }
            .separateBy(d", ")})"
      case PCalAssert(condition) =>
        d"assert ${describeExpr(condition)}"
      case PCalAssignment(pairs) =>
        def describeLhs(lhs: PCalAssignmentLhs): Description =
          lhs match {
            case PCalAssignmentLhsIdentifier(identifier) =>
              identifier.id.toDescription
            case PCalAssignmentLhsProjection(lhs, projections) =>
              d"${describeLhs(lhs)}[${projections.view.map(describeExpr).separateBy(d", ")}]"
            case PCalAssignmentLhsExtension(MPCalDollarVariable()) =>
              d"$$variable"
            case PCalAssignmentLhsExtension(contents) =>
              d"?? ${contents.toString} ??"
          }

        pairs.view
          .map { case PCalAssignmentPair(lhs, rhs) =>
            d"${describeLhs(lhs)} := ${describeExpr(rhs)}"
          }
          .separateBy(d" || ")
      case PCalAwait(condition) =>
        d"await ${describeExpr(condition)}"
      case PCalCall(target, arguments) =>
        d"call ${target.id}(${arguments.view.map(describeExpr).separateBy(d", ")})"
      case PCalEither(cases) =>
        d"either ${cases.view
            .map { block =>
              d"{\n${describeStatements(block).indented}\n}"
            }
            .separateBy(d" or ")}"
      case PCalGoto(target) =>
        d"goto $target"
      case PCalIf(condition, yes, no) =>
        d"if (${describeExpr(condition)}) {\n${describeStatements(yes).indented}\n}${
            if (no.nonEmpty) {
              d" else {\n${describeStatements(no).indented}\n}"
            } else d""
          }"
      case PCalLabeledStatements(label, statements) =>
        d"${label.name}${label.modifier match {
            case PCalLabel.PlusModifier  => d"-"
            case PCalLabel.MinusModifier => d"+"
            case PCalLabel.NoModifier    => d""
          }}:\n${describeStatements(statements, tailSemicolon = false).indented}"
      case PCalMacroCall(target, arguments) =>
        d"${target.id}(${arguments.view.map(describeExpr).separateBy(d", ")})"
      case PCalPrint(value) =>
        d"print ${describeExpr(value)}"
      case PCalReturn() => d"return"
      case PCalSkip()   => d"skip"
      case PCalWhile(condition, body) =>
        d"while (${describeExpr(condition)}) {\n${describeStatements(body).indented}\n}"
      case PCalWith(variables, body) =>
        val bodyDesc = d"{\n${describeStatements(body).indented}\n}"
        if (variables.size > 1) {
          d"with (${variables.view
              .map { decl =>
                d"\n${describeVarDecl(decl)}"
              }
              .separateBy(d", ")
              .indented}\n) $bodyDesc"
        } else {
          d"with (${variables.view.map(describeVarDecl).separateBy(d", ")}) $bodyDesc"
        }
      case PCalExtensionStatement(_) => !!!
    }

  def describeStatements(
      stmts: List[PCalStatement],
      tailSemicolon: Boolean = true,
  ): Description =
    if (tailSemicolon) {
      stmts.view
        .map(stmt => d"${describeStatement(stmt)};".ensureLineBreakBefore)
        .flattenDescriptions
    } else {
      stmts.view
        .map(stmt => d"${describeStatement(stmt)}".ensureLineBreakBefore)
        .separateBy(d";")
    }

  def describeVarDecl(varDecl: PCalVariableDeclaration): Description =
    varDecl match {
      case PCalVariableDeclarationEmpty(name) => name.id.toDescription
      case PCalVariableDeclarationValue(name, value) =>
        d"${name.id} = ${describeExpr(value)}"
      case PCalVariableDeclarationSet(name, set) =>
        d"${name.id} \\in ${describeExpr(set)}"
    }

  def apply(pcalAlgorithm: PCalAlgorithm): Description = {
    val PCalAlgorithm(
      fairness,
      name,
      variables,
      units,
      macros,
      procedures,
      processes,
    ) = pcalAlgorithm

    val header = fairness match {
      case PCalFairness.Unfair   => d"--algorithm"
      case PCalFairness.WeakFair => d"--fair algorithm"
      case PCalFairness.StrongFair =>
        d"--fair+ algorithm" // TODO: is this correct? we can't parse this
    }

    d"$header ${name.id} {${
        if (variables.nonEmpty) {
          d"\nvariables${variables.view.map { decl =>
              d" ${describeVarDecl(decl)};"
            }.flattenDescriptions}".indented
        } else d""
      }${
        if (units.nonEmpty) {
          d"\ndefine{${units.view.map { unit =>
              d"\n${describeUnit(unit)}".indented
            }.flattenDescriptions}\n}".indented
        } else d""
      }${macros.view
        .map { case PCalMacro(name, params, body, _) =>
          d"\n\nmacro ${name.id}(${params.view.map(_.id.id.toDescription).separateBy(d", ")}) {${describeStatements(body).indented}\n}"
        }
        .flattenDescriptions
        .indented}${procedures.view
        .map { case PCalProcedure(name, _, params, variables, body) =>
          d"\n\nprocedure ${name.id}(${params.view
              .map { case PCalPVariableDeclaration(name, value) =>
                d"${name.id}${value.map(v => d" = ${describeExpr(v)}").getOrElse(d"")}"
              }
              .separateBy(d", ")})${
              if (variables.nonEmpty) {
                d"\nvariables${variables.view.map {
                    case PCalPVariableDeclaration(name, value) =>
                      d" ${name.id}${value.map(v => d" = ${describeExpr(v)}").getOrElse(d"")};"
                  }.flattenDescriptions}".indented
              } else d""
            }\n{${describeStatements(body).indented}\n}"
        }
        .flattenDescriptions
        .indented}${processes match {
        case Left(statements) =>
          d"\n{${describeStatements(statements).indented}\n}"
        case Right(processes) =>
          processes.view
            .map { case PCalProcess(selfDecl, fairness, variables, body) =>
              d"\n\n${fairness match {
                  case PCalFairness.Unfair     => d""
                  case PCalFairness.WeakFair   => d"fair "
                  case PCalFairness.StrongFair => d"fair+ "
                }}process (${describeVarDecl(selfDecl)})${
                  if (variables.nonEmpty) {
                    d"\nvariables${variables.view.map { decl =>
                        d" ${describeVarDecl(decl)};"
                      }.flattenDescriptions}".indented
                  } else d""
                }\n{\n${describeStatements(body).indented}\n}"
            }
            .flattenDescriptions
            .indented
      }}\n}"
  }
}
