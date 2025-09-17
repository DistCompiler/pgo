package pgo.trans

import scala.collection.View

import pgo.util.{Description, !!!}
import pgo.util.Description.*
import pgo.model.mpcal.*
import pgo.model.pcal.*
import pgo.model.tla.*
import pgo.model.Definition
import scala.annotation.tailrec
import pgo.model.tla.TLANumber.{
  DecimalSyntax,
  BinarySyntax,
  OctalSyntax,
  HexadecimalSyntax,
}

object TLARenderPass:
  def describeQuantifierBound(qb: TLAQuantifierBound): Description =
    qb.tpe match {
      case TLAQuantifierBound.IdsType =>
        d"${qb.ids.map(_.id.id.toDescription).separateBy(d", ")} \\in ${describeExpr(qb.set)}"
      case TLAQuantifierBound.TupleType =>
        d"<<${qb.ids.map(_.id.id.toDescription).separateBy(d", ")}>> \\in ${describeExpr(qb.set)}"
    }

  def describePrefix(prefix: List[TLAGeneralIdentifierPart]): Description =
    prefix.view.map { case TLAGeneralIdentifierPart(id, parameters) =>
      d"${id.id}(${parameters.view.map(describeExpr).separateBy(d", ")})!"
    }.flattenDescriptions

  def describeExpr(expr: TLAExpression): Description =
    expr match {
      case TLAExtensionExpression(MPCalDollarVariable()) => d"$$variable"
      case TLAExtensionExpression(MPCalDollarValue())    => d"$$value"
      case TLAExtensionExpression(MPCalRefExpr(name, count)) =>
        d"ref ${name.id}${View.fill(count)(d"[_]")}"
      case TLAExtensionExpression(_) => !!!
      case TLAString(value) =>
        d""""${
            @tailrec
            def impl(chars: LazyList[Char], acc: StringBuilder): String =
              chars match {
                case LazyList()    => acc.result()
                case '"' #:: rest  => acc ++= "\\\""; impl(rest, acc)
                case '\t' #:: rest => acc ++= "\\t"; impl(rest, acc)
                case '\n' #:: rest => acc ++= "\\n"; impl(rest, acc)
                case '\f' #:: rest => acc ++= "\\f"; impl(rest, acc)
                case '\r' #:: rest => acc ++= "\\r"; impl(rest, acc)
                case '\\' #:: rest => acc ++= "\\\\"; impl(rest, acc)
                // these two cases account for a lexical bug, whereby placing (* or *) inside a string literal will otherwise break comments in PlusCal
                case '(' #:: '*' #:: rest => acc ++= "(_*"; impl(rest, acc)
                case '*' #:: ')' #:: rest => acc ++= "*_)"; impl(rest, acc)
                case ch #:: rest          => acc += ch; impl(rest, acc)
              }

            impl(value.to(LazyList), acc = new StringBuilder)
          }""""
      case TLANumber(
            value,
            rep,
          ) =>
        val (prefix, radix) = rep match
          case DecimalSyntax     => ("", 10)
          case BinarySyntax      => ("\\b", 2)
          case OctalSyntax       => ("\\o", 8)
          case HexadecimalSyntax => ("\\h", 16)

        value match {
          case TLANumber.IntValue(value) =>
            s"$prefix${value.toString(radix)}".toDescription
          case TLANumber.DecimalValue(value) =>
            value.toString().toDescription
        }
      case TLAGeneralIdentifier(name, prefix) =>
        d"${describePrefix(prefix)}${name.id}"
      case TLADot(lhs, identifier) =>
        d"(${describeExpr(lhs)}).${identifier.id}"
      case TLACrossProduct(operands) =>
        operands.view
          .map(describeExpr)
          .map(desc => d"($desc)")
          .separateBy(d" \\X ")
      case TLAOperatorCall(name, prefix, arguments) =>
        name match {
          case Definition.ScopeIdentifierName(name) =>
            d"${describePrefix(prefix)}${name.id}(${arguments.view.map(describeExpr).separateBy(d", ")})"
          case Definition.ScopeIdentifierSymbol(symbol) =>
            if (symbol.symbol.isPrefix) {
              val List(operand) = arguments
              d"${describePrefix(prefix)}${symbol.symbol.stringReprUsage} (${describeExpr(operand)})"
            } else if (symbol.symbol.isPostfix) {
              val List(operand) = arguments
              d"(${describeExpr(operand)}) ${describePrefix(prefix)}${symbol.symbol.stringReprUsage}"
            } else {
              assert(symbol.symbol.isInfix)
              val List(lhs, rhs) = arguments
              d"(${describeExpr(lhs)}) ${describePrefix(prefix)}${symbol.symbol.stringReprUsage} (${describeExpr(rhs)})"
            }
        }
      case TLAIf(cond, tval, fval) =>
        d"IF ${describeExpr(cond)} THEN ${describeExpr(tval)} ELSE ${describeExpr(fval)}"
      case TLALet(defs, body) =>
        d"LET ${defs.view.map(describeUnit(_).ensureLineBreakAfter).flattenDescriptions.indented} IN ${describeExpr(body)}"
      case TLACase(TLACaseArm(cond1, result1) :: armsRest, other) =>
        // those brackets can be necessary, it's safer to include them. otherwise, nested CASE expressions may steal
        //   each others' clauses
        d"(CASE ${describeExpr(cond1)} -> ${describeExpr(result1)}${armsRest.view
            .map { case TLACaseArm(cond, result) =>
              d"\n[] ${describeExpr(cond)} -> ${describeExpr(result)}"
            }
            .flattenDescriptions
            .indented}${other
            .map { other =>
              d"\n[] OTHER -> ${describeExpr(other)}".indented
            }
            .getOrElse(d"")})"
      case TLACase(_, _) => !!!
      case TLAMaybeAction(body, vars) =>
        d"[${describeExpr(body)}]_${describeExpr(vars)}"
      case TLARequiredAction(body, vars) =>
        d"<<${describeExpr(body)}>>_${describeExpr(vars)}"
      case TLAFairness(kind, vars, expression) =>
        kind match {
          case TLAFairness.StrongFairness =>
            d"SF_${describeExpr(vars)}(${describeExpr(expression)})"
          case TLAFairness.WeakFairness =>
            d"WF_${describeExpr(vars)}(${describeExpr(expression)})"
        }
      case TLAFunction(args, body) =>
        d"[${args.view.map(describeQuantifierBound).separateBy(d", ")} |-> ${describeExpr(body)}]"
      case TLAFunctionCall(function, params) =>
        d"(${describeExpr(function)})[${params.view.map(describeExpr).separateBy(d", ")}]"
      case TLAFunctionSet(from, to) =>
        d"[${describeExpr(from)} -> ${describeExpr(to)}]"
      case TLAFunctionSubstitution(source, substitutions) =>
        d"[${describeExpr(source)} EXCEPT ${substitutions.view
            .map { case TLAFunctionSubstitutionPair(anchor, keys, value) =>
              d"!${keys.view.map { case TLAFunctionSubstitutionKey(indices) =>
                  d"[${indices.view.map(describeExpr).separateBy(d", ")}]"
                }.flattenDescriptions} = ${describeExpr(value)}"
            }
            .separateBy(d", ")}]"
      case TLAFunctionSubstitutionAt() => d"@"
      case TLAQuantifiedExistential(bounds, body) =>
        d"\\E ${bounds.view.map(describeQuantifierBound).separateBy(d", ")} : ${describeExpr(body)}"
      case TLAQuantifiedUniversal(bounds, body) =>
        d"\\A ${bounds.view.map(describeQuantifierBound).separateBy(d", ")} : ${describeExpr(body)}"
      case TLAExistential(ids, body) =>
        d"\\EE ${ids.view.map(_.id.id.toDescription).separateBy(d", ")} : ${describeExpr(body)}"
      case TLAUniversal(ids, body) =>
        d"\\AA ${ids.view.map(_.id.id.toDescription).separateBy(d", ")} : ${describeExpr(body)}"
      case TLASetConstructor(contents) =>
        d"{${contents.view.map(describeExpr).separateBy(d", ")}}"
      case TLASetRefinement(binding, when) =>
        d"{${describeQuantifierBound(binding)} : ${describeExpr(when)}}"
      case TLASetComprehension(body, bounds) =>
        d"{${describeExpr(body)} : ${bounds.view.map(describeQuantifierBound).separateBy(d", ")}}"
      case TLATuple(elements) =>
        d"<<${elements.view.map(describeExpr).separateBy(d", ")}>>"
      case TLARecordConstructor(fields) =>
        if (fields.isEmpty) {
          d"[ ]" // or else this empty case will be parsed as the temporal "always" prefix operator
        } else {
          d"[${fields.view
              .map { case TLARecordConstructorField(name, value) =>
                d"${name.id} |-> ${describeExpr(value)}"
              }
              .separateBy(d", ")}]"
        }
      case TLARecordSet(fields) =>
        if (fields.isEmpty) {
          d"[ ]" // same as above, avoids confusion with temporal "always" operator []
        } else {
          d"[${fields.view
              .map { case TLARecordSetField(name, set) =>
                d"${name.id} : ${describeExpr(set)}"
              }
              .separateBy(d", ")}]"
        }
      case TLAChoose(ids, tpe, body) =>
        tpe match {
          case TLAChoose.Id =>
            val List(id) = ids
            d"CHOOSE ${id.id.id} : ${describeExpr(body)}"
          case TLAChoose.Tuple =>
            d"CHOOSE <<${ids.view.map(_.id.id).map(_.toDescription).separateBy(d", ")}>> : ${describeExpr(body)}"
        }
      case TLAQuantifiedChoose(binding, body) =>
        d"CHOOSE ${describeQuantifierBound(binding)} : ${describeExpr(body)}"
      case TLALambda(idents, body) =>
        d"LAMBDA ${idents.map(_.id.id.toDescription).separateBy(d", ")} : ${describeExpr(body)}"
    }

  def describeOpDecl(opDecl: TLAOpDecl): Description =
    opDecl.variant match {
      case TLAOpDecl.NamedVariant(ident, 0) =>
        ident.id.toDescription
      case TLAOpDecl.NamedVariant(ident, arity) =>
        d"${ident.id}(${View.fill(arity)(d"_").separateBy(d", ")})"
      case TLAOpDecl.SymbolVariant(sym) =>
        if (sym.symbol.isPrefix) {
          d"${sym.symbol.stringReprDefn} _"
        } else if (sym.symbol.isPostfix) {
          d"_ ${sym.symbol.stringReprDefn}"
        } else {
          assert(sym.symbol.isInfix)
          d"_ ${sym.symbol.stringReprDefn} _"
        }
    }

  def describeUnit(unit: TLAUnit, ignoreLocal: Boolean = false): Description =
    unit match {
      case TLARecursive(decls) =>
        d"RECURSIVE ${decls.view.map(_.decl).map(describeOpDecl).separateBy(d", ")}"
      case TLAAssumption(assumption) =>
        d"ASSUME ${describeExpr(assumption)}"
      case TLAConstantDeclaration(constants) =>
        d"CONSTANTS ${constants.view.map(describeOpDecl).separateBy(d", ")}"
      case TLAInstance(moduleName, remappings, isLocal) =>
        d"${if (isLocal && !ignoreLocal) d"LOCAL " else d""}INSTANCE ${moduleName.id}${
            if (remappings.nonEmpty) {
              d" WITH ${remappings.view
                  .map { case TLAInstanceRemapping(from, to) =>
                    from match {
                      case Definition.ScopeIdentifierName(name) =>
                        d"${name.id} <- ${describeExpr(to)}"
                      case Definition.ScopeIdentifierSymbol(symbol) =>
                        d"${symbol.symbol.stringReprDefn} <- ${describeExpr(to)}"
                    }
                  }
                  .separateBy(d", ")}"
            } else d""
          }"
      case TLAModule(name, exts, units) =>
        d"---- MODULE ${name.id} ----${
            if (exts.nonEmpty) {
              d"\nEXTENDS ${exts.view.map(_.id.toDescription).separateBy(d", ")}"
            } else d""
          }${units.view.map(describeUnit(_).ensureLineBreakBefore).flattenDescriptions}\n===="
      case TLAModuleDefinition(name, args, instance, isLocal) =>
        d"${if (isLocal && !ignoreLocal) d"LOCAL " else d""}${name.id}(${args.view.map(describeOpDecl).separateBy(d", ")}) == ${describeUnit(instance)}"
      case TLAOperatorDefinition(
            name: Definition.ScopeIdentifierName,
            Nil,
            TLAFunction(args, body),
            isLocal,
          ) =>
        d"${if (isLocal && !ignoreLocal) d"LOCAL " else d""}${d"${name.name.id}[${args.view.map(describeQuantifierBound).separateBy(d", ")}] == ${describeExpr(body)}"}"
      case TLAOperatorDefinition(name, args, body, isLocal) =>
        d"${if (isLocal && !ignoreLocal) d"LOCAL " else d""}${name match {
            case Definition.ScopeIdentifierName(name) if args.isEmpty =>
              d"${name.id} == ${describeExpr(body)}"
            case Definition.ScopeIdentifierName(name) =>
              d"${name.id}(${args.view.map(describeOpDecl).separateBy(d", ")}) == ${describeExpr(body)}"
            case Definition.ScopeIdentifierSymbol(symbol) =>
              if (symbol.symbol.isPrefix) {
                val List(TLAOpDecl(TLAOpDecl.NamedVariant(id, 0))) = args: @unchecked
                d"${symbol.symbol.stringReprDefn} ${id.id} == ${describeExpr(body)}"
              } else if (symbol.symbol.isPostfix) {
                val List(TLAOpDecl(TLAOpDecl.NamedVariant(id, 0))) = args: @unchecked
                d"${id.id} ${symbol.symbol.stringReprDefn} == ${describeExpr(body)}"
              } else {
                assert(symbol.symbol.isInfix)
                val List(TLAOpDecl(TLAOpDecl.NamedVariant(idLhs, 0)), TLAOpDecl(TLAOpDecl.NamedVariant(idRhs, 0))) = args: @unchecked
                d"${idLhs.id} ${symbol.symbol.stringReprDefn} ${idRhs.id} == ${describeExpr(body)}"
              }
          }}"
      case TLATheorem(theorem) =>
        d"THEOREM ${describeExpr(theorem)}"
      case TLAVariableDeclaration(variables) =>
        d"VARIABLES ${variables.view.map(_.id.id.toDescription).separateBy(d", ")}"
    }
end TLARenderPass
