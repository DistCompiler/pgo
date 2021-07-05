package pgo.util

import pgo.model.Definition
import pgo.model.tla.BuiltinModules.TLABuiltinOperator
import pgo.model.tla._

import scala.annotation.tailrec

object TLAExprInterpreter {
  sealed abstract class TLAValue
  final case class TLAValueBool(value: Boolean) extends TLAValue
  final case class TLAValueNumber(value: Int) extends TLAValue
  final case class TLAValueString(value: String) extends TLAValue
  final case class TLAValueSet(value: Set[TLAValue]) extends TLAValue
  final case class TLAValueTuple(value: List[TLAValue]) extends TLAValue
  final case class TLAValueFunction(value: Map[TLAValue,TLAValue]) extends TLAValue

  lazy val builtinOperators: IdMap[TLABuiltinOperator,List[TLAValue]=>TLAValue] = IdMap.empty

  def interpret(expr: TLAExpression)(implicit env: Map[String,TLAValue]): TLAValue =
    expr match {
      case TLAString(value) => TLAValueString(value)
      case TLANumber(value, _) =>
        value match {
          case TLANumber.IntValue(value) => TLAValueNumber(value.intValue)
        }
      case TLAGeneralIdentifier(name, prefix) =>
        assert(prefix.isEmpty)
        env(name.id)
      case TLADot(lhs, identifier) =>
        interpret(lhs) match {
          case TLAValueFunction(value) => value(identifier.id)
        }
      case opcall@TLAOperatorCall(_, _, arguments) =>
        opcall.refersTo match {
          case builtin: BuiltinModules.TLABuiltinOperator =>
            builtinOperators(builtin)(arguments.map(interpret))
          case TLAOperatorDefinition(_, args, body, _) =>
            assert(args.size == arguments.size)
            assert(args.forall(_.variant.isInstanceOf[TLAOpDecl.NamedVariant]))
            val argNames = args.view.map(_.variant.asInstanceOf[TLAOpDecl.NamedVariant].ident.id)
            val argValues = arguments.map(interpret)
            interpret(body)(env = env ++ (argNames zip argValues))
        }
      case TLAIf(cond, tval, fval) =>
        interpret(cond) match {
          case TLAValueBool(value) =>
            if(value) interpret(tval) else interpret(fval)
        }
      case TLALet(defs, body) =>
        @tailrec
        def impl(defs: List[TLAUnit])(implicit env: Map[String,TLAValue]): TLAValue =
          defs match {
            case Nil => interpret(body)
            case unit :: restUnits =>
              unit match {
                case TLAOperatorDefinition(name, args, body, _) if args.isEmpty =>
                  val strName = name match {
                    case Definition.ScopeIdentifierName(name) => name.id
                    case Definition.ScopeIdentifierSymbol(symbol) => symbol.symbol.stringReprDefn
                  }
                  impl(restUnits)(env = env.updated(strName, interpret(body)))
                case _: TLAOperatorDefinition =>
                  // for definitions with args, they will be called by TLAOperatorCall, and scoping is done already
                  impl(restUnits)
              }
          }

        impl(defs)
      case TLACase(arms, other) =>
        @tailrec
        def armEval(arms: List[TLACaseArm]): TLAValue =
          arms match {
            case Nil => other match {
              case Some(value) => interpret(value)
            }
            case TLACaseArm(cond, result) :: otherArms =>
              interpret(cond) match {
                case TLAValueBool(value) =>
                  if(value) {
                    interpret(result)
                  } else {
                    armEval(otherArms)
                  }
              }
          }

        armEval(arms)
      case TLAFunction(args, body) =>
        def impl(args: List[TLAQuantifierBound], acc: List[TLAValue])(implicit env: Map[String,TLAValue]): Iterator[(TLAValue,TLAValue)] =
          args match {
            case Nil => Iterator.single(TLAValueTuple(acc) -> interpret(body))
            case TLAQuantifierBound(tpe, ids, set) :: restArgs =>
              interpret(set) match {
                case TLAValueSet(setValue) =>
                  tpe match {
                    case TLAQuantifierBound.IdsType =>
                      val List(id) = ids
                      setValue.iterator.flatMap { v =>
                        impl(restArgs, acc :+ v)(env = env.updated(id.id.id, v))
                      }
                    case TLAQuantifierBound.TupleType =>
                      setValue.iterator.flatMap {
                        case v@TLAValueTuple(elems) =>
                          assert(elems.size == ids.size)
                          impl(restArgs, acc :+ v)(env = env ++ (ids.view.map(_.id.id) zip elems))
                      }
                  }
              }
          }

        TLAValueFunction(impl(args, Nil).toMap)
      case TLAFunctionCall(function, params) =>
        val paramValue = params match {
          case List(singleParam) => interpret(singleParam)
          case params => TLAValueTuple(params.map(interpret))
        }
        interpret(function) match {
          case TLAValueTuple(value) =>
            paramValue match {
              case TLAValueNumber(idx) => value(idx)
            }
          case TLAValueFunction(value) => value(paramValue)
        }
      case TLAFunctionSet(from, to) =>
        (interpret(from), interpret(to)) match {
          case (TLAValueSet(fromSet), TLAValueSet(toSet)) =>
            TLAValueSet {
              val keyList = fromSet.toList
              val valueList = toSet.toList
              val valueSets = keyList.iterator.foldLeft(Iterator.single(Nil: List[TLAValue])) { (acc, _) =>
                acc.flatMap(lst => valueList.iterator.map(v => v :: lst))
              }
              valueSets.map(valueSet => TLAValueFunction((keyList zip valueSet).toMap)).toSet
            }
        }
      case TLAFunctionSubstitution(source, substitutions) =>
        substitutions.foldLeft(interpret(source)) { (fnValue, sub) =>
          val TLAFunctionSubstitutionPair(_, keys, value) = sub
          def subKeys(keys: List[TLAFunctionSubstitutionKey], origValue: TLAValue): TLAValue =
            keys match {
              case Nil => interpret(value)(env = env.updated("@", origValue))
              case TLAFunctionSubstitutionKey(indices) :: restKeys =>
                val indexValue = indices match {
                  case List(index) => interpret(index)
                  case indices => TLAValueTuple(indices.map(interpret))
                }
                origValue match {
                  case TLAValueFunction(origFn) =>
                    TLAValueFunction(origFn.updated(indexValue, subKeys(restKeys, origFn(indexValue))))
                }
            }

          subKeys(keys, fnValue)
        }
      case TLAFunctionSubstitutionAt() => env("@")
      case TLAQuantifiedExistential(bounds, body) =>
        def impl(bounds: List[TLAQuantifierBound])(implicit env: Map[String,TLAValue]): TLAValue =
          bounds match {
            case Nil => interpret(body)
            case TLAQuantifierBound(tpe, ids, set) :: restBounds =>
              val setValue = interpret(set)
              tpe match {
                case TLAQuantifierBound.IdsType =>
                  val List(id) = ids
                  setValue match {
                    case TLAValueSet(setValue) =>
                      TLAValueBool(setValue.exists { v =>
                        impl(restBounds)(env = env.updated(id.id.id, v)) match {
                          case TLAValueBool(value) => value
                        }
                      })
                  }
                case TLAQuantifierBound.TupleType =>
                  setValue match {
                    case TLAValueSet(setValue) =>
                      TLAValueBool(setValue.exists {
                        case TLAValueTuple(elems) =>
                          assert(elems.size == ids.size)
                          impl(restBounds)(env = env ++ (ids.view.map(_.id.id) zip elems)) match {
                            case TLAValueBool(value) => value
                          }
                      })
                  }
              }
          }

        impl(bounds)
      case TLAQuantifiedUniversal(bounds, body) =>
        def impl(bounds: List[TLAQuantifierBound])(implicit env: Map[String,TLAValue]): TLAValue =
          bounds match {
            case Nil => interpret(body)
            case TLAQuantifierBound(tpe, ids, set) :: restBounds =>
              val setValue = interpret(set)
              tpe match {
                case TLAQuantifierBound.IdsType =>
                  val List(id) = ids
                  setValue match {
                    case TLAValueSet(setValue) =>
                      TLAValueBool(setValue.forall { v =>
                        impl(restBounds)(env = env.updated(id.id.id, v)) match {
                          case TLAValueBool(value) => value
                        }
                      })
                  }
                case TLAQuantifierBound.TupleType =>
                  setValue match {
                    case TLAValueSet(setValue) =>
                      TLAValueBool(setValue.forall {
                        case TLAValueTuple(elems) =>
                          assert(elems.size == ids.size)
                          impl(restBounds)(env = env ++ (ids.view.map(_.id.id) zip elems)) match {
                            case TLAValueBool(value) => value
                          }
                      })
                  }
              }
          }

        impl(bounds)
      case TLASetConstructor(contents) =>
        TLAValueSet(contents.view.map(interpret).toSet)
      case TLASetRefinement(TLAQuantifierBound(tpe, ids, set), when) =>
        interpret(set) match {
          case TLAValueSet(setValue) =>
            tpe match {
              case TLAQuantifierBound.IdsType =>
                val List(id) = ids
                TLAValueSet(setValue.filter { v =>
                  interpret(when)(env = env.updated(id.id.id, v)) match {
                    case TLAValueBool(value) => value
                  }
                })
              case TLAQuantifierBound.TupleType =>
                TLAValueSet(setValue.filter {
                  case TLAValueTuple(elems) =>
                    assert(elems.size == ids.size)
                    interpret(when)(env = env ++ (ids.view.map(_.id.id) zip elems)) match {
                      case TLAValueBool(value) => value
                    }
                })
            }
        }
      case TLASetComprehension(body, bounds) =>
        def impl(bounds: List[TLAQuantifierBound])(implicit env: Map[String,TLAValue]): Iterator[TLAValue] =
          bounds match {
            case Nil => Iterator.single(interpret(body))
            case TLAQuantifierBound(tpe, ids, set) :: restBounds =>
              interpret(set) match {
                case TLAValueSet(setValue) =>
                  tpe match {
                    case TLAQuantifierBound.IdsType =>
                      val List(id) = ids
                      setValue.iterator.flatMap { v =>
                        impl(restBounds)(env = env.updated(id.id.id, v))
                      }
                    case TLAQuantifierBound.TupleType =>
                      setValue.iterator.flatMap {
                        case TLAValueTuple(elems) =>
                          assert(ids.size == elems.size)
                          impl(restBounds)(env = env ++ (ids.view.map(_.id.id) zip elems))
                      }
                  }
              }
          }

        TLAValueSet(impl(bounds).toSet)
      case TLATuple(elements) =>
        TLAValueTuple(elements.map(interpret))
      case TLARecordConstructor(fields) =>
        TLAValueFunction(fields.view.map {
          case TLARecordConstructorField(name, value) =>
            TLAValueString(name.id) -> interpret(value)
        }.toMap)
      case TLARecordSet(fields) =>
        def impl(fields: List[TLARecordSetField], acc: Map[TLAValue,TLAValue]): Iterator[TLAValue] =
          fields match {
            case Nil => Iterator.single(TLAValueFunction(acc))
            case TLARecordSetField(name, set) :: restFields =>
              interpret(set) match {
                case TLAValueSet(setValue) =>
                  setValue.iterator.flatMap { v =>
                    impl(restFields, acc.updated(name.id, v))
                  }
              }
          }

        TLAValueSet(impl(fields, Map.empty).toSet)
    }
}
