package pgo.trans

import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, SourceLocation, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.{ById, Description, NameCleaner}
import Description._
import pgo.model.tla.BuiltinModules.{TLABuiltinOperator, builtinModules}
import pgo.util.MPCalPassUtils.MappedRead
import pgo.util.Unreachable.!!!

import java.util.Locale
import scala.annotation.tailrec
import scala.collection.{View, mutable}

object MPCalGoCodegenPass {
  final case class UnsupportedOperationsError(override val errors: List[UnsupportedOperationsError.UnsupportedOperationError]) extends PGoError

  object UnsupportedOperationsError {
    final case class UnsupportedOperationError(override val sourceLocation: SourceLocation) extends PGoError.Error {
      override val description: Description = d"unsupported built-in operator referenced"
    }
  }

  lazy val unsupportedOperators: Set[ById[TLABuiltinOperator]] = View(
    BuiltinModules.Intrinsics.memberAlpha("STRING"),

    BuiltinModules.Intrinsics.memberSym(TLASymbol.PrimeSymbol),
    BuiltinModules.Intrinsics.memberSym(TLASymbol.EnabledSymbol),
    BuiltinModules.Intrinsics.memberSym(TLASymbol.UnchangedSymbol),
    BuiltinModules.Intrinsics.memberSym(TLASymbol.CDotSymbol),

    BuiltinModules.Intrinsics.memberSym(TLASymbol.TLAlwaysSymbol),
    BuiltinModules.Intrinsics.memberSym(TLASymbol.TLEventuallySymbol),
    BuiltinModules.Intrinsics.memberSym(TLASymbol.SequencingSymbol),
    BuiltinModules.Intrinsics.memberSym(TLASymbol.PlusArrowSymbol),

    BuiltinModules.TLC.memberAlpha("Print"),
    BuiltinModules.TLC.memberAlpha("PrintT"),
    BuiltinModules.TLC.memberAlpha("JavaTime"),
    BuiltinModules.TLC.memberAlpha("Permutations"),
    BuiltinModules.TLC.memberAlpha("SortSeq"),

    BuiltinModules.Sequences.memberAlpha("SelectSeq"),

    BuiltinModules.Bags.memberAlpha("IsABag"),
    BuiltinModules.Bags.memberAlpha("BagToSet"),
    BuiltinModules.Bags.memberAlpha("SetToBag"),
    BuiltinModules.Bags.memberAlpha("BagIn"),
    BuiltinModules.Bags.memberAlpha("EmptyBag"),
    BuiltinModules.Bags.memberAlpha("CopiesIn"),
    BuiltinModules.Bags.memberSym(TLASymbol.OPlusSymbol),
    BuiltinModules.Bags.memberSym(TLASymbol.OMinusSymbol),
    BuiltinModules.Bags.memberAlpha("BagUnion"),
    BuiltinModules.Bags.memberSym(TLASymbol.SquareSupersetOrEqualSymbol),
    BuiltinModules.Bags.memberAlpha("SubBag"),
    BuiltinModules.Bags.memberAlpha("BagOfAll"),
    BuiltinModules.Bags.memberAlpha("BagCardinality"),

    BuiltinModules.Peano.memberAlpha("PeanoAxioms"),
    BuiltinModules.Peano.memberAlpha("Succ"),
    BuiltinModules.Peano.memberAlpha("Nat"),

    BuiltinModules.ProtoReals.memberAlpha("IsModelOfReals"),
    BuiltinModules.ProtoReals.memberAlpha("RM"),
    BuiltinModules.ProtoReals.memberAlpha("Real"),
    BuiltinModules.ProtoReals.memberAlpha("Infinity"),
    BuiltinModules.ProtoReals.memberAlpha("MinusInfinity"),
    BuiltinModules.ProtoReals.memberSym(TLASymbol.SlashSymbol),
    BuiltinModules.ProtoReals.memberAlpha("Int"),

    BuiltinModules.Reals.memberAlpha("Real"),
    BuiltinModules.Reals.memberSym(TLASymbol.SlashSymbol),
    BuiltinModules.Reals.memberAlpha("Infinity"),
  ).to(ById.setFactory)

  private val TLAValue = "distsys.TLAValue"
  private val ArchetypeResourceHandle = "distsys.ArchetypeResourceHandle"
  val goKeywords: List[String] =
    """
      |break        default      func         interface    select
      |case         defer        go           map          struct
      |chan         else         goto         package      switch
      |const        fallthrough  if           range        type
      |continue     for          import       return       var
      |""".stripMargin.split(Array(' ', '\n')).view.filter(_.nonEmpty).toList

  sealed abstract class Binding {
    val bind: String
  }
  final case class IndependentCallableBinding(bind: String) extends Binding
  final case class DependentCallableBinding(bind: String) extends Binding
  final case class FixedValueBinding(bind: String) extends Binding
  final case class ResourceBinding(bind: String) extends Binding

  case class GoCodegenContext(nameCleaner: NameCleaner, bindings: Map[ById[RefersTo.HasReferences],Binding] = Map.empty,
                              errOpt: Option[Description] = None,
                              ctxName: String, selfName: String, constantsName: String, constantsTypeName: String,
                              resourceMappingCounts: Map[ById[RefersTo.HasReferences],Int] = Map.empty
                             ) {
    def err: Description = errOpt.get
    def cleanName[T](hint: String)(fn: String => T): T =
      fn(nameCleaner.cleanName(hint))
  }

  def toGoPublicName(id: String): String =
    id.capitalize

  def translateMPCalCallable(callableName: String, selfDeclOpt: Option[TLADefiningIdentifier], params: List[MPCalParam], variables: List[PCalVariableDeclaration], body: List[PCalStatement])(implicit ctx: GoCodegenContext): Description = {
    assert(body.forall(_.isInstanceOf[PCalLabeledStatements]))
    val nameCleaner = ctx.nameCleaner

    val programCounterResourceName = nameCleaner.cleanName("programCounter")
    val err = nameCleaner.cleanName("err")

    val pcalEithers = locally {
      val acc = mutable.ListBuffer.empty[PCalEither]
      body.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
        case either@PCalEither(_) => acc += either
      })
      acc.result()
    }
    val fairnessCounterNames = pcalEithers.view
      .map(either => either -> ctx.nameCleaner.cleanName("fairnessCounter"))
      .to(ById.mapFactory)

    val InitLabelTag = ctx.nameCleaner.cleanName("InitLabelTag")
    val DoneLabelTag = ctx.nameCleaner.cleanName("DoneLabelTag")
    val labelBinds = (body.view.map {
      case PCalLabeledStatements(label, _) =>
        label.name -> s"${ctx.nameCleaner.cleanName(label.name)}LabelTag"
    } ++ List("Done" -> DoneLabelTag)).toMap

    val FirstLabel = labelBinds(body.head.asInstanceOf[PCalLabeledStatements].label.name)

    /**
     * Ensures that any archetype resource reads embedded within expr are lifted out and performed ahead of time.
     * Pure expressions will be unaffected.
     *
     * e.g:
     * `print x + 1`
     * becomes something like
     * `
     * tmp := ctx.Read(...)
     * (tmp + 1).PCalPrint()
     * `
     */
    def readExpr(expr: TLAExpression, hint: String = "resourceRead")(fn: Description=>Description)(implicit ctx: GoCodegenContext): Description = {
      val resourceReads = mutable.ListBuffer[(DefinitionOne,PCalVariableDeclarationEmpty,List[TLAExpression])]()
      lazy val readReplacer: PartialFunction[Rewritable,Rewritable] = {
        case expr@MappedRead(mappingCount, ident) if ctx.resourceMappingCounts.get(ById(ident.refersTo)).contains(mappingCount) =>
          @tailrec
          def findIndices(expr: TLAExpression, acc: mutable.ListBuffer[TLAExpression]): List[TLAExpression] =
            expr match {
              case _: TLAGeneralIdentifier => acc.result()
              case TLAFunctionCall(fn, params) =>
                if(params.size == 1) {
                  acc.prepend(params.head)
                } else {
                  acc.prepend(TLATuple(params))
                }
                findIndices(fn, acc)
            }

          val indices = findIndices(expr, mutable.ListBuffer.empty).map(_.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer))
          val cleanName = ctx.nameCleaner.cleanName(hint)
          val replacementDefn = PCalVariableDeclarationEmpty(TLAIdentifier(cleanName))
          val replacementAST = TLAGeneralIdentifier(TLAIdentifier(cleanName), Nil).setRefersTo(replacementDefn)
          resourceReads += ((ident.refersTo, replacementDefn, indices))
          replacementAST
        case ident@TLAGeneralIdentifier(_, prefix) =>
          assert(prefix.isEmpty)
          ctx.bindings.get(ById(ident.refersTo)) match {
            case Some(ResourceBinding(_)) =>
              val cleanName = ctx.nameCleaner.cleanName(hint)
              val replacementDefn = PCalVariableDeclarationEmpty(TLAIdentifier(cleanName))
              val replacementAST = TLAGeneralIdentifier(TLAIdentifier(cleanName), Nil).setRefersTo(replacementDefn)
              resourceReads += ((ident.refersTo, replacementDefn, Nil))
              replacementAST
            case Some(_) => ident // does not bind a resource; needs no read process
            case _ => ident // an expression-local variable, bound by let or some quantifier. also needs no read process
          }
      }
      val exprWithReads = expr.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer)
      val origCtx = ctx
      locally {
        implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ resourceReads.view.map {
          case (_, replaceDefn, _) => ById(replaceDefn) -> FixedValueBinding(replaceDefn.name.id)
        })
        resourceReads.view.map {
          case (defn, replaceDefn, indices) =>
            d"\nvar ${replaceDefn.name.id} $TLAValue" +
              d"\n${replaceDefn.name.id}, ${ctx.err} = ${ctx.ctxName}.Read(${ctx.bindings(ById(defn)).bind}, []$TLAValue{${indices.view.map(translateExpr)}})" +
              d"\nif ${ctx.err} != nil {${
                d"\ncontinue".indented
              }\n}"
        }.flattenDescriptions +
          fn(translateExpr(exprWithReads))
      }
    }

    /**
     * The plural of readExpr.
     *
     * @param exprs multiple expressions to read
     * @param fn the "body", mapping from a list of bound expression values to a sequence of Go statements
     * @param ctx the context
     * @return the entire sequence of (1) perform expression reads and bindings (2) insert the result of fn(...)
     */
    def readExprs(exprs: List[(TLAExpression,String)])(fn: List[Description]=>Description)(implicit ctx: GoCodegenContext): Description = {
      def impl(exprs: List[(TLAExpression,String)], acc: mutable.ListBuffer[Description]): Description =
        exprs match {
          case Nil => fn(acc.result())
          case (expr, hint) :: restExprs =>
            readExpr(expr, hint = hint) { exprRead =>
              acc.append(exprRead)
              impl(restExprs, acc)
            }
        }

      impl(exprs, mutable.ListBuffer[Description]())
    }

    def commit(body: =>Description)(implicit ctx: GoCodegenContext): Description =
      d"\n${ctx.err} = ${ctx.ctxName}.Commit()" +
        d"\nif ${ctx.err} != nil {${
          d"\ncontinue".indented
        }\n}" +
        body

    def goto(label: String)(implicit ctx: GoCodegenContext): Description =
      d"\n${ctx.err} = ${ctx.ctxName}.Write($programCounterResourceName, []$TLAValue{}, distsys.NewTLANumber($label))" +
        d"\nif ${ctx.err} != nil {${
          d"\ncontinue".indented
        }\n}"

    def impl(stmts: List[PCalStatement], pfxDesc: Description = d"")(implicit ctx: GoCodegenContext): Description =
      stmts match {
        case Nil =>
          d"$pfxDesc\n// no statements"
        case PCalGoto(target) :: Nil =>
          pfxDesc + goto(labelBinds(target)) + commit(d"")
        case PCalReturn() :: Nil =>
          pfxDesc + commit(d"\nreturn nil")
        case PCalExtensionStatement(call@MPCalCall(_, arguments)) :: restStmts =>
          ??? // generate a jump to a separate, synthetic block. this block will have its own PC, and control will
          // go through it to call the procedure. When the procedure returns, that block will take care of executing
          // the correct jump (not considered: tail calls).
          /*val exprArgs = arguments.collect { case Right(expr) => expr }
          val exprArgIndices = exprArgs.view.zipWithIndex.to(IdMap)
          pfxDesc + readExprs(exprArgs) { exprReads =>
            commit {
              val IndependentCallableBinding(nameToCall) = ctx.bindings(call.refersTo)
              d"\n${ctx.err} = $nameToCall(${ctx.constantsName}${
                arguments.map {
                  case Left(ref) => d", ${ctx.bindings(ref.refersTo).bind}"
                  case Right(expr) => d", ${exprReads(exprArgIndices(expr))}"
                }
              })" +
                d"\nif ${ctx.err} != nil {${
                  d"\nreturn err".indented
                }\n}" +
                (restStmts match {
                  case PCalGoto(target) :: Nil =>
                    d"\ngoto $target"
                  case PCalReturn() :: Nil =>
                    d"\nreturn nil"
                })
            }
          }*/
        case stmt :: restStmts =>
          val result = stmt match {
            case PCalAssert(condition) =>
              val conditionExpr = condition
              readExpr(condition, hint = "condition") { condition =>
                d"\nif !$condition.AsBool() {${
                  (d"""\n${ctx.err} = fmt.Errorf("%w: ${
                    escapeStringToGo(PCalRenderPass.describeExpr(conditionExpr).linesIterator.mkString("\n"))
                  }", distsys.ErrAssertionFailed)""" +
                    d"\ncontinue").indented
                }\n}"
              }
            case PCalAssignment(List(PCalAssignmentPair(lhs, rhs))) =>
              @tailrec
              def gatherLhsIndices(lhs: PCalAssignmentLhs, acc: mutable.ListBuffer[TLAExpression]): List[TLAExpression] =
                lhs match {
                  case PCalAssignmentLhsIdentifier(_) => acc.result()
                  case PCalAssignmentLhsProjection(lhs, projections) =>
                    if (projections.size == 1) {
                      acc.prepend(projections.head)
                    } else {
                      acc.prepend(TLATuple(projections))
                    }
                    gatherLhsIndices(lhs, acc)
                  case PCalAssignmentLhsExtension(_) => !!!
                }

              @tailrec
              def findLhsIdent(lhs: PCalAssignmentLhs): PCalAssignmentLhsIdentifier =
                lhs match {
                  case ident: PCalAssignmentLhsIdentifier => ident
                  case PCalAssignmentLhsProjection(lhs, _) => findLhsIdent(lhs)
                  case PCalAssignmentLhsExtension(_) => !!!
                }

              readExprs((rhs, "exprRead") :: gatherLhsIndices(lhs, mutable.ListBuffer.empty).map(_ -> "indexRead")) { exprReads =>
                d"\n${ctx.err} = ${ctx.ctxName}.Write(${ctx.bindings(ById(findLhsIdent(lhs).refersTo)).bind}, []$TLAValue{${exprReads.tail.separateBy(d", ")}}, ${exprReads.head})" +
                  d"\nif ${ctx.err} != nil {${
                    d"\ncontinue".indented
                  }\n}"
              }
            case PCalAwait(condition) =>
              readExpr(condition, hint = "condition") { condition =>
                d"\nif !$condition.AsBool() {${
                  (d"\n${ctx.err} = distsys.ErrCriticalSectionAborted" +
                    d"\ncontinue").indented
                }\n}"
              }
            case PCalCall(_, _) => !!! // replaced by MPCalCall above
            case either@PCalEither(cases) =>
              ctx.cleanName(s"fairnessCounterCurrent") { fairnessCounterCurrent =>
                d"\n$fairnessCounterCurrent := ${fairnessCounterNames(ById(either))}" +
                  d"\n${fairnessCounterNames(ById(either))} = (${fairnessCounterNames(ById(either))} + 1) % ${cases.size}" +
                  d"\nswitch $fairnessCounterCurrent {${
                    cases.view.zipWithIndex.map {
                      case (body, idx) =>
                        d"\ncase $idx:" +
                          impl(body).indented
                    }.flattenDescriptions +
                      d"\ndefault:" +
                      d"""\npanic("current branch of either matches no code paths!")""".indented
                  }\n}"
              }
            case PCalIf(condition, yes, no) =>
              readExpr(condition, hint = "condition") { condition =>
                d"\nif $condition.AsBool() {${
                  impl(yes).indented
                }\n} else {${
                  impl(no).indented
                }\n}"
              }
            case PCalLabeledStatements(_, _) => !!!
            case PCalMacroCall(_, _) => !!!
            case PCalPrint(value) =>
              readExpr(value, hint = "toPrint") { value =>
                d"\n$value.PCalPrint()"
              }
            case PCalSkip() =>
              d"\n// skip"
            case PCalWhile(_, _) => !!!
            case PCalWith(variables, body) =>
              readExprs(variables.map {
                case PCalVariableDeclarationValue(name, value) => (value, s"${name.id}Read")
                case PCalVariableDeclarationSet(name, set) => (set, s"${name.id}Read")
              }) { exprReads =>
                val oldCtx = ctx
                val cleanedNames = variables.map(decl => ctx.nameCleaner.cleanName(decl.name.id))
                ((variables.view zip exprReads) zip cleanedNames).map {
                  case ((PCalVariableDeclarationValue(_, _), read), name) =>
                    d"\nvar $name $TLAValue = $read"
                  case ((PCalVariableDeclarationSet(_, _), read), name) =>
                    d"\nvar $name $TLAValue = $read.SelectElement()"
                }.toList.flattenDescriptions + {
                  implicit val ctx: GoCodegenContext = oldCtx.copy(
                    bindings = oldCtx.bindings ++ (variables.view.map(ById(_)) zip cleanedNames.view.map(FixedValueBinding)))
                  impl(body)
                }
              }
          }
          impl(restStmts, pfxDesc = pfxDesc + result)
      }

    val paramNames = params.view.map {
      case param@MPCalRefParam(name, _) => param -> nameCleaner.cleanName(name.id)
      case param@MPCalValParam(name) => param -> nameCleaner.cleanName(name.id)
    }.to(ById.mapFactory)
    val paramLocalNames = params.view.collect {
      case param@MPCalValParam(name) => param -> nameCleaner.cleanName(name.id)
    }.to(ById.mapFactory)
    val varNames = variables.view.map { decl =>
      decl -> nameCleaner.cleanName(decl.name.id)
    }.to(ById.mapFactory)

    val origCtx = ctx
    locally {
      implicit val ctx: GoCodegenContext = origCtx.copy(
        bindings = origCtx.bindings ++
          selfDeclOpt.map(selfDecl => ById(selfDecl) -> FixedValueBinding(origCtx.selfName)) ++
          paramNames.collect { case (paramId@ById(_: MPCalRefParam)) -> name => paramId -> ResourceBinding(name) } ++
          paramLocalNames.view.map { case paramId -> name => paramId -> ResourceBinding(name) } ++
          varNames.view.map { case vId -> name => vId -> ResourceBinding(name) },
        errOpt = Some(err.toDescription),
        resourceMappingCounts = params.view.collect {
          case param@MPCalRefParam(_, mappingCount) => param -> mappingCount
        }.to(ById.mapFactory),
      )

      def ensureLocalResource(value: Description): Description =
        d"${ctx.ctxName}.EnsureArchetypeResourceByPosition(distsys.LocalArchetypeResourceMaker($value))"

      d"""\n\nfunc $callableName(${ctx.ctxName} *distsys.MPCalContext, ${ctx.selfName} $TLAValue, ${ctx.constantsName} ${ctx.constantsTypeName}${
        params.view.map {
          case param@MPCalRefParam(_, _) => d", ${paramNames(ById(param))} $ArchetypeResourceHandle"
          case param@MPCalValParam(_) => d", ${paramNames(ById(param))} $TLAValue"
        }.flattenDescriptions
      }) error {${
        (d"\nvar ${ctx.err} error" +
          d"\n// label tags" +
          d"\nconst (${
            (d"\n$InitLabelTag = iota" +
              body.view.map {
                case PCalLabeledStatements(label, _) =>
                  d"\n${labelBinds(label.name)}"
              }.flattenDescriptions +
              d"\n$DoneLabelTag").indented
          }\n)" +
          d"\n$programCounterResourceName := ${
            ensureLocalResource {
              d"distsys.NewTLANumber($InitLabelTag)"
            }
          }" +
          params.view.collect {
            case param: MPCalValParam =>
              d"\n${paramLocalNames(ById(param))} := ${ensureLocalResource(paramNames(ById(param)).toDescription)}"
          }.flattenDescriptions +
          variables.view.map { decl =>
            d"\n${varNames(ById(decl))} := ${ensureLocalResource(d"$TLAValue{}")}" +
              d"\n_ = ${varNames(ById(decl))}" // avoid any chance of the unused vars error
          }.flattenDescriptions +
          pcalEithers.map { either =>
            d"\nvar ${fairnessCounterNames(ById(either))} int = 0"
          }.flattenDescriptions +
          d"\n" +
          d"\nfor {${
            (d"\nif $err != nil {${
              (d"\nif $err == distsys.ErrCriticalSectionAborted {${
                (d"\nctx.Abort()" +
                  d"\n$err = nil").indented
              }\n} else {${
                d"\nreturn $err".indented
              }\n}").indented
            }\n}" +
              ctx.cleanName("labelTag") { labelTag =>
                d"\nvar $labelTag $TLAValue" +
                  d"\n$labelTag, ${ctx.err} = ${ctx.ctxName}.Read($programCounterResourceName, []$TLAValue{})" +
                  d"\nif ${ctx.err} != nil {${
                    d"\nreturn ${ctx.err}".indented
                  }\n}" +
                  d"\nswitch $labelTag.AsNumber() {${
                    // perform any initial commits
                    d"\ncase $InitLabelTag:" +
                      variables.map {
                        case PCalVariableDeclarationEmpty(_) => d""
                        case decl@PCalVariableDeclarationSet(_, set) =>
                          readExpr(set) { setRead =>
                            d"\n${ctx.err} = ${ctx.ctxName}.Write(${varNames(ById(decl))}, nil, $setRead.SelectElement())" +
                              d"\nif ${ctx.err} != nil {${
                                d"\ncontinue".indented
                              }\n}"
                          }
                        case decl@PCalVariableDeclarationValue(_, value) =>
                          readExpr(value) { valueRead =>
                            d"\n${ctx.err} = ${ctx.ctxName}.Write(${varNames(ById(decl))}, nil, $valueRead)" +
                              d"\nif ${ctx.err} != nil {${
                                d"\ncontinue".indented
                              }\n}"
                          }
                      }.flattenDescriptions.indented +
                      goto(FirstLabel).indented +
                      body.map {
                        case PCalLabeledStatements(label, statements) =>
                          d"\ncase ${labelBinds(label.name)}:${
                            impl(statements).indented
                          }"
                      }.flattenDescriptions +
                      d"\ncase $DoneLabelTag:" +
                      d"\nreturn nil".indented
                  }\ndefault:${
                    d"""\nreturn fmt.Errorf("invalid program counter %v", $labelTag)""".indented
                  }\n}"
              }).indented
          }\n}").indented
      }\n}"""
    }
  }

  def escapeStringToGo(str: String): String =
    str.flatMap {
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\t' => "\\t"
      case '\n' => "\\n"
      case '\f' => "\\f"
      case '\r' => "\\r"
      case ch => ch.toString
    }

  def translateQuantifierBound(bound: TLAQuantifierBound, setExpr: Description)(implicit ctx: GoCodegenContext): (Map[ById[RefersTo.HasReferences],String],Description) =
    bound match {
      case TLAQuantifierBound(TLAQuantifierBound.IdsType, List(id), _) =>
        val boundIds: Map[ById[RefersTo.HasReferences],String] = Map(ById(id) -> ctx.nameCleaner.cleanName(id.id.id))
        val bindings = d"\nvar ${boundIds(ById(id))} $TLAValue = $setExpr" +
          d"\n_ = ${boundIds(ById(id))}" // stop the Go compiler from throwing errors on unused vars
        (boundIds, bindings)
      case TLAQuantifierBound(TLAQuantifierBound.TupleType, elements, _) =>
        val boundIds: Map[ById[RefersTo.HasReferences],String] = elements.view.map(id => ById(id) -> ctx.nameCleaner.cleanName(id.id.id)).toMap
        val bindings = elements.view.zipWithIndex.map {
          case (element, elemIdx) =>
            d"\nvar ${boundIds(ById(element))} $TLAValue = $setExpr.ApplyFunction(distsys.NewTLANumber(${elemIdx + 1 /* TLA+ tuples are 1-indexed */}))" +
              d"\n_ = ${boundIds(ById(element))}"
        }.flattenDescriptions
        (boundIds, bindings)
    }

  def translateQuantifierBounds(bounds: List[TLAQuantifierBound], setsTupleName: String)(body: GoCodegenContext=>Description)(implicit ctx: GoCodegenContext): Description = {
    val bindingInfos = bounds.view.zipWithIndex.map {
      case (bound, idx) => translateQuantifierBound(bound, d"$setsTupleName[$idx]")
    }.toList
    val boundIds: Map[ById[RefersTo.HasReferences], String] = bindingInfos.view.map(_._1).reduce(_ ++ _)

    val innerCtx: GoCodegenContext = ctx.copy(bindings = ctx.bindings ++ boundIds.map {
      case id -> name => id -> FixedValueBinding(name)
    })
    bindingInfos.view.map(_._2).flattenDescriptions + body(innerCtx)
  }

  /**
   * Given ctx, translates the expression into Go code.
   *
   * The output type is Description, which can be thought of as a lazy String which is optimized for
   * concatenation, embedding, and other generative operations.
   *
   * Note: this function relies on readExpr, defined above, for the handling of archetype resource reads.
   */
  def translateExpr(expression: TLAExpression)(implicit ctx: GoCodegenContext): Description =
    expression match {
      case TLAString(value) =>
        d"""distsys.NewTLAString("${escapeStringToGo(value)}")"""
      case TLANumber(value, _) =>
        d"""distsys.NewTLANumber(${
          value match {
            case TLANumber.IntValue(value) => value.toString()
            case TLANumber.DecimalValue(value) => ??? //value.toString() // FIXME: should we be able to support this?
          }
        })"""
      case expr@MappedRead(mappingCount, ident) if ctx.resourceMappingCounts.get(ById(ident.refersTo)).contains(mappingCount) =>
        @tailrec
        def findIndices(expr: TLAExpression, acc: mutable.ListBuffer[TLAExpression]): List[TLAExpression] =
          expr match {
            case _: TLAGeneralIdentifier => acc.result()
            case TLAFunctionCall(fn, params) =>
              if(params.size == 1) {
                acc.prepend(params.head)
              } else {
                acc.prepend(TLATuple(params))
              }
              findIndices(fn, acc)
          }

        val indices = findIndices(expr, mutable.ListBuffer.empty).map(translateExpr).separateBy(d", ")
        d"${ctx.ctxName}.Read(${ctx.bindings(ById(ident.refersTo)).bind}, []$TLAValue{$indices})"
      case ident@TLAGeneralIdentifier(_, prefix) =>
        assert(prefix.isEmpty)
        ctx.bindings(ById(ident.refersTo)) match {
          case IndependentCallableBinding(bind) =>
            // only makes sense when:
            // - passing an operator to an operator
            // - reading an arity 0 built-in (which is basically like a constant)
            bind.toDescription
          case DependentCallableBinding(bind) =>
            // only makes sense when:
            // - reading a locally-defined operator with arity 0
            // - passing an (arity >=1) operator to an operator
            val cleanArgs = View.fill(ident.refersTo.arity)(ctx.nameCleaner.cleanName("arg")).toList
            val wrappedFunc =
              d"func(${cleanArgs.view.map(arg => d"$arg $TLAValue").separateBy(d", ")}) $TLAValue {${
                d"\nreturn $bind(${ctx.constantsName}${cleanArgs.view.map(arg => d", $arg").flattenDescriptions})".indented
              }\n}"

            if(ident.refersTo.arity == 0) {
              wrappedFunc + d"()" // if arity 0, pass by value
            } else {
              wrappedFunc
            }
          case FixedValueBinding(bind) => bind.toDescription
          case ResourceBinding(_) => !!!
        }
      case TLADot(lhs, identifier) =>
        d"${translateExpr(lhs)}.ApplyFunction(${
          d"""distsys.NewTLAString("${identifier.id}")"""
        })"
      case call@TLAOperatorCall(_, prefix, arguments) =>
        assert(prefix.isEmpty)
        ctx.bindings(ById(call.refersTo)) match {
          case IndependentCallableBinding(bind) =>
            d"$bind(${arguments.map(translateExpr).separateBy(d", ")})"
          case DependentCallableBinding(bind) =>
            d"$bind(${ctx.constantsName}, ${arguments.map(translateExpr).separateBy(d", ")})"
        }
      case TLAIf(cond, tval, fval) =>
        d"func() $TLAValue {${
          (d"\nif ${translateExpr(cond)}.AsBool() {" +
            d"\nreturn ${translateExpr(tval)}".indented +
            d"\n} else {" +
            d"\nreturn ${translateExpr(fval)}".indented +
            d"\n}").indented
        }\n}()"
      case TLALet(defs, body) =>
        val origCtx = ctx
        d"func() $TLAValue {${
          val defnNames = defs.view.map {
            case defn@TLAOperatorDefinition(name, _, _, _) =>
              ById(defn) -> origCtx.nameCleaner.cleanName(name match {
                case Definition.ScopeIdentifierName(name) => name.id
                case Definition.ScopeIdentifierSymbol(symbol) => symbol.symbol.productPrefix
              })
          }.toMap
          implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ defs.view.map {
            case defn@TLAOperatorDefinition(_, Nil, _, _) => ById(defn) -> FixedValueBinding(defnNames(ById(defn)))
            case defn@TLAOperatorDefinition(_, _, _, _) => ById(defn) -> IndependentCallableBinding(defnNames(ById(defn)))
          })
          val origCtx2 = ctx
          (defs.view.map { defn =>
            (defn match {
              case defn@TLAOperatorDefinition(_, Nil, body, _) =>
                d"\nvar ${defnNames(ById(defn))} $TLAValue = ${translateExpr(body)}"
              case defn@TLAOperatorDefinition(_, args, body, _) =>
                val opDeclNames = args.view.map {
                  case decl@TLAOpDecl(variant) =>
                    variant match {
                      case TLAOpDecl.NamedVariant(ident, _) => ById(decl) -> origCtx2.nameCleaner.cleanName(ident.id)
                      case TLAOpDecl.SymbolVariant(sym) => ById(decl) -> origCtx2.nameCleaner.cleanName(sym.symbol.productPrefix)
                    }
                }.toMap
                implicit val ctx: GoCodegenContext = origCtx2.copy(bindings = origCtx2.bindings ++ args.view.map {
                  case decl@TLAOpDecl(variant) =>
                    variant match {
                      case TLAOpDecl.NamedVariant(_, 0) => ById(decl) -> FixedValueBinding(opDeclNames(ById(decl)))
                      case TLAOpDecl.NamedVariant(_, _) => ById(decl) -> IndependentCallableBinding(opDeclNames(ById(decl)))
                      case TLAOpDecl.SymbolVariant(_) => ById(decl) -> IndependentCallableBinding(opDeclNames(ById(decl)))
                    }
                })
                d"\n${defnNames(ById(defn))} := func(${
                  args.view.map { opDecl =>
                    if (opDecl.arity == 0) {
                      d"${opDeclNames(ById(opDecl))} $TLAValue"
                    } else {
                      d"${opDeclNames(ById(opDecl))} func(${View.fill(opDecl.arity)(TLAValue.toDescription).flattenDescriptions}) $TLAValue"
                    }
                  }.separateBy(d", ")
                }) $TLAValue {${
                  d"\nreturn ${translateExpr(body)}".indented
                }\n}"
              case _ => !!!
            }) + d"\n_ = ${defnNames(ById(defn.asInstanceOf[TLAOperatorDefinition]))}"
          }.flattenDescriptions + d"\nreturn ${translateExpr(body)}").indented
        }\n}()"
      case TLACase(arms, other) =>
        d"func() $TLAValue {${
          d"switch {${
            arms.map {
              case TLACaseArm(cond, result) =>
                d"\ncase ${translateExpr(cond)}.AsBool():" +
                  d"\nreturn ${translateExpr(result)}".indented
            }.flattenDescriptions +
              d"\ndefault:" +
              other.map(other => d"\nreturn ${translateExpr(other)}")
                .getOrElse(d"""\npanic("no cases matched for TLA+ case expression!")""").indented
          }\n}"
        }\n}()"
      case TLAMaybeAction(_, _) => !!!
      case TLARequiredAction(_, _) => !!!
      case TLAFairness(_, _, _) => !!!
      case TLAFunction(args, body) =>
        ctx.cleanName("args") { argsName =>
          d"""distsys.NewTLAFunction([]$TLAValue{${args.view.map(_.set).map(translateExpr).separateBy(d", ")}}, func($argsName []$TLAValue) $TLAValue {${
            translateQuantifierBounds(args, argsName) { innerCtx =>
              implicit val ctx: GoCodegenContext = innerCtx
              d"\nreturn ${translateExpr(body)}"
            }.indented
          }\n})"""
        }
      case TLAFunctionCall(function, params) =>
        d"""${translateExpr(function)}.ApplyFunction(${
          if(params.size == 1) {
            translateExpr(params.head)
          } else {
            d"""distsys.NewTLATuple(${
              params.view.map(translateExpr).separateBy(d", ")
            })"""
          }
        })"""
      case TLAFunctionSet(from, to) =>
        d"distsys.NewTLAFunctionSet(${translateExpr(from)}, ${translateExpr(to)})"
      case TLAFunctionSubstitution(source, substitutions) =>
        d"distsys.TLAFunctionSubstitution(${translateExpr(source)}, []distsys.TLAFunctionSubstitutionRecord{${
          substitutions.view.map {
            case TLAFunctionSubstitutionPair(anchor, keys, value) =>
              ctx.cleanName("anchor") { anchorName =>
                d"\n{[]$TLAValue{${
                  keys.view.map {
                    case TLAFunctionSubstitutionKey(List(index)) => translateExpr(index)
                    case TLAFunctionSubstitutionKey(indices) =>
                      d"distsys.NewTLATuple(${indices.view.map(translateExpr).separateBy(d", ")})"
                  }.separateBy(d", ")
                }}, func($anchorName $TLAValue) $TLAValue {${
                  d"return ${translateExpr(value)(ctx = ctx.copy(bindings = ctx.bindings.updated(ById(anchor), FixedValueBinding(anchorName))))}"
                }\n}},"
              }
          }.flattenDescriptions.indented
        }\n})"
      case at@TLAFunctionSubstitutionAt() =>
        val FixedValueBinding(name) = ctx.bindings(ById(at.refersTo))
        name.toDescription
      case TLAQuantifiedExistential(bounds, body) =>
        ctx.cleanName("args") { argsName =>
          d"""distsys.TLAQuantifiedExistential([]$TLAValue{${
            bounds.view.map(_.set).map(translateExpr).separateBy(d", ")
          }}, func($argsName []$TLAValue) bool {${
            translateQuantifierBounds(bounds, argsName) { innerCtx =>
              implicit val ctx: GoCodegenContext = innerCtx
              d"\nreturn ${translateExpr(body)}.AsBool()"
            }.indented
          }\n})"""
        }
      case TLAQuantifiedUniversal(bounds, body) =>
        ctx.cleanName("args") { argsName =>
          d"""distsys.TLAQuantifiedUniversal([]$TLAValue{${
            bounds.view.map(_.set).map(translateExpr).separateBy(d", ")
          }}, func($argsName []$TLAValue) bool {${
            translateQuantifierBounds(bounds, argsName) { innerCtx =>
              implicit val ctx: GoCodegenContext = innerCtx
              d"\nreturn ${translateExpr(body)}.AsBool()"
            }.indented
          }\n})"""
        }
      case TLAExistential(_, _) => !!!
      case TLAUniversal(_, _) => !!!
      case TLASetConstructor(contents) =>
        d"distsys.NewTLASet(${contents.view.map(translateExpr).separateBy(d", ")})"
      case TLASetRefinement(binding, when) =>
        val origCtx = ctx
        ctx.cleanName("elem") { elemName =>
          d"""distsys.TLASetRefinement(${translateExpr(binding.set)}, func($elemName $TLAValue) bool {${
            val (bindings, bindingCode) = translateQuantifierBound(binding, elemName.toDescription)
            locally {
              implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ bindings.view.map {
                case id -> name => id -> FixedValueBinding(name)
              })
              (bindingCode + d"\nreturn ${translateExpr(when)}.AsBool()").indented
            }
          }\n})"""
        }
      case TLASetComprehension(body, bounds) =>
        ctx.cleanName("args") { argsName =>
          d"""distsys.TLASetComprehension([]$TLAValue{${
            bounds.view.map(_.set).map(translateExpr).separateBy(d", ")
          }}, func($argsName []$TLAValue) $TLAValue {${
            translateQuantifierBounds(bounds, argsName) { innerCtx =>
              implicit val ctx: GoCodegenContext = innerCtx
              d"\nreturn ${translateExpr(body)}"
            }.indented
          }\n})"""
        }
      case TLATuple(elements) =>
        d"distsys.NewTLATuple(${elements.view.map(translateExpr).separateBy(d", ")})"
      case TLARecordConstructor(fields) =>
        d"distsys.NewTLARecord([]distsys.TLARecordField{${
          fields.view.map {
            case TLARecordConstructorField(name, value) =>
              d"""\n{distsys.NewTLAString("${name.id}"), ${translateExpr(value)}},"""
          }.flattenDescriptions.indented
        }${if(fields.nonEmpty) d"\n" else d""}})"
      case TLARecordSet(fields) =>
        d"distsys.NewTLARecordSet([]distsys.TLARecordField{${
          fields.view.map {
            case TLARecordSetField(name, set) => d"""\n{distsys.NewTLAString("${name.id}"), ${translateExpr(set)}},"""
          }.flattenDescriptions.indented
        }${if(fields.nonEmpty) d"\n" else d""}})"
    }

  @throws[PGoError]
  def apply(tlaModule: TLAModule, mpcalBlock: MPCalBlock, packageName: Option[String]): Description = {
    locally {
      val errors = mutable.ListBuffer[UnsupportedOperationsError.UnsupportedOperationError]()

      def checkBuiltin(sourceLocation: SourceLocation, builtin: TLABuiltinOperator): Unit =
        if (unsupportedOperators(ById(builtin))) {
          errors += UnsupportedOperationsError.UnsupportedOperationError(sourceLocation)
        }

      val supportedOpsChecker: PartialFunction[Visitable, Unit] = {
        case ident: TLAGeneralIdentifier =>
          ident.refersTo match {
            case builtin: TLABuiltinOperator => checkBuiltin(ident.sourceLocation, builtin)
            case _ =>
          }
        case opCall: TLAOperatorCall =>
          opCall.refersTo match {
            case builtin: TLABuiltinOperator => checkBuiltin(opCall.sourceLocation, builtin)
            case _ =>
          }
      }
      tlaModule.units.foreach(_.visit(Visitable.BottomUpFirstStrategy)(supportedOpsChecker))
      mpcalBlock.units.foreach(_.visit(Visitable.BottomUpFirstStrategy)(supportedOpsChecker))
      mpcalBlock.mpcalProcedures.foreach(_.visit(Visitable.BottomUpFirstStrategy)(supportedOpsChecker))
      mpcalBlock.archetypes.foreach(_.visit(Visitable.BottomUpFirstStrategy)(supportedOpsChecker))

      if(errors.nonEmpty) {
        throw UnsupportedOperationsError(errors.toList)
      }
    }

    val nameCleaner = new NameCleaner
    goKeywords.foreach(nameCleaner.addKnownName)
    nameCleaner.addKnownName("distsys")

    val Constants = nameCleaner.cleanName("Constants")

    val tlaExtDefns = (BuiltinModules.Intrinsics.members.view ++ tlaModule.exts.flatMap {
      case TLAModuleRefBuiltin(module) => module.members.view
      case TLAModuleRefModule(module) => ??? // TODO: actually implement modules
    }).toList

    val tlaExtDefnNames = tlaExtDefns.view.map {
      case defn@TLABuiltinOperator(_, identifier, _) =>
        identifier match {
          case Definition.ScopeIdentifierName(name) =>
            ById(defn) -> s"distsys.TLA_${name.id}"
          case Definition.ScopeIdentifierSymbol(symbol) =>
            ById(defn) -> s"distsys.TLA_${symbol.symbol.productPrefix}"
        }
    }.toMap

    val tlaUnits = (tlaModule.units.view.collect {
      case defn: TLAOperatorDefinition => defn
    } ++ mpcalBlock.units.view).toList

    val tlaUnitNames: Map[ById[TLAUnit],String] = tlaUnits.view.map {
      case defn@TLAOperatorDefinition(name, _, _, _) =>
        name match {
          case Definition.ScopeIdentifierName(name) =>
            ById(defn) -> nameCleaner.cleanName(toGoPublicName(name.id))
          case Definition.ScopeIdentifierSymbol(symbol) =>
            ById(defn) -> nameCleaner.cleanName(toGoPublicName(symbol.symbol.productPrefix))
        }
    }.toMap

    val constantDecls = tlaModule.units.view.collect {
      case TLAConstantDeclaration(constants) => constants
    }.flatten.toList

    // depends on the "constants" parameter, has to be scoped _within_ any top-level definition
    val constantNames = constantDecls.view.map {
      case decl@TLAOpDecl(variant) =>
        variant match {
          case TLAOpDecl.NamedVariant(ident, _) => ById(decl) -> nameCleaner.cleanName(toGoPublicName(ident.id))
          case TLAOpDecl.SymbolVariant(sym) => ById(decl) -> nameCleaner.cleanName(toGoPublicName(sym.symbol.productPrefix))
        }
    }.toMap

    val ctxName = nameCleaner.cleanName("ctx")
    val selfName = nameCleaner.cleanName("self")
    val constantsName = nameCleaner.cleanName("constants")

    implicit val ctx: GoCodegenContext = GoCodegenContext(
      nameCleaner = nameCleaner,
      ctxName = ctxName,
      selfName = selfName,
      constantsName = constantsName,
      constantsTypeName = Constants,
      bindings = (mpcalBlock.mpcalProcedures.view.map { proc =>
        ById(proc) -> IndependentCallableBinding(nameCleaner.cleanName(toGoPublicName(proc.name.id)))
      } ++ mpcalBlock.archetypes.view.map { arch =>
        ById(arch) -> IndependentCallableBinding(nameCleaner.cleanName(toGoPublicName(arch.name.id)))
      } ++ tlaExtDefnNames.map {
        case defnId -> name => defnId -> IndependentCallableBinding(name)
      } ++ constantDecls.view.map {
        case decl@TLAOpDecl(variant) =>
          variant match {
            case TLAOpDecl.NamedVariant(_, 0) => ById(decl) -> FixedValueBinding(s"$constantsName.${constantNames(ById(decl))}")
            case TLAOpDecl.NamedVariant(_, _) => ById(decl) -> IndependentCallableBinding(s"$constantsName.${constantNames(ById(decl))}")
            case TLAOpDecl.SymbolVariant(_) => ById(decl) -> IndependentCallableBinding(s"$constantsName.${constantNames(ById(decl))}")
          }
      } ++ tlaUnits.view.map { defn =>
        ById(defn.asInstanceOf[RefersTo.HasReferences]) -> DependentCallableBinding(tlaUnitNames(ById(defn)))
      }).toMap
    )

    d"package ${packageName.getOrElse(mpcalBlock.name.id.toLowerCase(Locale.ROOT)): String}\n" +
      d"\nimport (${
        (d"""\n"github.com/UBC-NSS/pgo/distsys"""" +
          d"""\n"fmt"""").indented
      }\n)" +
      d"\n" +
      d"\nvar _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import" +
      d"\nvar _ = distsys.TLAValue{} // same, for distsys" +
      d"\n" +
      d"\ntype $Constants struct {${
        constantDecls.map {
          case decl@TLAOpDecl(variant) =>
            variant match {
              case TLAOpDecl.NamedVariant(_, 0) =>
                d"\n${constantNames(ById(decl))} $TLAValue"
              case TLAOpDecl.NamedVariant(_, arity) =>
                d"\n${constantNames(ById(decl))} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")} $TLAValue"
              case TLAOpDecl.SymbolVariant(sym) =>
                val arity = if (sym.symbol.isPrefix) 1 else if (sym.symbol.isPostfix) 1 else { assert(sym.symbol.isInfix); 2 }
                d"\n${constantNames(ById(decl))} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")} $TLAValue"
            }
        }.flattenDescriptions.indented
      }\n}\n" +
      tlaUnits.view.map {
        case defn@TLAOperatorDefinition(name, args, body, _) =>
          val origCtx = ctx
          val argNames = args.view.map {
            case decl@TLAOpDecl(variant) =>
              variant match {
                case TLAOpDecl.NamedVariant(ident, 0) =>
                  ById(decl) -> FixedValueBinding(nameCleaner.cleanName(ident.id))
                case TLAOpDecl.NamedVariant(ident, _) =>
                  ById(decl) -> IndependentCallableBinding(nameCleaner.cleanName(ident.id))
                case TLAOpDecl.SymbolVariant(sym) =>
                  ById(decl) -> IndependentCallableBinding(nameCleaner.cleanName(sym.symbol.productPrefix))
              }
          }.toMap
          d"\nfunc ${tlaUnitNames(ById(defn))}($constantsName $Constants${args.view.map {
            case decl@TLAOpDecl(variant) =>
              variant match {
                case TLAOpDecl.NamedVariant(_, 0) => d", ${argNames(ById(decl)).bind} $TLAValue"
                case TLAOpDecl.NamedVariant(_, arity) => d", ${argNames(ById(decl)).bind} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")}) $TLAValue"
                case TLAOpDecl.SymbolVariant(sym) =>
                  val arity = if(sym.symbol.isInfix) 2 else 1
                  d", ${argNames(ById(decl)).bind} func(${View.fill(arity)(TLAValue.toDescription).separateBy(d", ")}) $TLAValue"
              }
          }.flattenDescriptions}) $TLAValue {${
            implicit val ctx: GoCodegenContext = origCtx.copy(bindings = origCtx.bindings ++ argNames)
            d"\nreturn ${translateExpr(body)}".indented
          }\n}\n"
      }.flattenDescriptions + // TODO: procedures
      mpcalBlock.archetypes.view.map { arch =>
        translateMPCalCallable(ctx.bindings(ById(arch)).bind,
          selfDeclOpt = Some(arch.selfDecl), params = arch.params, variables = arch.variables, body = arch.body)
      }.flattenDescriptions
  }
}
