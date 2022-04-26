package pgo.trans

import pgo.model.{Definition, DefinitionOne, PGoError, RefersTo, Rewritable, SourceLocation, Visitable}
import pgo.model.mpcal._
import pgo.model.pcal._
import pgo.model.tla._
import pgo.util.{ById, Description, MPCalPassUtils, NameCleaner}
import Description._
import pgo.model.Definition.ScopeIdentifierName
import pgo.model.tla.BuiltinModules.TLABuiltinOperator
import pgo.util.MPCalPassUtils.MappedRead
import pgo.util.!!!

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

  private val TLAValue = "tla.TLAValue"
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
  final case class ConstantBinding(bind: String) extends Binding

  case class GoCodegenContext(nameCleaner: NameCleaner, bindings: Map[ById[RefersTo.HasReferences],Binding] = Map.empty,
                              err: String, iface: String) {
    def cleanName[T](hint: String)(fn: String => T): T =
      fn(nameCleaner.cleanName(hint))
  }

  def toGoPublicName(id: String): String =
    id.capitalize

  def hasMappingWithCount(mappingCount: Int, ident: TLAGeneralIdentifier): Boolean =
    ident.refersTo match {
      case MPCalRefParam(_, `mappingCount`) => true
      case _ => false
    }

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
      case expr@MappedRead(mappingCount, ident) if hasMappingWithCount(mappingCount, ident) =>
        val indices = MPCalPassUtils.findMappedReadIndices(expr, mutable.ListBuffer.empty)
          .map(_.rewrite(Rewritable.TopDownFirstStrategy)(readReplacer))
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
            d"\n${replaceDefn.name.id}, ${ctx.err} = ${ctx.iface}.Read(${ctx.bindings(ById(defn)).bind}, []$TLAValue{${indices.view.map(translateExpr).separateBy(d", ")}})" +
            d"\nif ${ctx.err} != nil {${
              d"\nreturn ${ctx.err}".indented
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

  def translateBodyStmts(labelPrefix: String, selfDecl: DefinitionOne, fairnessInfix: String, stateVariables: Set[ById[DefinitionOne]], refStateVariables: Set[ById[DefinitionOne]], stmts: List[PCalStatement])(implicit ctx: GoCodegenContext): Description = {
    val pcalEithers: List[PCalEither] = locally {
      val acc = mutable.ListBuffer.empty[PCalEither]
      stmts.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
        case either: PCalEither => acc += either
      })
      acc.result()
    }
    val pcalWithSetDecls: List[PCalVariableDeclarationSet] = locally {
      val acc = mutable.ListBuffer.empty[PCalVariableDeclarationSet]
      stmts.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
        case PCalWith(decls, _) =>
          acc ++= decls.view.collect { case decl: PCalVariableDeclarationSet => decl }
      })
      acc.result()
    }
    val fairnessCounterIds = (pcalEithers.view ++ pcalWithSetDecls.view)
      .zipWithIndex
      .map { case (either, idx) => ById(either) -> s"$labelPrefix.$fairnessInfix.$idx" }
      .toMap

    val necessaryStateVariables: List[(DefinitionOne,String)] = locally {
      val acc = mutable.ListBuffer.empty[(DefinitionOne,String)]
      // MPCalRefExpr is deliberately omitted from capture, because the reference is passed as a string, and not otherwise used in codegen.
      stmts.foreach(_.visit(Visitable.BottomUpFirstStrategy) {
        case ident: TLAGeneralIdentifier if stateVariables(ById(ident.refersTo)) =>
          acc += ident.refersTo -> ctx.nameCleaner.cleanName(ident.name.id)
        case lhs: PCalAssignmentLhsIdentifier if stateVariables(ById(lhs.refersTo)) =>
          acc += lhs.refersTo -> ctx.nameCleaner.cleanName(lhs.identifier.id)
      })
      acc.result().distinctBy(p => ById(p._1))
    }

    def impl(stmts: List[PCalStatement], pfxDesc: Description = d"")(implicit ctx: GoCodegenContext): Description =
      stmts match {
        case Nil =>
          d"$pfxDesc\n// no statements"
        case PCalGoto(target) :: Nil =>
          pfxDesc + d"\nreturn ${ctx.iface}.Goto(${mkGoString(s"$labelPrefix.$target")})"
        case PCalReturn() :: Nil =>
          pfxDesc + d"\nreturn ${ctx.iface}.Return()"
        case PCalExtensionStatement(call@MPCalCall(_, arguments)) :: (tailStmt@(PCalReturn() | PCalGoto(_))) :: restStmts =>
          assert(restStmts.isEmpty)

          // the two small differences between a tail-call and a call with a local return addr
          // note that all calls should be followed by a goto indicating return address, as a consequence of
          // the normalize pass
          val returnTargetOpt = tailStmt match {
            case PCalReturn() => ""
            case PCalGoto(returnTarget) => s", ${mkGoString(s"$labelPrefix.$returnTarget")}"
          }
          val callFn = tailStmt match {
            case PCalReturn() => "TailCall"
            case PCalGoto(_) => "Call"
          }

          val callee = call.refersTo

          // while value arguments can be read as usual with readExpr, for ref arguments, we have to pass the underlying resource's name
          def readArgumentValues(arguments: List[Either[MPCalRefExpr,TLAExpression]], accBinds: List[Description] = Nil)(body: List[Description]=>Description): Description = {
            arguments match {
              case Nil => body(accBinds.reverse)
              case Left(ref) :: restArgs =>
                val bind = ctx.nameCleaner.cleanName(ref.name.id)
                // to get the name of the underlying resource (which may be different from that of name in the ref expr), there are two cases:
                ref.refersTo match {
                  case _: MPCalRefParam =>
                    // 1) the name already refers to a ref param, so the resource with that name actually stores the ref'd
                    //    resource as a value already. treat the ref param as a plain value, and the correct name comes out
                    d"\n$bind := ${ctx.iface}.ReadArchetypeResourceLocal(${mkGoString(s"$labelPrefix.${ref.name.id}")})" +
                      readArgumentValues(restArgs, bind.toDescription :: accBinds)(body)
                  case _ =>
                    // 2) the name refers to a state variable (param or internal state var), and we should pass the name
                    //    directly as a string value, which is statically know to be the actual name in the ref
                    readArgumentValues(restArgs, d"tla.MakeTLAString(${mkGoString(s"$labelPrefix.${ref.name.id}")})" :: accBinds)(body)
                }
              case Right(expr) :: restArgs =>
                // for plain expressions, fall back to standard processing for reading values
                readExpr(expr) { argBind =>
                  readArgumentValues(restArgs, argBind :: accBinds)(body)
                }
            }
          }

          pfxDesc + readArgumentValues(arguments) { argBinds =>
            val calleeName = mkGoString(callee.name.id)
            d"\nreturn ${ctx.iface}.$callFn($calleeName$returnTargetOpt, ${argBinds.separateBy(d", ")})"
          }

        case stmt :: restStmts =>
          val result = stmt match {
            case PCalAssert(condition) =>
              val conditionExpr = condition
              readExpr(condition, hint = "condition") { condition =>
                d"\nif !$condition.AsBool() {${
                  d"""\nreturn fmt.Errorf("%w: ${
                    escapeStringToGo(PCalRenderPass.describeExpr(conditionExpr).linesIterator.mkString("\n"))
                  }", distsys.ErrAssertionFailed)""".indented
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
                d"\n${ctx.err} = ${ctx.iface}.Write(${ctx.bindings(ById(findLhsIdent(lhs).refersTo)).bind}, []$TLAValue{${exprReads.tail.separateBy(d", ")}}, ${exprReads.head})" +
                  d"\nif ${ctx.err} != nil {${
                    d"\nreturn ${ctx.err}".indented
                  }\n}"
              }
            case PCalAwait(condition) =>
              readExpr(condition, hint = "condition") { condition =>
                d"\nif !$condition.AsBool() {${
                  d"\nreturn distsys.ErrCriticalSectionAborted".indented
                }\n}"
              }
            case PCalCall(_, _) => !!! // replaced by MPCalCall above
            case either@PCalEither(cases) =>
              d"""\nswitch ${ctx.iface}.NextFairnessCounter("${fairnessCounterIds(ById(either))}", ${cases.size}) {${
                cases.view.zipWithIndex.map {
                  case (body, idx) =>
                    d"\ncase $idx:" +
                      impl(body).indented
                }.flattenDescriptions +
                  d"\ndefault:" +
                  d"""\npanic("current branch of either matches no code paths!")""".indented
              }\n}"""
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
              @tailrec
              def performBindings(variables: List[PCalVariableDeclarationBound], bindings: Description)(implicit ctx: GoCodegenContext): Description =
                variables match {
                  case Nil =>
                    bindings + impl(body)
                  case decl :: restDecls =>
                    val cleanedName = ctx.nameCleaner.cleanName(decl.name.id)
                    val oneBind = decl match {
                      case PCalVariableDeclarationValue(name, value) =>
                        readExpr(value, s"${name.id}Read") { read =>
                          d"\nvar $cleanedName $TLAValue = $read"
                        }
                      case decl@PCalVariableDeclarationSet(name, set) =>
                        readExpr(set, s"${name.id}Read") { read =>
                          // need a temp local var to store translated read's result, or we might evaluate it up to 3 times
                          val tempName = ctx.nameCleaner.cleanName(s"${name.id}Read")
                          // weird semantics:
                          // - with of an empty set is just not explored, so if the set's empty we abort the critical section
                          // - like with an either, try to keep making progress by exploring multiple possible element selections.
                          //   this uses the same fairness mechanism as either, which approximates round-robin selection of set elements.
                          d"\nvar $tempName = $read" +
                            d"\nif $tempName.AsSet().Len() == 0 {${
                              d"\nreturn distsys.ErrCriticalSectionAborted".indented
                            }\n}" +
                            d"\nvar $cleanedName $TLAValue = $tempName.SelectElement(${ctx.iface}.NextFairnessCounter(\"${fairnessCounterIds(ById(decl))}\", uint($tempName.AsSet().Len())))"
                        }
                    }
                    performBindings(restDecls, bindings + oneBind + d"\n_ = $cleanedName")(
                      ctx.copy(bindings = ctx.bindings.updated(ById(decl), FixedValueBinding(cleanedName))))
                }

              performBindings(variables, d"")
          }
          impl(restStmts, pfxDesc = pfxDesc + result)
      }

    val origCtx = ctx
    locally {
      implicit val ctx: GoCodegenContext = origCtx.copy(
        bindings = origCtx.bindings ++
          Some(ById(selfDecl) -> FixedValueBinding(s"${origCtx.iface}.Self()")) ++
          necessaryStateVariables.view.map {
            case defn -> bind => ById(defn) -> ResourceBinding(bind)
          })

      d"\nvar ${ctx.err} error" +
        d"\n_ = ${ctx.err}" +
        necessaryStateVariables.view.map {
          case (defn, bind) =>
            val stateVarName = s"$labelPrefix.${defn.identifier.asInstanceOf[ScopeIdentifierName].name.id}"
            if (refStateVariables(ById(defn))) {
              d"\n$bind, ${ctx.err} := ${ctx.iface}.RequireArchetypeResourceRef(${mkGoString(stateVarName)})" +
                d"\nif ${ctx.err} != nil {${
                  d"\nreturn ${ctx.err}".indented
                }\n}"
            } else {
              d"\n$bind := ${ctx.iface}.RequireArchetypeResource(${mkGoString(stateVarName)})"
            }
        }.flattenDescriptions +
        impl(stmts)
    }
  }

  def translateCriticalSection(labelPrefix: String, selfDecl: DefinitionOne, stateVariables: Set[ById[DefinitionOne]], refStateVariables: Set[ById[DefinitionOne]], criticalSection: PCalLabeledStatements)(implicit ctx: GoCodegenContext): Description = {
    d"\ndistsys.MPCalCriticalSection {${
      (d"\nName: ${mkGoString(s"$labelPrefix.${criticalSection.label.name}")},".indented +
        d"\nBody: func(${ctx.iface} distsys.ArchetypeInterface) error {${
            translateBodyStmts(labelPrefix,
              selfDecl = selfDecl,
              fairnessInfix = criticalSection.label.name,
              stateVariables = stateVariables,
              refStateVariables = refStateVariables,
              stmts = criticalSection.statements).indented
        }\n},").indented
    }\n},"
  }

  def mkGoString(str: String): String =
    s""""${escapeStringToGo(str)}""""

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
            d"\nvar ${boundIds(ById(element))} $TLAValue = $setExpr.ApplyFunction(tla.MakeTLANumber(${elemIdx + 1 /* TLA+ tuples are 1-indexed */}))" +
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
        d"""tla.MakeTLAString("${escapeStringToGo(value)}")"""
      case TLANumber(value, _) =>
        d"""tla.MakeTLANumber(${
          value match {
            case TLANumber.IntValue(value) => value.toString()
            case TLANumber.DecimalValue(value) => ??? //value.toString() // FIXME: should we be able to support this?
          }
        })"""
      case MappedRead(mappingCount, ident) if hasMappingWithCount(mappingCount, ident) => !!!
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

            if(ident.refersTo.arity == 0) {
              // if arity 0, just call with iface as only argument and yield the value
              d"$bind(${ctx.iface})"
            } else {
              // if arity >= 1 and this is not an operator call (that's a different AST node), construct a function
              // with the right arguments in-place
              val cleanArgs = View.fill(ident.refersTo.arity)(ctx.nameCleaner.cleanName("arg")).toList
              d"func(${cleanArgs.view.map(arg => d"$arg $TLAValue").separateBy(d", ")}) $TLAValue {${
                d"\nreturn $bind(${ctx.iface}${cleanArgs.view.map(arg => d", $arg").flattenDescriptions})".indented
              }\n}"
            }
          case FixedValueBinding(bind) => bind.toDescription
          case ConstantBinding(bind) =>
            if(ident.refersTo.arity == 0) {
              d"$bind()"
            } else {
              // because constant bindings give variadic functions, we need to generate a forwarder that is fixed-arity
              // since the only place this makes sense is passing a constant operator to another operator
              val cleanArgs = View.fill(ident.refersTo.arity)(ctx.nameCleaner.cleanName("arg")).toList
              d"func(${cleanArgs.view.map(arg => d"$arg $TLAValue").separateBy(d", ")}) $TLAValue {${
                d"\nreturn $bind(${cleanArgs.view.map(_.toDescription).separateBy(d", ")})".indented
              }\n}"
            }
          case ResourceBinding(_) => !!!
        }
      case TLADot(lhs, identifier) =>
        d"${translateExpr(lhs)}.ApplyFunction(${
          d"""tla.MakeTLAString("${identifier.id}")"""
        })"
      case TLACrossProduct(operands) =>
        d"tla.TLACrossProduct(${operands.view.map(translateExpr).separateBy(d", ")})"
      case call@TLAOperatorCall(_, prefix, arguments) =>
        assert(prefix.isEmpty)
        // special cases: boolean logic in TLC is short-circuiting, so we need to special case /\, \/, and => to avoid
        // breaking situations that rely on it (bounds checks, etc, where part of the condition may crash)
        call.refersTo match {
          case ref if ref eq BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalAndSymbol) =>
            val List(lhs, rhs) = arguments
            d"tla.MakeTLABool(${translateExpr(lhs)}.AsBool() && ${translateExpr(rhs)}.AsBool())"
          case ref if ref eq BuiltinModules.Intrinsics.memberSym(TLASymbol.LogicalOrSymbol) =>
            val List(lhs, rhs) = arguments
            d"tla.MakeTLABool(${translateExpr(lhs)}.AsBool() || ${translateExpr(rhs)}.AsBool())"
          case ref if ref eq BuiltinModules.Intrinsics.memberSym(TLASymbol.ImpliesSymbol) =>
            val List(lhs, rhs) = arguments
            d"tla.MakeTLABool(!${translateExpr(lhs)}.AsBool() || ${translateExpr(rhs)}.AsBool())"
          case _ =>
            ctx.bindings(ById(call.refersTo)) match {
              case IndependentCallableBinding(bind) =>
                d"$bind(${arguments.map(translateExpr).separateBy(d", ")})"
              case DependentCallableBinding(bind) =>
                d"$bind(${ctx.iface}, ${arguments.map(translateExpr).separateBy(d", ")})"
              case ConstantBinding(bind) =>
                d"$bind(${arguments.map(translateExpr).separateBy(d", ")})"
            }
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
                .getOrElse(d"""\npanic(fmt.Errorf("%w: no cases matched for TLA+ case expression!", tla.ErrTLAType))""").indented
          }\n}"
        }\n}()"
      case TLAMaybeAction(_, _) => !!!
      case TLARequiredAction(_, _) => !!!
      case TLAFairness(_, _, _) => !!!
      case TLAFunction(args, body) =>
        ctx.cleanName("args") { argsName =>
          d"""tla.MakeTLAFunction([]$TLAValue{${args.view.map(_.set).map(translateExpr).separateBy(d", ")}}, func($argsName []$TLAValue) $TLAValue {${
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
            d"""tla.MakeTLATuple(${
              params.view.map(translateExpr).separateBy(d", ")
            })"""
          }
        })"""
      case TLAFunctionSet(from, to) =>
        d"tla.MakeTLAFunctionSet(${translateExpr(from)}, ${translateExpr(to)})"
      case TLAFunctionSubstitution(source, substitutions) =>
        d"tla.TLAFunctionSubstitution(${translateExpr(source)}, []tla.TLAFunctionSubstitutionRecord{${
          substitutions.view.map {
            case TLAFunctionSubstitutionPair(anchor, keys, value) =>
              ctx.cleanName("anchor") { anchorName =>
                d"\n{[]$TLAValue{${
                  keys.view.map {
                    case TLAFunctionSubstitutionKey(List(index)) => translateExpr(index)
                    case TLAFunctionSubstitutionKey(indices) =>
                      d"tla.MakeTLATuple(${indices.view.map(translateExpr).separateBy(d", ")})"
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
          d"""tla.TLAQuantifiedExistential([]$TLAValue{${
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
          d"""tla.TLAQuantifiedUniversal([]$TLAValue{${
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
        d"tla.MakeTLASet(${contents.view.map(translateExpr).separateBy(d", ")})"
      case TLASetRefinement(binding, when) =>
        val origCtx = ctx
        ctx.cleanName("elem") { elemName =>
          d"""tla.TLASetRefinement(${translateExpr(binding.set)}, func($elemName $TLAValue) bool {${
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
          d"""tla.TLASetComprehension([]$TLAValue{${
            bounds.view.map(_.set).map(translateExpr).separateBy(d", ")
          }}, func($argsName []$TLAValue) $TLAValue {${
            translateQuantifierBounds(bounds, argsName) { innerCtx =>
              implicit val ctx: GoCodegenContext = innerCtx
              d"\nreturn ${translateExpr(body)}"
            }.indented
          }\n})"""
        }
      case TLATuple(elements) =>
        d"tla.MakeTLATuple(${elements.view.map(translateExpr).separateBy(d", ")})"
      case TLARecordConstructor(fields) =>
        d"tla.MakeTLARecord([]tla.TLARecordField{${
          fields.view.map {
            case TLARecordConstructorField(name, value) =>
              d"""\n{tla.MakeTLAString("${name.id}"), ${translateExpr(value)}},"""
          }.flattenDescriptions.indented
        }${if(fields.nonEmpty) d"\n" else d""}})"
      case TLARecordSet(fields) =>
        d"tla.MakeTLARecordSet([]tla.TLARecordField{${
          fields.view.map {
            case TLARecordSetField(name, set) => d"""\n{tla.MakeTLAString("${name.id}"), ${translateExpr(set)}},"""
          }.flattenDescriptions.indented
        }${if(fields.nonEmpty) d"\n" else d""}})"
      case TLAQuantifiedChoose(binding@TLAQuantifierBound(_, _, set), body) =>
        val boundName = ctx.nameCleaner.cleanName("element")
        d"tla.TLAChoose(${translateExpr(set)}, func($boundName $TLAValue) bool {${
          val (bindings, bindingCode) = translateQuantifierBound(binding, d"$boundName")
          (bindingCode +
            d"\nreturn ${translateExpr(body)(ctx = ctx.copy(bindings = ctx.bindings ++ bindings.view.mapValues(FixedValueBinding)))}.AsBool()").indented
        }\n})"
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
    nameCleaner
      .addKnownName("distsys")
      .addKnownName("tla")
      .addKnownName("fmt")

    val tlaExtDefns = (BuiltinModules.Intrinsics.members.view ++ tlaModule.exts.flatMap {
      case TLAModuleRefBuiltin(module) => module.members.view
      case TLAModuleRefModule(module) => ??? // TODO: actually implement modules
    } ++ BuiltinModules.PCalNames.members).toList

    val tlaExtDefnNames = tlaExtDefns.view.map {
      case defn@TLABuiltinOperator(_, identifier, _) =>
        identifier match {
          case Definition.ScopeIdentifierName(name) =>
            ById(defn) -> s"tla.TLA_${name.id}"
          case Definition.ScopeIdentifierSymbol(symbol) =>
            ById(defn) -> s"tla.TLA_${symbol.symbol.productPrefix}"
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

    val errName = nameCleaner.cleanName("err")
    val ifaceName = nameCleaner.cleanName("iface")
    val jumpTableName = nameCleaner.cleanName("jumpTable")
    val procTableName = nameCleaner.cleanName("procTable")

    implicit val ctx: GoCodegenContext = GoCodegenContext(
      nameCleaner = nameCleaner,
      err = errName,
      iface = ifaceName,
      bindings = (mpcalBlock.mpcalProcedures.view.map { proc =>
        ById(proc) -> IndependentCallableBinding(nameCleaner.cleanName(toGoPublicName(proc.name.id)))
      } ++ mpcalBlock.archetypes.view.map { arch =>
        ById(arch) -> IndependentCallableBinding(nameCleaner.cleanName(toGoPublicName(arch.name.id)))
      } ++ tlaExtDefnNames.map {
        case defnId -> name => defnId -> IndependentCallableBinding(name)
      } ++ constantDecls.view.map {
        case decl@TLAOpDecl(variant) =>
          val name = variant match {
            case TLAOpDecl.NamedVariant(ident, _) => ident.id
            case TLAOpDecl.SymbolVariant(sym) => sym.symbol.stringReprDefn
          }
          ById(decl) -> ConstantBinding(s"$ifaceName.GetConstant(${mkGoString(name)})")
      } ++ tlaUnits.view.map { defn =>
        // we know this unit is an operator defn; we don't support any other type yet
        ById(defn.asInstanceOf[RefersTo.HasReferences]) -> DependentCallableBinding(tlaUnitNames(ById(defn)))
      }).toMap
    )

    d"package ${packageName.getOrElse(mpcalBlock.name.id.toLowerCase(Locale.ROOT)): String}\n" +
      d"\nimport (${
        (d"""\n"github.com/UBC-NSS/pgo/distsys"""" +
          d"""\n"github.com/UBC-NSS/pgo/distsys/tla"""" +
          d"""\n"fmt"""").indented
      }\n)" +
      d"\n" +
      d"\nvar _ = new(fmt.Stringer) // unconditionally prevent go compiler from reporting unused fmt import" +
      d"\nvar _ = distsys.ErrDone" +
      d"\nvar _ = tla.TLAValue{} // same, for tla" +
      d"\n" +
      tlaUnits.view.map {
        case defn@TLAOperatorDefinition(_, args, body, _) =>
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
          d"\nfunc ${tlaUnitNames(ById(defn))}(${ctx.iface} distsys.ArchetypeInterface${args.view.map {
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
          }\n}"
      }.flattenDescriptions +
      d"\n\nvar $procTableName = distsys.MakeMPCalProcTable(${
        mpcalBlock.mpcalProcedures.view.map { proc =>
          d"\ndistsys.MPCalProc {${
            (d"\nName: ${mkGoString(proc.name.id)}," +
              d"\nLabel: ${mkGoString(s"${proc.name.id}.${proc.body.head.asInstanceOf[PCalLabeledStatements].label.name}")}," +
              d"\nStateVars: []string{${
                (proc.params.view ++ proc.variables.view)
                  .map(_.identifier.asInstanceOf[ScopeIdentifierName].name.id)
                  .map(id => s"${proc.name.id}.$id")
                  .map(mkGoString)
                  .map(_.toDescription)
                  .separateBy(d", ")
              }}," +
              d"\nPreAmble: func(${ctx.iface} distsys.ArchetypeInterface) error {${
                val preambleSynthStmts = proc.variables.map {
                  case decl@PCalPVariableDeclaration(name, value) =>
                    PCalAssignment(List(PCalAssignmentPair(
                      PCalAssignmentLhsIdentifier(name)
                        .setRefersTo(decl),
                      value.getOrElse(TLAGeneralIdentifier(TLAIdentifier("defaultInitValue"), Nil)
                        .setRefersTo(BuiltinModules.PCalNames.memberAlpha("defaultInitValue"))))))
                }

                (translateBodyStmts(proc.name.id,
                  selfDecl = proc.selfDecl,
                  fairnessInfix = ".",
                  stateVariables = (proc.params.view ++ proc.variables.view).to(ById.setFactory),
                  refStateVariables = proc.params.view.collect { case ref: MPCalRefParam => ref }.to(ById.setFactory),
                  stmts = preambleSynthStmts) +
                  d"\nreturn nil").indented
              }\n},").indented
          }\n},".indented
        }.flattenDescriptions
      }${if(mpcalBlock.mpcalProcedures.nonEmpty) d"\n" else d""})" +
      d"\n\nvar $jumpTableName = distsys.MakeMPCalJumpTable(${
        mpcalBlock.mpcalProcedures.view.map { proc =>
          proc.body.view.map {
            case criticalSection@PCalLabeledStatements(_, _) =>
              translateCriticalSection(proc.name.id,
                selfDecl = proc.selfDecl,
                stateVariables = (proc.params.view ++ proc.variables).to(ById.setFactory),
                refStateVariables = proc.params.view.collect { case ref: MPCalRefParam => ref }.to(ById.setFactory),
                criticalSection = criticalSection)
            case _ => !!!
          }.flattenDescriptions +
            d"\ndistsys.MPCalCriticalSection {${ // the Error label exists for all procedures, and is trivial
              d"\nName: ${mkGoString(s"${proc.name.id}.Error")}," +
                d"\nBody: func(distsys.ArchetypeInterface) error {${
                  d"\nreturn distsys.ErrProcedureFallthrough".indented
                }\n},"
            }\n},"
        }.flattenDescriptions.indented +
          mpcalBlock.archetypes.view.map { arch =>
            arch.body.view.map {
              case criticalSection@PCalLabeledStatements(_, _) =>
                translateCriticalSection(arch.name.id,
                  selfDecl = arch.selfDecl,
                  stateVariables = (arch.params.view ++ arch.variables.view).to(ById.setFactory),
                  refStateVariables = arch.params.view.collect { case ref: MPCalRefParam => ref }.to(ById.setFactory),
                  criticalSection = criticalSection)
            }.flattenDescriptions +
              d"\ndistsys.MPCalCriticalSection {${ // the Done label exists for all archetypes, and is trivial
                (d"\nName: ${mkGoString(s"${arch.name.id}.Done")}," +
                  d"\nBody: func(distsys.ArchetypeInterface) error {${
                    d"\nreturn distsys.ErrDone".indented
                  }\n},").indented
              }\n},"
          }.flattenDescriptions.indented
      }${if(mpcalBlock.archetypes.nonEmpty || mpcalBlock.pcalProcedures.nonEmpty) d"\n" else d""})" +
      mpcalBlock.archetypes.view.map { arch =>
        d"\n\nvar ${ctx.bindings(ById(arch)).bind} = distsys.MPCalArchetype {${
          (d"\nName: ${mkGoString(arch.name.id)}," +
            d"\nLabel: ${mkGoString(s"${arch.name.id}.${arch.body.head.asInstanceOf[PCalLabeledStatements].label.name}")}," +
            d"\nRequiredRefParams: []string{${
              arch.params.view
                .collect { case MPCalRefParam(name, _) => s"${arch.name.id}.${name.id}" }
                .map(mkGoString)
                .map(_.toDescription)
                .separateBy(d", ")
            }}," +
            d"\nRequiredValParams: []string{${
              arch.params.view
                .collect { case MPCalValParam(name) => s"${arch.name.id}.${name.id}" }
                .map(mkGoString)
                .map(_.toDescription)
                .separateBy(d", ")
            }}," +
            d"\nJumpTable: $jumpTableName," +
            d"\nProcTable: $procTableName," +
            d"\nPreAmble: func(${ctx.iface} distsys.ArchetypeInterface) {${
              val (resultDesc, _) = arch.variables.foldLeft((d"", ctx.copy(bindings = ctx.bindings + (ById(arch.selfDecl) -> FixedValueBinding(s"${ctx.iface}.Self()"))))) { (pair, decl) =>
                val (prevDesc, origCtx) = pair
                implicit val ctx: GoCodegenContext = origCtx
                val resName = s"${arch.name.id}.${decl.name.id}"
                val resBind = ById(decl) -> FixedValueBinding(s"${ctx.iface}.ReadArchetypeResourceLocal(${mkGoString(resName)})")
                decl match {
                  case PCalVariableDeclarationEmpty(_) =>
                    (prevDesc + d"\n${ctx.iface}.EnsureArchetypeResourceLocal(${mkGoString(resName)}, $TLAValue{})",
                      ctx.copy(bindings = ctx.bindings + resBind))
                  case PCalVariableDeclarationValue(_, value) => (prevDesc + d"\n${ctx.iface}.EnsureArchetypeResourceLocal(${mkGoString(resName)}, ${translateExpr(value)})",
                    ctx.copy(bindings = ctx.bindings + resBind))
                  case PCalVariableDeclarationSet(_, set) => (prevDesc + d"\n${ctx.iface}.EnsureArchetypeResourceLocal(${mkGoString(resName)}, ${translateExpr(set)}.SelectElement(0))",
                    ctx.copy(bindings = ctx.bindings + resBind))
                }
              }
              resultDesc.indented
            }\n},").indented
        }\n}"
      }.flattenDescriptions
  }
}
