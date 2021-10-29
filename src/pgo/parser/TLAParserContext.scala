package pgo.parser

import pgo.model.Definition.{ScopeIdentifier, ScopeIdentifierName}
import pgo.model.mpcal.{MPCalCall, MPCalRefExpr}
import pgo.model.pcal.{PCalAssignmentLhsIdentifier, PCalCall, PCalMacroCall}
import pgo.model.{Definition, DefinitionComposite, DefinitionOne, Visitable}
import pgo.model.tla._

import scala.annotation.tailrec
import scala.collection.mutable

final case class TLAParserContext(minColumn: Int = -1,
                                  lateBindingStack: Int = 0,
                                  currentScope: Map[Definition.ScopeIdentifier,DefinitionOne] = Map.empty,
                                  recursiveOperators: Map[Definition.ScopeIdentifier,TLARecursive.Decl] = Map.empty,
                                  functionSubstitutionPairAnchor: Option[TLAFunctionSubstitutionPairAnchor] = None) {
  def withMinColumn(minColumn: Int): TLAParserContext =
    copy(minColumn=minColumn)

  def withDefinition(defn: Definition): TLAParserContext =
    defn match {
      case defn: TLAOperatorDefinition if currentScope.get(defn.identifier).exists(_.isInstanceOf[TLARecursive.Decl]) =>
        val decl = currentScope(defn.identifier).asInstanceOf[TLARecursive.Decl]
        // this fixes one thing: the recursive directive now properly refers to the operator defn
        // the full-module parser should then go on to properly update any already-made references to the recursive decl
        decl.setRefersTo(defn)
        copy(currentScope = currentScope.updated(defn.identifier, defn))
      case defn: DefinitionOne =>
        copy(currentScope=currentScope.updated(defn.identifier, defn))
      case defn: DefinitionComposite => defn.singleDefinitions.foldLeft(this)(_.withDefinition(_))
    }

  def withFunctionSubstitutionPairAnchor(anchor: TLAFunctionSubstitutionPairAnchor): TLAParserContext =
    copy(functionSubstitutionPairAnchor = Some(anchor))

  def withLateBinding: TLAParserContext =
    copy(lateBindingStack = lateBindingStack + 1)

  /**
   * match any "late bindings" (e.g bindings that are defined after use) up with any unbound parts of the given
   * AST node, or raise a binding error
   *
   * Note: this relies on know what things refer to other things, and should hopefully work on PCal, MPCal, and TLA+,
   *       given references that work via DefinitionOne
   *
   * @param visitable the AST node
   * @param defns the definitions to late-bind
   */
  def resolveLateBindings(visitable: Visitable, defns: IterableOnce[DefinitionOne]): Unit = {
    val defnMap = defns.iterator.map(defn => defn.identifier -> defn).toMap

    // gather all nested unbound names
    // yes, this could end up being really slow, but last time I tried to be smart w/ mutable state or something,
    // a fuzz tester exposed a really weird bug
    val binders = mutable.ListBuffer[(ScopeIdentifier,DefinitionOne=>Unit)]()
    visitable.visit(Visitable.TopDownFirstStrategy) {
      case ident@TLAGeneralIdentifier(name, Nil) if !ident.hasRefersTo => binders += ScopeIdentifierName(name) -> ident.setRefersTo
      case lhs@PCalAssignmentLhsIdentifier(name) if !lhs.hasRefersTo => binders += ScopeIdentifierName(name) -> lhs.setRefersTo
      case ref@MPCalRefExpr(name, _) if !ref.hasRefersTo => binders += ScopeIdentifierName(name) -> ref.setRefersTo
    }

    binders.foreach {
      case (ident, setRef) =>
        defnMap.get(ident) match {
          case Some(defn) => setRef(defn)
          case None =>
            // if the late bindings count is 0 we should check that no idents remain unbound.
            // if so, raise the [AST traversal-wise, probably lexically] "earliest" one as an error.
            // otherwise, unbound idents may still be bound via currently unknown context, so don't do anything
            if(lateBindingStack == 0) {
              throw DefinitionLookupError(Nil, ident)
            }
        }
    }
  }

  def lookupModuleExtends(id: Definition.ScopeIdentifierName): TLAModuleRef =
    currentScope.get(id) match {
      case Some(defn: TLAModule) => TLAModuleRefModule(defn).setSourceLocation(id.sourceLocation)
      case Some(defn) => throw DoesNotExtendAModuleError(id, defn)
      case None => BuiltinModules.builtinModules.get(id) match {
        case Some(builtin) => TLAModuleRefBuiltin(builtin).setSourceLocation(id.sourceLocation)
        case None => throw ModuleNotFoundError(id)
      }
    }

  def instantiateModule(id: Definition.ScopeIdentifierName): TLAParserContext = {
    currentScope.get(id) match {
      case Some(defn: TLAModule) => ???
      case _ => ???
    }
  }

  def lookupDefinition(path: List[Definition.ScopeIdentifier]): Option[DefinitionOne] = {
    path match {
      case Nil => None
      case List(id) => currentScope.get(id)
      case id :: tl =>
        currentScope.get(id).flatMap(lookupDefinition(_, tl))
    }
  }

  @tailrec
  private def lookupDefinition(defn: DefinitionOne, path: List[Definition.ScopeIdentifier]): Option[DefinitionOne] =
    path match {
      case Nil => None
      case List(id) => defn.scope.get(id)
      case hd :: tl =>
        defn.scope.get(hd) match {
          case None => None
          case Some(defn) => lookupDefinition(defn, tl)
        }
    }
}
