package pgo.parser

import pgo.model.mpcal.ModularPlusCalArchetype
import pgo.model.tla.{TLADefinitionOne, TLAGeneralIdentifierPart, TLAIdentifier}
import pgo.util.SourceLocation

sealed abstract class ParsingError(msg: String) extends RuntimeException(msg)

final case class DefinitionLookupError(loc: SourceLocation, pfx: List[TLAGeneralIdentifierPart],
                                       id: TLAIdentifier) extends ParsingError(
  s"""${loc.prettyString}
     |identifier ${pfx.mkString("!")}${if(pfx.nonEmpty){"!"} else {""}}$id does not refer to a known definition""".stripMargin)

final case class ModuleNotFoundError(loc: SourceLocation, id: TLAIdentifier) extends ParsingError(
  s"""${loc.prettyString}
     |module $id not found""".stripMargin)

final case class DoesNotExtendAModuleError(loc: SourceLocation, id: TLAIdentifier, badDefn: TLADefinitionOne) extends ParsingError(
  s"""${loc.prettyString}
     |found a definition when looking for module $id, but it is not a module. found $badDefn instead""".stripMargin)

final case class ArityMismatchError(loc: SourceLocation, defn: TLADefinitionOne, actualArity: Int) extends ParsingError(
  s"""${loc.prettyString}
     |arity mismatch: expected ${defn.arity}, found $actualArity""".stripMargin)

final case class ArchetypeArityMismatchError(loc: SourceLocation, archetype: ModularPlusCalArchetype, actualArity: Int) extends ParsingError(
  s"""${loc.prettyString}
     |archetype arity mismatch: expected ${archetype.getParams.size()}, found $actualArity""".stripMargin)

final case class KindMismatchError(loc: SourceLocation) extends ParsingError(
  s"""${loc.prettyString}
     |kind mismatch""".stripMargin)

final case class ParseFailureError(err: String, loc: SourceLocation) extends ParsingError(
  s"""${loc.prettyString}
     |parsing failed: $err""".stripMargin)
