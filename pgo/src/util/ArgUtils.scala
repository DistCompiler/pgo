package pgo.util

import scala.concurrent.duration.Duration

import org.rogach.scallop
import org.rogach.scallop.ValueConverter

object ArgUtils:
  given pathConverter: ValueConverter[os.Path] =
    scallop.singleArgConverter(os.Path(_, os.pwd))
  given listOfPathConverter: ValueConverter[List[os.Path]] =
    scallop.listArgConverter(os.Path(_, os.pwd))
  given durationConverter: ValueConverter[Duration] =
    scallop.singleArgConverter(Duration.apply)
end ArgUtils
