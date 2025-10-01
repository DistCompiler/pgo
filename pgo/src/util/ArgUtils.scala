package pgo.util

import org.rogach.scallop
import org.rogach.scallop.ValueConverter
import scala.concurrent.duration.Duration

object ArgUtils:
  given pathConverter: ValueConverter[os.Path] =
    scallop.singleArgConverter(os.Path(_, os.pwd))
  given listOfPathConverter: ValueConverter[List[os.Path]] =
    scallop.listArgConverter(os.Path(_, os.pwd))
  given durationConverter: ValueConverter[Duration] =
    scallop.singleArgConverter(Duration.apply)
end ArgUtils
