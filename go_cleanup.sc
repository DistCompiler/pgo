// clean up Go .mod files in all the generated Go projects

os.walk(os.pwd)
  .filter(os.isDir)
  .filter(dir => os.exists(dir / "go.mod"))
  .foreach:
    dir =>
      val relativeDir = dir.relativeTo(os.pwd)
      println(s"updating $dir...")

      val originalMod = os.read(dir / "go.mod")
      final case class Patch(pred: String => Boolean, patch: String)
      val patches: List[Patch] = List(
        Patch(
          pred = _.startsWith("module "),
          patch = s"module github.com/DistCompiler/pgo/$relativeDir\n",
        ),
        // Patch(
        //   pred = _.startsWith("\tgithub.com/DistCompiler/pgo/distsys "),
        //   patch = "",
        // ),
        // Patch(
        //   pred = _.startsWith("require github.com/DistCompiler/pgo/distsys "),
        //   patch = "",
        // ),
        // Patch(
        //   pred = _.startsWith("\tgithub.com/DistCompiler/pgo/distsys "),
        //   patch = "\tgithub.com/DistCompiler/pgo/distsys v0.0.0\n",
        // ),
        // Patch(
        //   pred = _.startsWith("require github.com/DistCompiler/pgo/distsys "),
        //   patch = "require github.com/DistCompiler/pgo/distsys v0.0.0\n",
        // ),
      )

      def patchLineIfNecessary(line: String): String =
        patches.find(patch => patch.pred(line)) match
          case None => line
          case Some(Patch(_, patch)) if line != patch =>
            if patch.nonEmpty
            then
              print(s"  !< $line")
              print(s"  !> $patch")
            else print(s"  !- $line")
            patch
          case Some(_) => line

      os.write.over(
        dir / "go.mod",
        originalMod.linesWithSeparators
          .map(patchLineIfNecessary),
      )

      // val getCmd = os.proc("go", "get", "-u", s"github.com/DistCompiler/pgo/$relativeDir")
      // println(s"[$relativeDir]$$ ${getCmd.commandChunks.mkString(" ")}")
      // getCmd.call(cwd = dir, mergeErrIntoOut = true, stdout = os.Inherit)

      // val tidyCmd = os.proc("go", "mod", "tidy")
      // println(s"[$relativeDir]$$ ${tidyCmd.commandChunks.mkString(" ")}")
      // tidyCmd.call(cwd = dir, mergeErrIntoOut = true, stdout = os.Inherit)
