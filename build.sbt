
ThisBuild / scalaVersion := "2.13.6"

lazy val pgo = (project in file("."))
  .settings(
      name := "pgo",

      scalacOptions += "-deprecation",

      Compile / scalaSource := baseDirectory.value / "src",
      Test / scalaSource := baseDirectory.value / "test",

      libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,

      libraryDependencies += "org.rogach" %% "scallop" % "4.1.0",

      libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1",
      libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.8.1",

      libraryDependencies += "com.lihaoyi" %% "upickle" % "1.5.0",
      libraryDependencies += "io.github.java-diff-utils" % "java-diff-utils" % "4.11",
      libraryDependencies += "com.lihaoyi" % "ammonite" % "2.5.2" cross CrossVersion.full,

      libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.15.4" % Test,
      libraryDependencies += "com.lihaoyi" %% "pprint" % "0.7.1" % Test,
      libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.11" % Test,

      libraryDependencies += "com.lihaoyi" %% "mainargs" % "0.2.2" % Test,
      libraryDependencies += "com.lihaoyi" %% "upickle" % "1.5.0" % Test,
      libraryDependencies += "com.github.daddykotex" %% "courier" % "3.1.0" % Test,
  )