
ThisBuild / scalaVersion := "2.13.6"

lazy val pgo = (project in file("."))
  .settings(
    name := "pgo",

    Compile / scalaSource := baseDirectory.value / "src",
    Test / scalaSource := baseDirectory.value / "test",

    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,

    libraryDependencies += "org.rogach" %% "scallop" % "4.0.3",

    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.0.0",
    libraryDependencies += "com.lihaoyi" %% "os-lib" % "0.7.8",

    libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.15.4" % Test,
    libraryDependencies += "com.lihaoyi" %% "pprint" % "0.6.6" % Test,
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.9" % Test,
    libraryDependencies += "io.github.java-diff-utils" % "java-diff-utils" % "4.11" % Test,

    libraryDependencies += "com.lihaoyi" %% "mainargs" % "0.2.1" % Test,
  )