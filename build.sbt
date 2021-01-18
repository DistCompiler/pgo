name := "pgo"
scalaVersion := "2.13.4"
javacOptions ++= Seq("-source", "1.8")

Compile / javaSource := baseDirectory.value / "src"
Test / javaSource := baseDirectory.value / "test"
Compile / scalaSource := baseDirectory.value / "src"
Test / scalaSource := baseDirectory.value / "test"

unmanagedJars in Compile ++= Seq(
  file("lib/json.jar"),
  file("lib/plume.jar"))

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.2.0-M1"

libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % Test

libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.2" % Test
libraryDependencies += "org.scalatestplus" %% "junit-4-13" % "3.2.2.0" % Test

libraryDependencies += "io.github.java-diff-utils" % "java-diff-utils" % "4.9" % Test