// Main
//> using scala 3.5.2
//> using options -deprecation -Ximport-suggestion-timeout 0
// note: disable import suggestions because this projects stackoverflows it every time (somehow)
//       if this ever gets fixed, you can re-enable it. Try it on new compiler releases...

//> using dependency "com.lihaoyi::os-lib:0.11.3"
//> using dependency "com.lihaoyi::upickle:4.1.0"
//> using dependency "io.github.java-diff-utils:java-diff-utils:4.15"
//> using dependency "org.rogach::scallop:5.2.0"
//> using dependency "org.scala-lang.modules::scala-parser-combinators:2.4.0"

//> using exclude "systems/"

// run setup.sc to populate
//> using resourceDir .tools/

// setup.sc
//> using dep "com.lihaoyi::requests:0.9.0"

// Test
//> using testFramework org.scalatest.tools.Framework
//> using test.dependency "com.github.daddykotex::courier:3.2.0"
//> using test.dependency "com.lihaoyi::mainargs:0.7.6"
//> using test.dependency "com.lihaoyi::pprint:0.9.0"
//> using test.dependency "com.lihaoyi::upickle:4.0.2"
//> using test.dependency "org.scalacheck::scalacheck:1.18.1"
//> using test.dependency "org.scalatest::scalatest:3.2.19"

