// Main
//> using scala 3
//> using options -deprecation -Ximport-suggestion-timeout 0
// note: disable import suggestions because this project stackoverflows it every time (somehow)
//       if this ever gets fixed, you can re-enable it. Try it on new compiler releases...

//> using dependency "com.lihaoyi::os-lib:0.11.4"
//> using dependency "com.lihaoyi::upickle:4.2.1"
//> using dependency "io.github.java-diff-utils:java-diff-utils:4.15"
//> using dependency "org.rogach::scallop:5.2.0"
//> using dependency "org.scala-lang.modules::scala-parser-combinators:2.4.0"

//> using exclude "systems/"

// run setup.sc to populate
//> using resourceDir .tools/

// setup.sc
//> using dep "com.lihaoyi::requests:0.9.0"

// Test
///> using testFramework munit.Framework
//> using test.dependency "com.github.daddykotex::courier:3.2.0"
//> using test.dependency "com.lihaoyi::mainargs:0.7.6"
//> using test.dependency "com.lihaoyi::pprint:0.9.0"
//> using test.dependency org.scalameta::munit::1.1.1
//> using test.dependency org.scalameta::munit-scalacheck:1.1.0
