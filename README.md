# PGo #

## Purpose/motivation

TLA+ is a specification language for distributed systems. Coupled with a TLC model checker, TLA+ allows for verification of distributed systems and algorithms. PlusCal is a C-syntax based language that allows for easier writing of TLA+, which is written in set and mathematical notation. https://github.com/tlaplus

Go is a C based language developed by Google for developing distributed systems. Go has built in support for concurrency with channels, and goroutines, which makes it very practical for developing distributed systems.

TLA+ specification and Go implementation is not related. PGo is a tool that aims to connect the specification with the implementation through allowing the generation of Go code based on a PlusCal specification. PGo would allow developers to translate a verified PlusCal specification of a distributed system algorithm into a valid Go program.

## Current status

Under development. 

## How does it work

PGo acts as a source to source compiler written in Java. It uses TLA+ toolset to parse PlusCal into an AST, which is then translated to a Go AST, and finally written.

## How do install it?

Requirements: JRE8, and one of Eclipse or Ant 1.9

1. First download the source

2. Option 1: Import as an Eclipse project
Option 2: Execute `ant pgo` assuming the project is in the `pgo/` directory

## How to use it? e.g., command line usage/how to run test suite
I don't know yet