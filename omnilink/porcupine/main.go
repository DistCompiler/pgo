package main

import (
	"fmt"
	"os"

	"github.com/anishathalye/porcupine"
	"github.com/distcompiler/pgo/omnilink/porcupine/setbench"
)

func main() {
	if len(os.Args) < 3 {
		panic(fmt.Errorf("Too few command-line arguments, got: %v. Need mode then tracefile.", os.Args))
	}
	var err error
	mode, traceFile := os.Args[1], os.Args[2]
	var model porcupine.Model
	var ops []porcupine.Operation
	switch mode {
	case "setbench":
		ops, err = setbench.LoadOperations(traceFile)
		if err != nil {
			panic(err)
		}
		model = setbench.SetBenchModel
	default:
		panic(fmt.Errorf("Invalid mode %s. Options: setbench", mode))
	}

	result, info := porcupine.CheckOperationsVerbose(model, ops, 0)
	fmt.Printf("Linearizability check result: %v, writing path to ./viz.html\n", result)
	err = porcupine.VisualizePath(model, info, "./viz.html")
	if err != nil {
		panic(err)
	}

	if result != porcupine.Ok {
		os.Exit(1)
	}
}
