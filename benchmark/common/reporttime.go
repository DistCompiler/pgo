package benchmark

import (
	"fmt"
	"log"
	"os"
	"time"
	"strconv"
)

func GetEnvInt(key string, fallback int) int {
	value := os.Getenv(key)
	if value == "" {
		return fallback
	} else {
		numeric, err := strconv.Atoi(value)
		if err != nil {
			panic(fmt.Sprintf("Could not parse env variable %s=%s", key, value))
		}
		return numeric
	}
}

func AppendToResults(content string) {
    f, err := os.OpenFile("results.txt", os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
    if err != nil {
        log.Fatal(err)
    }
    if _, err := f.Write([]byte(content)); err != nil {
        log.Fatal(err)
    }
    if err := f.Close(); err != nil {
        log.Fatal(err)
    }
}

func TestAndReport(runTest func(int)) {
	numNodes := GetEnvInt("NUM_NODES", 20)
	numIterations := GetEnvInt("PGO_BENCHMARK_ITERATIONS", 1)
	totalTime := 0
	for i := 0; i < numIterations; i++ {
		start := time.Now()
		runTest(numNodes)
		elapsed := time.Since(start)
		fmt.Printf("Iteration %d completed in %s\n", i + 1, elapsed)
		totalTime += int(elapsed.Milliseconds())
	}
	logContent := fmt.Sprintf("%d %d\n", numNodes, totalTime / numIterations)
	AppendToResults(logContent)

}
