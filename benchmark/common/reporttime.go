package benchmark

import (
	"fmt"
	"os"
	"strconv"
	"time"
)

func getEnvInt(key string, fallback int) int {
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

func TestAndReport(runTest func(int, time.Duration)) {
	numNodes := getEnvInt("NUM_NODES", 20)
	//numIterations := getEnvInt("PGO_BENCHMARK_ITERATIONS", 1)
	broadcastInterval := getEnvInt("BROADCAST_INTERVAL", 5)
	totalTime := 0
	for i := 0; i < 1; i++ {
		start := time.Now()
		runTest(numNodes, time.Duration(broadcastInterval) * time.Second)
		elapsed := time.Since(start)
		fmt.Printf("Iteration %d completed in %s\n", i + 1, elapsed)
		totalTime += int(elapsed.Milliseconds())
	}
	//f, err := os.OpenFile("results.txt", os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	//if err != nil {
	//	log.Fatal(err)
	//}
	//logContent := fmt.Sprintf("%d %d\n", numNodes, totalTime / numIterations)
	//if _, err := f.Write([]byte(logContent)); err != nil {
	//	log.Fatal(err)
	//}
	//if err := f.Close(); err != nil {
	//	log.Fatal(err)
	//}

}