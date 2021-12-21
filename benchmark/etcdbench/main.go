package main

import (
	"context"
	"fmt"
	"log"
	"math/rand"
	"sync"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
)

var letterRunes = []rune("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

const valueSize = 10
const keySize = 100
const numClients = 1
const numRequests = 100

func RandStringRunes(n int) string {
	b := make([]rune, n)
	for i := range b {
		b[i] = letterRunes[rand.Intn(len(letterRunes))]
	}
	return string(b)
}

type atomicCounter struct {
	lock sync.RWMutex
	val  int
}

func (ac *atomicCounter) get() int {
	ac.lock.RLock()
	defer ac.lock.RUnlock()
	return ac.val
}

func (ac *atomicCounter) inc() {
	ac.lock.Lock()
	defer ac.lock.Unlock()
	ac.val += 1
}

func average(a []time.Duration) time.Duration {
	var tot time.Duration

	for _, e := range a {
		tot += e
	}
	return time.Duration(int64(tot) / int64(len(a)))
}

func main() {
	cli, err := clientv3.New(clientv3.Config{
		Endpoints:   []string{"127.0.0.1:2379", "127.0.0.2:2379", "127.0.0.3:2379"},
		DialTimeout: 5 * time.Second,
	})
	if err != nil {
		log.Fatal(err)
	}
	defer func() {
		if err := cli.Close(); err != nil {
			log.Println(err)
		}
	}()

	ctx := context.Background()

	var keys []string
	for i := 0; i < keySize; i++ {
		key := fmt.Sprintf("key%d", i)
		_, err := cli.Put(ctx, key, RandStringRunes(valueSize))
		if err != nil {
			log.Fatal(err)
		}
		keys = append(keys, key)
	}

	log.Println("setup done")

	start := time.Now()

	var latencies []time.Duration
	var lock sync.Mutex

	reqCnt := atomicCounter{val: 0}
	var wg sync.WaitGroup
	for k := 0; k < numClients; k++ {
		wg.Add(1)

		go func() {
			for reqCnt.get() < numRequests {
				key := keys[rand.Intn(len(keys))]
				r := rand.Intn(2) + 1
				reqStart := time.Now()

				var err error
				if r%2 == 0 {
					_, err = cli.Put(ctx, key, RandStringRunes(valueSize))
				} else {
					_, err = cli.Get(ctx, key)
				}
				if err != nil {
					log.Fatal(err)
				}

				reqElapsed := time.Since(reqStart)

				lock.Lock()
				latencies = append(latencies, reqElapsed)
				lock.Unlock()

				reqCnt.inc()
			}
			wg.Done()
		}()
	}

	wg.Wait()

	elapsed := time.Since(start)
	iops := float64(numRequests) / elapsed.Seconds()
	avgLatency := average(latencies)

	fmt.Printf("elapsed = %s, iops = %f, average latency = %s\n", elapsed, iops, avgLatency)
}
