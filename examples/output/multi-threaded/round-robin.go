package main

import (
	"fmt"
	"sync"
)

var iters int

var procs int

var counter int

var token int

var pGoStart chan bool

var pGoWait sync.WaitGroup

var pGoLock []sync.RWMutex

func init() {
	iters = 10
	procs = 3
	counter = 0
	token = -1
	pGoStart = make(chan bool)
	pGoLock = make([]sync.RWMutex, 1)
}

func P(self int) {
	defer pGoWait.Done()
	<-pGoStart
	i := 0
	for {
		if !(i < iters) {
			break
		}
	waitToken:
		pGoLock[0].Lock()
		if !(token == -1 || token == self) {
			pGoLock[0].Unlock()
			goto waitToken
		}
		pGoLock[0].Unlock()
		pGoLock[0].Lock()
		counter = counter + 1
		token = (self + 1) % procs
		fmt.Printf("%v\n", counter)
		pGoLock[0].Unlock()
		i = i + 1
	}
}

func main() {
	tmpRange := make([]int, procs-1-0+1)
	for i := 0; i <= procs-1; i++ {
		tmpRange[i-0] = i
	}
	for _, v := range tmpRange {
		pGoWait.Add(1)
		go P(v)
	}
	close(pGoStart)
	pGoWait.Wait()
}
