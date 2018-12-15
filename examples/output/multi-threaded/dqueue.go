package main

import (
	"fmt"
	"sync"
)

var queue []string

var pGoStart chan bool

var pGoWait sync.WaitGroup

var pGoLock []sync.RWMutex

func init() {
	queue = []string{}
	pGoStart = make(chan bool)
	pGoLock = make([]sync.RWMutex, 1)
}

func Producer(self int) {
	defer pGoWait.Done()
	<-pGoStart
	for {
		if !true {
			break
		}
		pGoLock[0].Lock()
		if len(queue) < 3 {
			tmpSlice := make([]string, len(queue), len(queue)+1)
			copy(tmpSlice, queue)
			tmpSlice = append(tmpSlice, "resource")
			queue = tmpSlice
		}
		pGoLock[0].Unlock()
	}
}

func Consumer(self int) {
	defer pGoWait.Done()
	<-pGoStart
	resource := ""
	for {
		if !true {
			break
		}
		pGoLock[0].Lock()
		if len(queue) != 0 {
			resource = queue[0]
			queue = queue[1:]
			if !(resource == "resource") {
				panic("(resource)=(\"resource\")")
			}
			fmt.Printf("%v\n", resource)
		}
		pGoLock[0].Unlock()
	}
}

func main() {
	pGoWait.Add(1)
	go Producer(2)
	for _, v := range []int{0, 1} {
		pGoWait.Add(1)
		go Consumer(v)
	}
	close(pGoStart)
	pGoWait.Wait()
}
