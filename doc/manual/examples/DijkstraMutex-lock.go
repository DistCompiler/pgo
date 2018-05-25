package main

import (
	"math/rand"
	"pgo/datatypes"
	"sync"
	"time"
)

var PGoLock []sync.RWMutex = make([]sync.RWMutex, 3)
var Proc datatypes.Set = datatypes.Sequence(1, 10)
var k int           // PGo inferred type int; Lock group 2
var b datatypes.Map // PGo inferred type map[int]bool; Lock group 0
var c datatypes.Map // PGo inferred type map[int]bool; Lock group 1
var PGoWait sync.WaitGroup
var PGoStart chan bool = make(chan bool)

func P(self int) {
	var temp int            // PGo inferred type int
	var temp2 datatypes.Set // PGo inferred type set[int]
	defer PGoWait.Done()
	<-PGoStart
	for true {
		PGoLock[0].Lock()
		b.Put(self, false)
		PGoLock[0].Unlock()
	Li1:
		if k != self {
			PGoLock[1].Lock()
			c.Put(self, true)
			PGoLock[1].Unlock()
			temp = k
			if b.Get(temp).(bool) {
				PGoLock[2].Lock()
				k = self
				PGoLock[2].Unlock()
			}
			goto Li1
		}
		PGoLock[1].Lock()
		c.Put(self, false)
		temp2 = Proc.Difference(datatypes.NewSet(self))
		PGoLock[1].Unlock()
		for !datatypes.NewSet().Equal(temp2) {
			{
				var j int = temp2.ToSlice()[rand.Intn(temp2.Size())].(int) // PGo inferred type int
				temp2 = temp2.Difference(datatypes.NewSet(j))
				if !c.Get(j).(bool) {
					goto Li1
				}
			}
		}
		// TODO skipped from pluscal
		PGoLock[1].Lock()
		c.Put(self, true)
		PGoLock[1].Unlock()
		PGoLock[0].Lock()
		b.Put(self, true)
		PGoLock[0].Unlock()
		// TODO skipped from pluscal
	}
}

func main() {
	rand.Seed(time.Now().UnixNano())
	for k_interface := range Proc.Iter() {
		k = k_interface.(int)
		b = datatypes.MapsTo(func(i int) bool {
			return true
		}, Proc)
		c = datatypes.MapsTo(func(i int) bool {
			return true
		}, Proc)
		for procId := range Proc.Iter() {
			PGoWait.Add(1)
			go P(procId.(int))
		}
		close(PGoStart)
		PGoWait.Wait()
	}
}
