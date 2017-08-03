package main

import (
	"math/rand"
	"pgoutil"
	"sync"
	"time"
)

var k int
var b pgoutil.Map
var c pgoutil.Map
var Proc pgoutil.Set
var PGoWait sync.WaitGroup
var PGoStart chan bool = make(chan bool)

func P(self int)  {
	var temp int
	var temp2 pgoutil.Set
	defer PGoWait.Done()
	<-PGoStart
	for true {
		b.Put(self, false)
		Li1:
		if k != self {
			c.Put(self, true)
			temp = k
			if b.Get(temp).(bool) {
				k = self
			}
			goto Li1
		}
		c.Put(self, false)
		temp2 = Proc.Difference(pgoutil.NewSet(self))
		for !pgoutil.NewSet().Equal(temp2) {
			{
				j := temp2.ToSlice()[rand.Intn(temp2.Size())].(int)
				temp2 = temp2.Difference(pgoutil.NewSet(j))
				if !c.Get(j).(bool) {
					goto Li1
				}
			}
		}
		// TODO skipped from pluscal
		c.Put(self, true)
		b.Put(self, true)
		// TODO skipped from pluscal
	}
}

func main()  {
	rand.Seed(time.Now().UnixNano())
	for k_interface := range Proc.Iter() {
		k = k_interface.(int)
		b = pgoutil.MapsTo(func(i int) bool {
				return true
			}, Proc)
		c = pgoutil.MapsTo(func(i int) bool {
				return true
			}, Proc)
		Proc = pgoutil.Sequence(1, 10)
		for procId := range Proc.Iter() {
			PGoWait.Add(1)
			go P(procId.(int))
		}
		close(PGoStart)
		PGoWait.Wait()
	}
}
