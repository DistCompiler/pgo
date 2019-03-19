package main

import (
	"sort"
	"sync"
)

var Proc []int

var b []struct {
	key   int
	value bool
}

var c []struct {
	key   int
	value bool
}

var k int

var pGoStart chan bool

var pGoWait sync.WaitGroup

var pGoLock []sync.RWMutex

func init() {
	tmpRange := make([]int, 3-1+1)
	for i := 1; i <= 3; i++ {
		tmpRange[i-1] = i
	}
	Proc = tmpRange
	function := make([]struct {
		key   int
		value bool
	}, 0, len(Proc))
	for _, i := range Proc {
		function = append(function, struct {
			key   int
			value bool
		}{key: i, value: true})
	}
	b = function
	function0 := make([]struct {
		key   int
		value bool
	}, 0, len(Proc))
	for _, i := range Proc {
		function0 = append(function0, struct {
			key   int
			value bool
		}{key: i, value: true})
	}
	c = function0
	k = Proc[0]
	pGoStart = make(chan bool)
	pGoLock = make([]sync.RWMutex, 3)
}

func P(self int) {
	defer pGoWait.Done()
	<-pGoStart
	temp := 0
	temp2 := []int{}
	pGoLock[1].Lock()
	for {
		if !true {
			pGoLock[1].Unlock()
			break
		}
		key := self
		index := sort.Search(len(b), func(i int) bool {
			return !(b[i].key < key)
		})
		b[index].value = false
		pGoLock[1].Unlock()
	Li1:
		pGoLock[0].Lock()
		if k != self {
			pGoLock[0].Unlock()
			pGoLock[2].Lock()
			key0 := self
			index0 := sort.Search(len(c), func(i0 int) bool {
				return !(c[i0].key < key0)
			})
			c[index0].value = true
			pGoLock[2].Unlock()
			pGoLock[0].Lock()
			temp = k
			pGoLock[0].Unlock()
			pGoLock[1].Lock()
			key1 := temp
			index1 := sort.Search(len(b), func(i1 int) bool {
				return !(b[i1].key < key1)
			})
			if b[index1].value {
				pGoLock[1].Unlock()
				pGoLock[0].Lock()
				k = self
				pGoLock[0].Unlock()
			} else {
				pGoLock[1].Unlock()
			}
			goto Li1
		} else {
			pGoLock[0].Unlock()
		}
		pGoLock[2].Lock()
		key0 := self
		index0 := sort.Search(len(c), func(i0 int) bool {
			return !(c[i0].key < key0)
		})
		c[index0].value = false
		tmpSet := make([]int, 0, len(Proc))
		for _, v := range Proc {
			if v != self {
				tmpSet = append(tmpSet, v)
			}
		}
		temp2 = tmpSet
		pGoLock[2].Unlock()
		pGoLock[2].Lock()
		for {
			if !(len(temp2) != 0) {
				break
			}
			j := temp2[0]
			tmpSet0 := make([]int, 0, len(temp2))
			for _, v := range temp2 {
				if v != j {
					tmpSet0 = append(tmpSet0, v)
				}
			}
			temp2 = tmpSet0
			key1 := j
			index1 := sort.Search(len(c), func(i1 int) bool {
				return !(c[i1].key < key1)
			})
			if !c[index1].value {
				pGoLock[2].Unlock()
				goto Li1
			}
			pGoLock[2].Unlock()
			pGoLock[2].Lock()
		}
		pGoLock[2].Unlock()
		pGoLock[2].Lock()
		key1 := self
		index1 := sort.Search(len(c), func(i1 int) bool {
			return !(c[i1].key < key1)
		})
		c[index1].value = true
		pGoLock[2].Unlock()
		pGoLock[1].Lock()
		key2 := self
		index2 := sort.Search(len(b), func(i2 int) bool {
			return !(b[i2].key < key2)
		})
		b[index2].value = true
		pGoLock[1].Unlock()
		pGoLock[1].Lock()
	}
}

func main() {
	for _, v := range Proc {
		pGoWait.Add(1)
		go P(v)
	}
	close(pGoStart)
	pGoWait.Wait()
}
