package main

import (
	"fmt"
	"os"
	"pgo/distsys"
	"sort"
	"strconv"
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

var processName string

var processArgument string

var err error

var globalState *distsys.StateServer

var refs distsys.VarReferences

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
	if len(os.Args) != 3 {
		fmt.Printf("Usage: %s processName(processArgument) ip:port\n", os.Args[0])
		os.Exit(1)
	}
	processPlusArgument := os.Args[1]
	ipPort := os.Args[2]
	processName, processArgument = distsys.ParseProcessId(processPlusArgument)
	peers := []string{"10.0.0.1:12345", "10.0.0.2:12345"}
	coordinator := peers[0]
	globalState, err = distsys.NewStateServer(peers, ipPort, coordinator, map[string]interface{}{
		"b": b,
		"c": c,
		"k": k,
	}, distsys.NewRandomMigrate(ipPort))
	if err != nil {
		panic(err)
	}
}

func P(self int) {
	temp := 0
	temp2 := []int{}
	refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"b"}})
	if err != nil {
		panic(err)
	}
	b = refs.Get("b").([]struct {
		key   int
		value bool
	})
	for {
		if !true {
			refs.Set("b", b)
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
			break
		}
		key := self
		index := sort.Search(len(b), func(i int) bool {
			return !(b[i].key < key)
		})
		b[index].value = false
		refs.Set("b", b)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
	Li1:
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"k"}})
		if err != nil {
			panic(err)
		}
		k = refs.Get("k").(int)
		if k != self {
			refs.Set("k", k)
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
			refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"c"}})
			if err != nil {
				panic(err)
			}
			c = refs.Get("c").([]struct {
				key   int
				value bool
			})
			key0 := self
			index0 := sort.Search(len(c), func(i0 int) bool {
				return !(c[i0].key < key0)
			})
			c[index0].value = true
			refs.Set("c", c)
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
			refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"k"}})
			if err != nil {
				panic(err)
			}
			k = refs.Get("k").(int)
			temp = k
			refs.Set("k", k)
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
			refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"b"}})
			if err != nil {
				panic(err)
			}
			b = refs.Get("b").([]struct {
				key   int
				value bool
			})
			key1 := temp
			index1 := sort.Search(len(b), func(i1 int) bool {
				return !(b[i1].key < key1)
			})
			if b[index1].value {
				refs.Set("b", b)
				err = globalState.Release(refs)
				if err != nil {
					panic(err)
				}
				refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"k"}})
				if err != nil {
					panic(err)
				}
				k = refs.Get("k").(int)
				k = self
				refs.Set("k", k)
				err = globalState.Release(refs)
				if err != nil {
					panic(err)
				}
			} else {
				refs.Set("b", b)
				err = globalState.Release(refs)
				if err != nil {
					panic(err)
				}
			}
			goto Li1
		} else {
			refs.Set("k", k)
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"c"}})
		if err != nil {
			panic(err)
		}
		c = refs.Get("c").([]struct {
			key   int
			value bool
		})
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
		refs.Set("c", c)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"c"}})
		if err != nil {
			panic(err)
		}
		c = refs.Get("c").([]struct {
			key   int
			value bool
		})
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
				refs.Set("c", c)
				err = globalState.Release(refs)
				if err != nil {
					panic(err)
				}
				goto Li1
			}
			refs.Set("c", c)
			err = globalState.Release(refs)
			if err != nil {
				panic(err)
			}
			refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"c"}})
			if err != nil {
				panic(err)
			}
			c = refs.Get("c").([]struct {
				key   int
				value bool
			})
		}
		refs.Set("c", c)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"c"}})
		if err != nil {
			panic(err)
		}
		c = refs.Get("c").([]struct {
			key   int
			value bool
		})
		key1 := self
		index1 := sort.Search(len(c), func(i1 int) bool {
			return !(c[i1].key < key1)
		})
		c[index1].value = true
		refs.Set("c", c)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"b"}})
		if err != nil {
			panic(err)
		}
		b = refs.Get("b").([]struct {
			key   int
			value bool
		})
		key2 := self
		index2 := sort.Search(len(b), func(i2 int) bool {
			return !(b[i2].key < key2)
		})
		b[index2].value = true
		refs.Set("b", b)
		err = globalState.Release(refs)
		if err != nil {
			panic(err)
		}
		refs, err = globalState.Acquire(&distsys.BorrowSpec{ReadNames: []string{}, WriteNames: []string{"b"}})
		if err != nil {
			panic(err)
		}
		b = refs.Get("b").([]struct {
			key   int
			value bool
		})
	}
}

func main() {
	err = globalState.WaitPeers()
	if err != nil {
		panic(err)
	}
	switch processName {
	case "P":
		i, err0 := strconv.Atoi(processArgument)
		if err0 != nil {
			panic("Process P requires an integer argument; err = " + err0.Error())
		}
		P(i)
	default:
		panic("Unknown process " + processName)
	}
	err = globalState.WaitPeers()
	if err != nil {
		panic(err)
	}
}
