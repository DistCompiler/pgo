package shopcart_test

import (
	"fmt"
	"log"
	"sync"
	"testing"
	"time"

	"github.com/DistCompiler/pgo/systems/shopcart"
	"github.com/DistCompiler/pgo/systems/shopcart/configs"
	"github.com/UBC-NSS/pgo/distsys/hashmap"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

func TestShopCart(t *testing.T) {
	c, err := configs.ReadConfig("configs/local-3.yaml")
	if err != nil {
		t.Fatal(err)
	}

	var wg sync.WaitGroup
	wg.Add(len(c.Peers))

	var nodes []*shopcart.Node
	for id := range c.Peers {
		nid := id
		ch := make(chan shopcart.Event, 10)

		node := shopcart.NewNode(nid, c, ch)
		nodes = append(nodes, node)

		go func() {
			if err := node.Run(); err != nil {
				log.Println(err)
			}
		}()

		go func() {
			var start time.Time
			roundIdx := 0
			numEvents := 2 * c.NumRounds
			for i := 0; i < numEvents; i++ {
				e := <-ch
				// log.Println(nid, e)
				if e == shopcart.AddStartEvent {
					start = time.Now()
				} else if e == shopcart.AddFinishEvent {
					elapsed := time.Since(start)
					fmt.Println("RESULT", roundIdx, nid, elapsed)
					roundIdx += 1
				}
			}
			wg.Done()
		}()
	}

	wg.Wait()

	for _, node := range nodes {
		node.Close()
	}
}

func TestHashMap(t *testing.T) {
	t1 := tla.MakeTLATuple(tla.MakeTLANumber(1), tla.MakeTLANumber(0))
	t2 := tla.MakeTLATuple(tla.MakeTLANumber(2), tla.MakeTLANumber(0))

	fmt.Println(t1, t1.Hash())
	fmt.Println(t2, t2.Hash())

	h := hashmap.New[bool]()
	h.Set(t1, true)

	val, ok := h.Get(t2)
	fmt.Println(val, ok)
}
