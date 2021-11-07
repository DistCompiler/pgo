package echo

import (
	"log"
	"time"

	"github.com/UBC-NSS/pgo/distsys/tla"
)

const ReqCnt = 10000

func Benchmark(in, out chan tla.TLAValue) {
	start := time.Now()
	for i := 0; i < ReqCnt; i++ {
		in <- tla.MakeTLANumber(int32(i))
		resp := <-out
		if resp.AsNumber() != int32(i) {
			panic("wrong response")
		}
	}
	elapsed := time.Since(start)
	log.Printf("duration: %s", elapsed)
}
