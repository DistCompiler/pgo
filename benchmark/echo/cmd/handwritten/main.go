package main

import (
	"time"

	"example.com/echo"
	"github.com/UBC-NSS/pgo/distsys/tla"
)

var serverAddr = "localhost:8000"

func server() {
	s := echo.NewEchoServer(serverAddr, tla.MakeTLANumber(1))
	defer s.Close()

	s.ListenAndServe()
}

func client() {
	c := echo.NewEchoClient(serverAddr, tla.MakeTLANumber(2))
	defer c.Close()

	in := make(chan tla.TLAValue)
	out := make(chan tla.TLAValue)
	go func() {
		for req := range in {
			resp, err := c.Call(req)
			if err != nil {
				panic(err)
			}
			out <- resp
		}
	}()

	echo.Benchmark(in, out)

	close(in)
}

func main() {
	go server()

	time.Sleep(1 * time.Second)

	client()
}
