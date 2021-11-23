# Echo Server Benchmark

A simple echo server benchmark. A client sequentially sends requests to the
server and waits for the response. After getting the response, the client 
retries. We measured the time it takes to finish this procedure for 10,000
requests. We tested PGo compiled Go output versus a handwritten echo server
in Go. The handwritten server uses raw TCP connections. The send and
received messages are the same in both systems. So the  serailization/deserialization 
cost for both systems should be equal.
The tests are done on an M1 Macbook Air.

```
$ go run cmd/handwritten/main.go
2021/11/08 17:46:07 duration: 1.281992334s
```

```
# using relaxed mailboxes
$ go run cmd/pgo/main.go -mbox relaxed
2021/11/08 17:47:29 duration: 1.572924875
```

```
# using tcp mailboxes
$ go run cmd/pgo/main.go -mbox tcp
2021/11/08 17:48:24 duration: 2.375066292s
```