# Shopcart CRDT Benchmark

A basic shopping cart application backed with CRDT AWORSet. There are 5 replica nodes concurrently making add and remove requests.
First, all of them will pick a random integer n (0 <= n < `MaxRand`) representing item id to add to the set for `AddRequest` many times.
Then, they will wait for 5 seconds, and remove `RemReqCnt` many random item ids from the set. (Note: in this scenario, they could request to remove
items not yet added.) The background state broadcast frequency is set to 2 seconds.
We measure the time for all nodes to complete the add and remove requests, as well as the time since all request has been sent to the time
all the nodes converges to single cart view.

```
$ go run cmd/main.go
2021/11/27 21:52:02 duration until request complete: 5.0158325s
2021/11/27 21:52:08 duration until converge: 6.4445919s
```
```
final state: {57, 54, 86, 74, 36, 1, 97, 94, 59, 85, 21, 82, 50, 15, 44, 70, 35, 67, 3, 29, 61, 23, 17, 81, 11, 43, 40, 37, 69, 66} (30)
ref state:   {57, 54, 86, 74, 36, 1, 97, 94, 59, 85,     82, 50, 15, 44, 70, 35, 67, 3, 29, 61, 23, 17, 81, 11, 43, 40, 37, 69, 66} (29)
```

It should also be noted that because the underlying CRDT uses add-wins semantics to resolve concurrent addition and removal of an element,
the final state could contain more elements than the ref state, which represent the state of totally ordered operations.
