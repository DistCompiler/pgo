# How to build the Doozer parts

Make sure this folder is somewhere like `$GOPATH/src/eval`. At least, it should be in your
`$GOPATH` for the `./vendor` directory to get picked up.

Once you've done that, run `go get .` as usual and things should work.

To get a working `doozerd` server, go into `vendor/github.com/ha/doozerd` and `go build .` to get
the desired effect. For a localhost-only deployment just run `./doozerd`. I think the `-l` and `-a`
flags are what you want if you're running across multiple machines.

For basic sanity tests, you can build the `doozer` CLI app by going to
`vendor/github.com/ha/doozer/cmd/doozer` and running `go build .` as usual.
The `--help` flag will show you a bunch of CRUD operations
you can use for basic sanity tests that you're running `doozerd` correctly.

`doozerclient.go` provides a means of interacting with Doozer which seems to work. Throw issues
as @fhackett if they don't. `main.go` contains some example code to set up a basic connection
(reproduced below):

```golang
client, err := DialDoozer("doozer:?ca=127.0.0.1:8046", "") // default addr
if err != nil {
    fmt.Fprintln(os.Stderr, "Error connecting to db:", err)
    os.Exit(1)
}
```

Fun story: the original Doozer source depends on code.google.com - remember when that
was mainstream? (yay Go dependency management that this even mattered...)
The only modifications in these vendor copies are carefully replacing
`"code.google.com/p/goprotobuf/proto"` with `"github.com/golang/protobuf/proto"` and
`"code.google.com/p/go.net/websocket"` with `"golang.org/x/net/websocket"`.

Note that this replacement includes inside old protobuf-generated files. Pray Protobuf never breaks
generated-source compatibility with the old version from 6 years ago :) (or, if it does you know
where to start)

