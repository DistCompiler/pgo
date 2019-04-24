package main

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"strconv"
	"time"
)

const (
	BUFFER_SIZE = 4096

	DUMMY_CLIENT = iota
	DOOZER_CIENT
	ETCD_CLIENT
	PAXOS_CLIENT
)

var (
	firstTimeStamp time.Time
	initChan       = make(chan bool, 0)
	startChan      = make(chan bool, 0)
	doneChan       = make(chan bool, 0)
)

func fatal(message string, status int) {
	fmt.Fprintf(os.Stderr, "%s\n", message)
	os.Exit(status)
}

func usage(programName string) {
	fatal(fmt.Sprintf("Usage: %s <dummy|doozer|etcd|paxos> <nworker> [<address1>..<addressN>]", programName), 1)
}

func parseClient(client string) int {
	switch client {
	case "dummy":
		return DUMMY_CLIENT
	case "doozer":
		return DOOZER_CIENT
	case "etcd":
		return ETCD_CLIENT
	case "paxos":
		return PAXOS_CLIENT
	default:
		fatal(fmt.Sprintf("Unknown client: %s\n", client), 1)
		return -1
	}
}

func createClient(which int, addresses []string) Client {
	switch which {
	case DUMMY_CLIENT:
		return NewDummyClient()
	case DOOZER_CIENT:
		client, err := DialDoozer(addresses[0], "")
		if err != nil {
			fatal(fmt.Sprintf("Error connecting to Doozer client: %v", err), 2)
		}
		return client
	case ETCD_CLIENT:
		client, err := NewEtcdClient(addresses[0])
		if err != nil {
			fatal(fmt.Sprintf("Error connecting to etcd client: %v", err), 2)
		}
		return client
	case PAXOS_CLIENT:
		client, err := NewPaxosClient(addresses)
		if err != nil {
			fatal(fmt.Sprintf("Error connecting to Paxos client: %v", err), 2)
		}

		return client
	default:
		panic(fmt.Sprintf("Unknown client: %d", which))
	}
}

func readToken(buffer []byte) int {
	for i, v := range buffer {
		if v == ' ' || v == '\n' {
			return i
		}
	}
	return len(buffer)
}

func issueGet(self int, client Client, key string) (time.Time, time.Duration) {
	before := time.Now()
	_, err := client.Get(key)
	if err != nil {
		fmt.Fprintln(os.Stdout, "Unable to issue get for worker", self)
		panic(err)
	}
	after := time.Now()

	return after, after.Sub(before)
}

func issuePut(self int, client Client, key string, value string) (time.Time, time.Duration) {
	before := time.Now()
	err := client.Put(key, value)
	if err != nil {
		fmt.Fprintln(os.Stdout, "Unable to issue put for worker", self)
		panic(err)
	}
	after := time.Now()

	return after, after.Sub(before)
}

func outputToLog(output *bufio.Writer, opType byte, offset time.Duration, latency time.Duration) {
	fmt.Fprintf(output, "%c %d %d\n", opType, offset, latency)
}

func worker(self int, which int, address string) {
	// set up connection to implementation
	// example: client := createClient(1, "doozer:?ca=127.0.0.1:8046")
	client := createClient(which, os.Args[3:])
	defer client.Close()

	output, err := os.Create(fmt.Sprintf("output/worker-%d.out", self))
	if err != nil {
		fmt.Fprintln(os.Stderr, "Unable to open output for worker", self)
		os.Exit(1)
	}
	writer := bufio.NewWriter(output)
	defer output.Close()

	input, err := os.Open(fmt.Sprintf("input/worker-%d.inp", self))
	if err != nil {
		fmt.Fprintln(os.Stderr, "Unable to open input for worker", self)
		os.Exit(1)
	}
	defer input.Close()

	initChan <- true
	<-startChan

	// bench
	buffer := make([]byte, BUFFER_SIZE)
	current := 0
	end := 0
	readMore := false
	lastTokenLength := -1

	for {
		switch {
		case end <= current:
			// we're completely out of data in the buffer
			n, err := input.Read(buffer)
			if err == io.EOF {
				// we're done!
				goto workerDone
			}
			if err != nil {
				fmt.Fprintln(os.Stderr, "Error reading from input:", err, "for worker", self)
				os.Exit(1)
			}
			// we got more data
			current = 0
			end = n
			readMore = false
			lastTokenLength = -1
		case end-current <= 4 || readMore:
			// there is some data left in the buffer but the data is only partial
			// so we need to read more
			// copy the remaining data to the start of the buffer
			n := copy(buffer, buffer[current:end])
			if n != end-current {
				fmt.Fprintf(os.Stderr, "Error copying data within buffer: %d bytes copied but %d bytes needed copying for worker %d\n", n, end-current, self)
				os.Exit(1)
			}
			n, err := input.Read(buffer[end-current:])
			if err != io.EOF && err != nil {
				fmt.Fprintln(os.Stderr, "Error reading from input:", err, "for worker", self)
				os.Exit(1)
			}
			// we (maybe) got more data
			end = end - current + n
			current = 0
			readMore = false
		default:
			switch buffer[current] {
			case 'g':
				// move reading head
				//     |
				//     v
				// get key
				i := current + 4
				// read the key
				tokenLength := readToken(buffer[i:end])
				if tokenLength == end-i && lastTokenLength < tokenLength {
					// we're in a situation like the following
					//   get k|ey
					// where | is the cut off because there was not enough space to read into the buffer
					// retry since there might be more data
					readMore = true
					lastTokenLength = tokenLength
					continue
				}
				// condition here: tokenLength < end-i || lastTokenLength == tokenLength
				// we've retried and there's no more data
				key := string(buffer[i : i+tokenLength])
				if tokenLength < end-i && buffer[i+tokenLength] != '\n' {
					fmt.Fprintln(os.Stderr, "Get command must be followed by new line; found", string(buffer[current:end]), "for worker", self)
					os.Exit(1)
				}

				// time to issue the get!
				timestamp, latency := issueGet(self, client, key)
				outputToLog(writer, 'g', timestamp.Sub(firstTimeStamp), latency)

				lastTokenLength = -1
				readMore = false
				current = i + tokenLength + 1
			case 'p':
				// move reading head
				//     |
				//     v
				// put key val
				i := current + 4
				// read the key
				tokenLength := readToken(buffer[i:end])
				if tokenLength == end-i && lastTokenLength < tokenLength {
					// we're in a situation like the following
					//   put k|ey value
					// where | is the cut off because there was not enough space to read into the buffer
					// retry since there might be more data
					readMore = true
					lastTokenLength = tokenLength
					continue
				}
				if tokenLength == end-i {
					fmt.Fprintln(os.Stderr, "Incomplete command:", string(buffer[current:end]), "for worker", self)
					os.Exit(1)
				}
				// condition here: tokenlength < end-token
				key := string(buffer[i : i+tokenLength])
				if buffer[i+tokenLength] != ' ' {
					fmt.Fprintln(os.Stderr, "Ill-formed command:", string(buffer[current:end]), "for worker", self)
					os.Exit(1)
				}
				// read the value
				i += tokenLength + 1
				tokenLength = readToken(buffer[i:end])
				if tokenLength == end-i && lastTokenLength < tokenLength {
					// we're in a situation like the following
					//   put key v|alue
					// where | is the cut off because there was not enough space to read into the buffer
					// retry since there might be more data
					readMore = true
					lastTokenLength = tokenLength
					continue
				}
				// condition here: tokenLength < end-i || lastTokenLength == tokenLength
				if tokenLength < end-i && buffer[i+tokenLength] != '\n' {
					fmt.Println(string(buffer[i+tokenLength:i+tokenLength+1]), buffer[i+tokenLength] == '\n')
					fmt.Fprintln(os.Stderr, "Put command must be followed by new line; found", string(buffer[current:end]), "for worker", self)
					os.Exit(1)
				}
				// we've (possibly) retried and there's no more data
				value := string(buffer[i : i+tokenLength])

				// time to issue the put!
				timestamp, latency := issuePut(self, client, key, value)
				outputToLog(writer, 'p', timestamp.Sub(firstTimeStamp), latency)

				lastTokenLength = -1
				readMore = false
				current = i + tokenLength + 1
			default:
				fmt.Fprintln(os.Stderr, "Unknown command:", string(buffer[current:current+3]), "for worker", self)
				os.Exit(1)
			}
		}
	}
workerDone:
	doneChan <- true
}

func main() {
	if len(os.Args) < 4 {
		usage(os.Args[0])
	}
	// parse number of workers
	n, err := strconv.ParseInt(os.Args[2], 10, 32)
	if err != nil {
		fmt.Fprintln(os.Stderr, "Unable to parse number of worker; found:", os.Args[1])
		os.Exit(2)
	}
	nworker := int(n)
	// parse client
	which := parseClient(os.Args[1])
	if which < 0 {
		usage(os.Args[0])
	}

	for i := 0; i < nworker; i++ {
		go worker(i, which, os.Args[3])
	}
	ninit := 0
	timeoutChan := time.After(1 * time.Minute)
	for {
		select {
		case <-initChan:
			ninit += 1
			if ninit == nworker {
				goto startBarrier
			}
		case <-timeoutChan:
			fmt.Fprintln(os.Stderr, "Unable to start workers in 1 minute")
			os.Exit(1)
		}
	}
startBarrier:
	firstTimeStamp = time.Now()
	close(startChan)

	ndone := 0
	timeoutChan = time.After(30 * time.Minute)
	for {
		select {
		case <-doneChan:
			ndone += 1
			if ndone == nworker {
				goto mainDone
			}
		case <-timeoutChan:
			fmt.Fprintln(os.Stderr, "Unable to finish in 30 minutes")
			os.Exit(1)
		}
	}

mainDone:
	fmt.Println("Done!")
}
