package main

import (
	"fmt"
	"io"
	"os"
)

const (
	BUFFER_SIZE = 4096
)

func readToken(buffer []byte) int {
	for i, v := range buffer {
		if v == ' ' || v == '\n' {
			return i
		}
	}
	return len(buffer)
}

func main() {
	// set up connection to implementation
	client := NewDummyClient()
	// bench
	buffer := make([]byte, BUFFER_SIZE)
	current := 0
	end := 0
	readMore := false
	lastTokenLength := -1
	stdin := os.Stdin
	for {
		switch {
		case end <= current:
			// we're completely out of data in the buffer
			n, err := stdin.Read(buffer)
			if err == io.EOF {
				// we're done!
				goto exit
			}
			if err != nil {
				fmt.Fprintln(os.Stderr, "Error reading from stdin:", err)
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
				fmt.Fprintf(os.Stderr, "Error copying data within buffer: %d bytes copied but %d bytes needed copying\n", n, end-current)
				os.Exit(2)
			}
			n, err := stdin.Read(buffer[end-current:])
			if err != io.EOF && err != nil {
				fmt.Fprintln(os.Stderr, "Error reading from stdin:", err)
				os.Exit(3)
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
					fmt.Fprintln(os.Stderr, "Get command must be followed by new line; found", string(buffer[current:end]))
					os.Exit(4)
				}
				// time to issue the get!
				client.Get(key)
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
					fmt.Fprintln(os.Stderr, "Incomplete command:", string(buffer[current:end]))
					os.Exit(5)
				}
				// condition here: tokenlength < end-token
				key := string(buffer[i : i+tokenLength])
				if buffer[i+tokenLength] != ' ' {
					fmt.Fprintln(os.Stderr, "Ill-formed command:", string(buffer[current:end]))
					os.Exit(6)
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
					fmt.Fprintln(os.Stderr, "Put command must be followed by new line; found", string(buffer[current:end]))
					os.Exit(7)
				}
				// we've (possibly) retried and there's no more data
				value := string(buffer[i : i+tokenLength])
				// time to issue the put!
				client.Put(key, value)
				lastTokenLength = -1
				readMore = false
				current = i + tokenLength + 1
			default:
				fmt.Fprintln(os.Stderr, "Unknown command:", string(buffer[current:current+3]))
				os.Exit(8)
			}
		}
	}
exit:
	fmt.Println("Done!")
}
