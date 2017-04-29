package main

import "fmt"

func main() {
	for _, i := range Sequence(1, 5) {
		fmt.Println("hi")
		fmt.Println(i)
	}
	fmt.Println("done")
}
