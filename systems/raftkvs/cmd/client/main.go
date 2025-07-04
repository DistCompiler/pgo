package main

import (
	"bufio"
	"errors"
	"flag"
	"fmt"
	"log"
	"os"
	"strconv"
	"strings"

	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
	"github.com/antithesishq/antithesis-sdk-go/random"
)

var ErrInvalidCmd = errors.New("invalid command")

func parseCmd(cmd string) (bootstrap.Request, error) {
	words := strings.Split(cmd, " ")
	if len(words) < 1 {
		return nil, ErrInvalidCmd
	}

	reqType := words[0]
	switch strings.ToLower(reqType) {
	case "get":
		if len(words) < 2 {
			return nil, ErrInvalidCmd
		}
		return bootstrap.GetRequest{
			Key: words[1],
		}, nil
	case "put":
		if len(words) < 3 {
			return nil, ErrInvalidCmd
		}
		return bootstrap.PutRequest{
			Key:   words[1],
			Value: words[2],
		}, nil
	default:
		return nil, ErrInvalidCmd
	}
}

func printResp(resp bootstrap.Response) {
	if !resp.OK {
		fmt.Println("key not found")
	} else {
		fmt.Printf("%v %v\n", resp.Key, resp.Value)
	}
}

func main() {
	var clientId int
	var configPath string
	var workloadPath string
	var randomOpCount int
	flag.IntVar(&clientId, "clientId", -1, "Client ID")
	flag.StringVar(&configPath, "c", "", "Config file")
	flag.StringVar(&workloadPath, "w", "", "Workload file (stdin if blank)")
	flag.IntVar(&randomOpCount, "randomOpCount", -1, "When enabled, ignore workload input and perform the given number of random operations")

	flag.Parse()

	if clientId == -1 {
		log.Fatal("clientId is not provided or it is invalid")
	}
	if configPath == "" {
		log.Fatal("config file is not provided")
	}

	c, err := configs.ReadConfig(configPath)
	if err != nil {
		log.Fatal(err)
	}

	var workloadFile *os.File
	if workloadPath != "" {
		workloadFile, err = os.Open(workloadPath)
		if err != nil {
			log.Fatal(err)
		}
		defer workloadFile.Close()
	}

	client := bootstrap.NewClient(clientId, c)

	reqCh := make(chan bootstrap.Request)
	respCh := make(chan bootstrap.Response)
	go func() {
		err := client.Run(reqCh, respCh)
		if err != nil {
			log.Fatal(err)
		}
	}()

	defer func() {
		close(reqCh)
		close(respCh)
		err := client.Close()
		if err != nil {
			log.Fatal(err)
		}
	}()

	if randomOpCount == -1 {
		var scanner *bufio.Scanner
		if workloadFile != nil {
			scanner = bufio.NewScanner(workloadFile)
		} else {
			scanner = bufio.NewScanner(os.Stdin)
		}
		for {
			fmt.Print("> ")
			ok := scanner.Scan()
			if !ok {
				break
			}

			req, err := parseCmd(scanner.Text())
			if err != nil {
				fmt.Printf("error: %v\n", err)
				continue
			}
			// fmt.Println(req)

			reqCh <- req

			resp := <-respCh
			printResp(resp)
		}
	} else {
		keyChoices := []string{}
		for i := range 10 {
			keyChoices = append(keyChoices, strconv.Itoa(i+1))
		}
		valueChoices := []string{}
		for i := range 10 {
			valueChoices = append(valueChoices, strconv.Itoa(i+1))
		}

		for range randomOpCount {
			switch random.RandomChoice([]bool{false, true}) {
			case false:
				req := bootstrap.GetRequest{
					Key: random.RandomChoice(keyChoices),
				}
				fmt.Println(req)
				reqCh <- req
				printResp(<-respCh)
			case true:
				req := bootstrap.PutRequest{
					Key:   random.RandomChoice(keyChoices),
					Value: random.RandomChoice(valueChoices),
				}
				fmt.Println(req)
				reqCh <- req
				printResp(<-respCh)
			}
		}
	}
}
