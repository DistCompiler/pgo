package main

import (
	"bufio"
	"errors"
	"flag"
	"fmt"
	"log"
	"os"
	"strings"

	"github.com/DistCompiler/pgo/systems/raftkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/raftkvs/configs"
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
		if len(words) < 2 {
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
	flag.IntVar(&clientId, "clientId", -1, "Client ID")
	flag.StringVar(&configPath, "c", "", "Config file")

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

	client := bootstrap.NewClient(clientId, c)

	reqCh := make(chan bootstrap.Request)
	respCh := make(chan bootstrap.Response)
	go func() {
		err := client.Run(reqCh, respCh)
		if err != nil {
			log.Println(err)
		}
	}()

	defer func() {
		close(reqCh)
		close(respCh)
		err := client.Close()
		if err != nil {
			log.Println(err)
		}
	}()

	scanner := bufio.NewScanner(os.Stdin)
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
}
