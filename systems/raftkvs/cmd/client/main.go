package main

import (
	"flag"
	"fmt"
	"log"

	"example.org/raftkvs/bootstrap"
	"example.org/raftkvs/configs"
)

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

	req := bootstrap.PutRequest{
		Key:   "hello",
		Value: "world",
	}
	reqCh <- req

	resp := <-respCh
	fmt.Println(resp)
}
