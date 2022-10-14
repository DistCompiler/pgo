package main

import (
	"flag"
	"log"

	"github.com/DistCompiler/pgo/systems/pbkvs/bootstrap"
	"github.com/DistCompiler/pgo/systems/pbkvs/configs"
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
	go func() {
		err := client.Run()
		if err != nil {
			log.Println(err)
		}
	}()
	defer func() {
		if err := client.Close(); err != nil {
			log.Println(err)
		}
	}()

	{
		resp, err := client.Put("key1", "value1")
		if err != nil {
			log.Printf("put error: %v", err)
		} else {
			log.Printf("put resp: %v", resp)
		}
	}
	{
		resp, err := client.Get("key1")
		if err != nil {
			log.Printf("get error: %v", err)
		} else {
			log.Printf("get resp: %v", resp)
		}
	}
}
