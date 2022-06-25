package configs

import (
	"time"

	"github.com/spf13/viper"
)

type Root struct {
	NumRounds int

	BroadcastInterval time.Duration
	SendTimeout       time.Duration
	DialTimeout       time.Duration

	Peers map[int]string
}

func ReadConfig(path string) (Root, error) {
	viper.SetConfigFile(path)
	if err := viper.ReadInConfig(); err != nil {
		return Root{}, err
	}
	var c Root
	err := viper.Unmarshal(&c)
	return c, err
}
