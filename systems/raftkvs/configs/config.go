package configs

import (
	"time"

	"github.com/spf13/viper"
)

type Root struct {
	NumServers int
	NumClients int

	Debug bool

	ClientRequestTimeout time.Duration

	FD             FD
	Mailboxes      Mailboxes
	LeaderElection LeaderElection

	AppendEntriesSendInterval time.Duration
	SharedResourceTimeout     time.Duration
	InputChanReadTimeout      time.Duration

	Servers map[int]Server
	Clients map[int]Client
}

type FD struct {
	PullInterval time.Duration
	Timeout      time.Duration
}

type Mailboxes struct {
	ReceiveChanSize int
	DialTimeout     time.Duration
	ReadTimeout     time.Duration
	WriteTimeout    time.Duration
}

type LeaderElection struct {
	Timeout       time.Duration
	TimeoutOffset time.Duration
}

type Server struct {
	MailboxAddr string
	MonitorAddr string
}

type Client struct {
	MailboxAddr string
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
