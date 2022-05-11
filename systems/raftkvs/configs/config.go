package configs

import (
	"time"

	"github.com/spf13/viper"
)

type Root struct {
	NumServers int
	NumClients int

	Debug bool

	FD             FD
	Mailboxes      Mailboxes
	LeaderElection LeaderElection

	AppendEntriesSendInterval time.Duration
	SharedResourceTimeout     time.Duration
	InputChanReadTimeout      time.Duration

	Archetypes map[int]Archetype
}

type FD struct {
	PullInterval time.Duration
	Timeout      time.Duration
}

type Mailboxes struct {
	DialTimeout  time.Duration
	ReadTimeout  time.Duration
	WriteTimeout time.Duration
}

type LeaderElection struct {
	Timeout       time.Duration
	TimeoutOffset time.Duration
}

type Archetype struct {
	MailboxAddr string
	MonitorAddr string
}

func ReadConfig(path string) (Root, error) {
	viper.SetConfigFile(path)
	if err := viper.ReadInConfig(); err != nil {
		return Root{}, nil
	}
	var c Root
	err := viper.Unmarshal(&c)
	return c, err
}
