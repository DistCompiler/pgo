package trace

import (
	"encoding/json"
	"fmt"
	"os"
	"sync"
)

type Recorder interface {
	RecordEvent(event Event)
}

type localFileRecorder struct {
	lock    sync.Mutex
	file    *os.File
	encoder *json.Encoder
}

func MakeLocalFileRecorderFromName(filename string) Recorder {
	_, err := os.Stat(filename)
	if err == nil {
		panic(fmt.Sprintf("log file %s already exists", filename))
	}
	file, err := os.Create(filename)
	if err != nil {
		panic(err)
	}
	return &localFileRecorder{
		file:    file,
		encoder: json.NewEncoder(file),
	}
}

func MakeLocalFileRecorder(file *os.File) Recorder {
	return &localFileRecorder{
		file:    file,
		encoder: json.NewEncoder(file),
	}
}

func (recorder *localFileRecorder) RecordEvent(event Event) {
	recorder.lock.Lock()
	defer recorder.lock.Unlock()

	err := recorder.encoder.Encode(event)
	if err != nil {
		panic(err)
	}
}
