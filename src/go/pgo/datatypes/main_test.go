package datatypes

import (
	"os"
	"testing"
)

func TestMain(m *testing.M) {
	GobInit()
	ret := m.Run()
	// teardown code here
	os.Exit(ret)
}
