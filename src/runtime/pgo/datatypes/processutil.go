package datatypes

import (
	"strconv"
	"strings"
)

func ParseProcessId(processId string) (string, interface{}) {
	leftParens := strings.Index(processId, "(")
	if leftParens < 0 {
		panic("Missing left parenthesis")
	}
	processName := processId[:leftParens]
	if processName == "" {
		panic("Missing process name")
	}
	rightParens := strings.LastIndex(processId, ")")
	if rightParens < 0 {
		panic("Missing right parenthesis")
	}
	argument := processId[leftParens+1 : rightParens]
	if argument == "" {
		panic("Missing processs argument")
	}
	i, err := strconv.Atoi(argument)
	if err != nil {
		return processName, argument
	}
	return processName, i
}
