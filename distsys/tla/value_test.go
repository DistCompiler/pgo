package tla

import (
	"testing"
)

func TestTLAModel(t *testing.T) {
	type Record struct {
		Name           string
		Operation      func() Value
		ExpectedResult string
	}

	tests := []Record{
		{
			Name: "Seq({})",
			Operation: func() Value {
				return ModuleSeq(MakeSet())
			},
			ExpectedResult: "{<<>>}",
		},
		{
			Name: "\\E foo \\in {} : TRUE",
			Operation: func() Value {
				return QuantifiedExistential([]Value{MakeSet()}, func([]Value) bool {
					return true
				})
			},
			ExpectedResult: "FALSE",
		},
		{
			Name: "[x \\in {} |-> x]",
			Operation: func() Value {
				return MakeRecord(nil)
			},
			ExpectedResult: "[x \\in {} |-> x]",
		},
		{
			Name: "1 .. 3",
			Operation: func() Value {
				return ModuleDotDotSymbol(MakeNumber(1), MakeNumber(4))
			},
			ExpectedResult: "{1, 2, 3, 4}",
		},
		{
			Name: "function over empty set short-circuit",
			Operation: func() Value {
				return MakeFunction([]Value{MakeSet(MakeNumber(12)), MakeSet()}, func([]Value) Value {
					panic("should not be called")
				})
			},
			ExpectedResult: "[x \\in {} |-> x]",
		},
	}

	for _, test := range tests {
		t.Run(test.Name, func(t *testing.T) {
			actualValue := test.Operation()
			actualStr := actualValue.String()
			if actualStr != test.ExpectedResult {
				t.Errorf("result %s did not equal expected value %s", actualStr, test.ExpectedResult)
			}
		})
	}
}
