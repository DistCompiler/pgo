package tla

import (
	"testing"
)

func TestTLAModel(t *testing.T) {
	type Record struct {
		Name           string
		Operation      func() TLAValue
		ExpectedResult string
	}

	tests := []Record{
		{
			Name: "Seq({})",
			Operation: func() TLAValue {
				return TLA_Seq(MakeTLASet())
			},
			ExpectedResult: "{<<>>}",
		},
		{
			Name: "\\E foo \\in {} : TRUE",
			Operation: func() TLAValue {
				return TLAQuantifiedExistential([]TLAValue{MakeTLASet()}, func([]TLAValue) bool {
					return true
				})
			},
			ExpectedResult: "FALSE",
		},
		{
			Name: "[x \\in {} |-> x]",
			Operation: func() TLAValue {
				return MakeTLARecord(nil)
			},
			ExpectedResult: "[x \\in {} |-> x]",
		},
		{
			Name: "1 .. 3",
			Operation: func() TLAValue {
				return TLA_DotDotSymbol(MakeTLANumber(1), MakeTLANumber(4))
			},
			ExpectedResult: "{1, 2, 3, 4}",
		},
		{
			Name: "function over empty set short-circuit",
			Operation: func() TLAValue {
				return MakeTLAFunction([]TLAValue{MakeTLASet(MakeTLANumber(12)), MakeTLASet()}, func([]TLAValue) TLAValue {
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
