package util

import "github.com/UBC-NSS/pgo/distsys"

func MatchAllPathsAbort(effects []distsys.Effect, fn func() bool) bool {
	abortCount := 0
	for _, effect := range effects {
		switch effect.(type) {
		case distsys.AbortEffect:
			abortCount++
		}
	}
	if abortCount != len(effects) {
		return false
	} else {
		return fn()
	}
}

func MatchUnambiguousCommit(effects []distsys.Effect, fn func(idx int) bool) bool {
	abortCount := 0
	commitIdx := -1
	for idx, effect := range effects {
		switch effect.(type) {
		case distsys.AbortEffect:
			abortCount++
		case distsys.CommitEffect:
			if commitIdx == -1 {
				commitIdx = idx
			}
		}
	}
	if commitIdx != -1 && abortCount == len(effects)-1 {
		return fn(commitIdx)
	} else {
		return false
	}
}
