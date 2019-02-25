package pgo.model.type;

import pgo.errors.Issue;

class UnificationException extends Exception {
	private final Issue issue;

	UnificationException(Issue issue) {
		this.issue = issue;
	}

	Issue getIssue() {
		return issue;
	}
}
