#!/usr/bin/env python3
#
from sys import exit, stdin
import re

lines = stdin.readlines()

for i in [ix for ix in range(len(lines)) if ix % 2 == 0]:
    lock = lines[i]
    unlock = lines[i + 1]
    if "Commit(TRUE)" not in lock:
        print(f"Line {i * 2} did not contain Commit(TRUE)")
        print(lock)
        exit(1)
    if "Commit(FALSE)" not in unlock:
        print(f"Line {i * 2 + 1} did not contain Commit(FALSE)")
        exit(1)
    lock_node = re.search(r'.*node(\d+)"', lock).group(1)
    unlock_node = re.search(r'.*node(\d+)"', lock).group(1)
    if lock_node != unlock_node:
        print(f"Mismatch: {lock_node} != {unlock_node}")
        exit(1)
    print(f"Node {lock_node} acquired and released lock.")

print("OK")
