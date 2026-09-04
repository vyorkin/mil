#!/usr/bin/env python3
"""
Rewrap a Russian `-- `-comment paragraph for the .lean files in this repo.

Usage:
    python3 scripts/rewrap_comment.py [-w WIDTH] < paragraph.txt

Input: one paragraph's worth of comment text on stdin, either already
split into `-- `-prefixed lines (they'll be joined back into one stream
of words first) or as plain unprefixed text.

Output: the paragraph rewrapped to `-- `-prefixed lines, greedily filling
each line up to WIDTH columns, but preferring to break at a clause
boundary (right after `. , : ; —` or right before a short list of
Russian conjunctions/relative words) instead of wherever a word happens
to first cross the width limit. Text inside a pair of backticks
(`` `code` ``) is treated as a single unbreakable token, so inline code
is never split across lines.

This is a heuristic first pass, not a substitute for reading the
result: always eyeball the output afterwards, since true phrase-aware
wrapping is a judgment call a script can only approximate.
"""

import argparse
import re
import sys

PREFIX = "-- "

# Words it's usually nicer to start a new line with, when a break is
# needed nearby anyway (coordinating/subordinating conjunctions and
# relative words that naturally open a new clause).
SOFT_BEFORE = {
    "и", "а", "но", "или", "либо", "да",
    "что", "чтобы", "если", "когда", "пока", "хотя",
    "который", "которая", "которое", "которые",
    "которого", "которой", "которых", "которому", "которым", "которыми",
    "где", "куда", "откуда", "как", "чем", "будто",
    "поэтому", "потому", "затем", "далее", "значит", "иначе",
}

CLAUSE_END_RE = re.compile(r"[.,:;—]$")


def tokenize(text: str) -> list[str]:
    """Split into words, keeping any `backtick span` as one atomic token."""
    tokens = []
    buf = []
    in_code = False
    for ch in text:
        if ch == "`":
            in_code = not in_code
            buf.append(ch)
            continue
        if ch.isspace() and not in_code:
            if buf:
                tokens.append("".join(buf))
                buf = []
            continue
        buf.append(ch)
    if buf:
        tokens.append("".join(buf))
    return tokens


def wrap(text: str, width: int = 78, slack: int = 20) -> list[str]:
    tokens = tokenize(text)
    lines: list[str] = []
    cur: list[str] = []
    cur_len = len(PREFIX)

    i = 0
    n = len(tokens)
    while i < n:
        tok = tokens[i]
        extra = len(tok) + (1 if cur else 0)
        if cur_len + extra <= width or not cur:
            cur.append(tok)
            cur_len += extra
            i += 1
            continue

        # `tok` doesn't fit. Look for a preferred earlier break point
        # within `slack` columns of the limit: right after a token
        # ending in clause punctuation, or right before a soft
        # conjunction (checking `tok` itself, the one that overflowed).
        break_at = len(cur)  # default: break right here (before tok)
        running = len(PREFIX)
        for j, t in enumerate(cur):
            running += len(t) + (1 if j > 0 else 0)
            if running < width - slack:
                continue
            if CLAUSE_END_RE.search(t):
                break_at = j + 1
        if tok.strip("«»\"'").lower() in SOFT_BEFORE:
            break_at = min(break_at, len(cur))

        lines.append(PREFIX + " ".join(cur[:break_at]))
        cur = cur[break_at:]
        cur_len = len(PREFIX) + (
            sum(len(t) + 1 for t in cur) - 1 if cur else 0
        )
        # retry placing tok against the shorter `cur`
        continue

    if cur:
        lines.append(PREFIX + " ".join(cur))
    return lines


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("-w", "--width", type=int, default=78)
    args = ap.parse_args()

    raw = sys.stdin.read()
    # Strip a leading "-- " (or bare "--") from each input line, if
    # present, then join into one text stream.
    lines_in = raw.splitlines()
    words = []
    for line in lines_in:
        stripped = line.strip()
        if stripped.startswith("--"):
            stripped = stripped[2:].strip()
        words.append(stripped)
    text = " ".join(w for w in words if w)

    for line in wrap(text, width=args.width):
        print(line)


if __name__ == "__main__":
    main()
