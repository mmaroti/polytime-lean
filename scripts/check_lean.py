#!/usr/bin/env python3
"""Check project Lean source conventions, optionally followed by lake build."""

import argparse
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
COPYRIGHT = re.compile(
    r"Copyright \(c\) \d{4}(?:-\d{4})? Miklos Maroti <mmaroti@math\.u-szeged\.hu>"
)
OPEN_SCOPE = re.compile(r"^\s*(namespace|(?:noncomputable\s+)?section)\s+(\S+)\s*$")
CLOSE_SCOPE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
UNNAMED_SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section\s*$")
PROOF_GAP = re.compile(r"\b(?:sorry|admit|axiom)\b")


def code_only(source: str) -> str:
    """Mask comments and strings while preserving positions and line numbers."""
    masked = list(source)
    index = 0
    while index < len(source):
        start = index
        if source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end == -1 else end
        elif source.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
        elif source[index] == '"':
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index = min(index + 2, len(source))
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        else:
            index += 1
            continue
        for position in range(start, index):
            if source[position] != "\n":
                masked[position] = " "
    return "".join(masked)


def check_source(source: str) -> list[tuple[int, str]]:
    problems = []
    header = source.split("-/", 1)[0] if source.startswith("/-") else ""
    if not COPYRIGHT.search(header):
        problems.append((1, "missing project copyright header"))
    if "SPDX-License-Identifier: Apache-2.0" not in header:
        problems.append((1, "missing Apache-2.0 license header"))

    scopes = []
    for line_number, line in enumerate(code_only(source).splitlines(), 1):
        for gap in PROOF_GAP.finditer(line):
            problems.append((line_number, f"unverified declaration: {gap.group()}"))
        opening = OPEN_SCOPE.fullmatch(line)
        closing = CLOSE_SCOPE.fullmatch(line)
        if opening:
            scopes.append((opening.group(2), line_number))
        elif UNNAMED_SECTION.fullmatch(line):
            problems.append((line_number, "name this section"))
        elif closing:
            name = closing.group(1)
            if not name:
                problems.append((line_number, "name this end command"))
            if scopes:
                expected, _ = scopes.pop()
                if name and name != expected:
                    problems.append((line_number, f"expected end {expected}, found end {name}"))
            elif name:
                problems.append((line_number, f"end {name} has no matching opening"))
    for name, line_number in scopes:
        problems.append((line_number, f"missing end {name}"))
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="run lake build after source checks pass")
    parser.add_argument("--target", action="append", default=[], help="build a specific Lake target; repeatable")
    args = parser.parse_args()
    if args.target and not args.build:
        parser.error("--target requires --build")

    try:
        listing = subprocess.run(
            ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
            cwd=ROOT, check=True, capture_output=True, text=True,
        )
        paths = sorted(
            path for path in set(filter(None, listing.stdout.split("\0")))
            if (ROOT / path).is_file()
        )
        if not paths:
            print("No project Lean files found.", file=sys.stderr)
            return 1
        problem_count = 0
        for relative_path in paths:
            for line_number, message in check_source((ROOT / relative_path).read_text(encoding="utf-8")):
                print(f"{relative_path}:{line_number}: {message}", file=sys.stderr)
                problem_count += 1
        if problem_count:
            print(f"Found {problem_count} source issue(s).", file=sys.stderr)
            return 1
        print(f"Source checks passed for {len(paths)} Lean files.", flush=True)
        if args.build:
            return subprocess.run(["lake", "build", *args.target], cwd=ROOT).returncode
        return 0
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"Check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
