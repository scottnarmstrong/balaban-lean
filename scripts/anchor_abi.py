#!/usr/bin/env python3
"""Compute or check elaborated ABI hashes of frozen anchors.

The ABI of an anchor is the `pp.all` rendering of its elaborated type, plus
its value for a definition anchor (or the types of its constructors for a
`structure`). Rendering happens in one temporary Lean file outside the
repository that imports the anchor modules; `pp.all` disables notation, so
the rendering of a stored declaration does not depend on the other imports.

Project amendment (Balaban, 2026-10-11): all anchors are rendered in a single
Lean process (the machine-wide compile throttle made one probe per anchor
time out), with a long timeout. Diagnostic positions are stripped, so the
rendering is stable under reordering of the anchors.

Usage:
  scripts/anchor_abi.py --manifest frozen/manifest.json            # check
  scripts/anchor_abi.py --manifest frozen/manifest.json --print    # show hashes

There is deliberately no option that writes the manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MARK = "ANCHOR_ABI_SECTION "


def probe_lines(index: int, anchor_id: str, export: str, kind: str) -> list[str]:
    lines = ["open Lean Elab Command in",
             "#eval show CommandElabM Unit from do",
             f"  logInfo m!\"{MARK}{index}\"",
             f"  let info ← getConstInfo `{export}",
             "  logInfo m!\"type: {info.type}\""]
    if kind == "definition":
        # A `structure` definition anchor has no value; its ABI is its type plus the type of
        # each constructor (which lists every field).
        lines += ["  match info with",
                  "  | .inductInfo v =>",
                  "    for c in v.ctors do",
                  "      let ci ← getConstInfo c",
                  "      logInfo m!\"constructor {c}: {ci.type}\"",
                  "  | _ =>",
                  "    match info.value? with",
                  "    | some v => logInfo m!\"value: {v}\"",
                  "    | none => throwError \"definition anchor has no value\""]
    return lines


def render_all(anchors: list[dict]) -> list[str]:
    modules = sorted({module_of(a["path"]) for a in anchors})
    lines = [f"import {m}" for m in modules]
    lines += ["set_option pp.all true", "set_option pp.maxSteps 100000000"]
    for index, anchor in enumerate(anchors):
        lines += probe_lines(index, anchor["id"], anchor["export"], anchor["kind"])
    with tempfile.TemporaryDirectory(prefix="anchor-abi-") as tmp:
        probe = Path(tmp) / "AbiProbe.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                capture_output=True, text=True, timeout=14400)
    output = result.stdout + result.stderr
    if result.returncode != 0 or re.search(r":\d+:\d+: error", output):
        raise RuntimeError(f"elaboration failed\n{output}")
    # Strip the temporary file path and position from each diagnostic.
    prefix = re.compile(r"^.*?AbiProbe\.lean:\d+:\d+: ")
    debug = ROOT / ".lake" / "anchor_abi_last_output.txt"
    debug.parent.mkdir(parents=True, exist_ok=True)
    debug.write_text(output, encoding="utf-8")
    sections: list[list[str]] = [[] for _ in anchors]
    current = None
    for line in output.splitlines():
        stripped = prefix.sub("", line, count=1)
        if stripped.startswith("info: "):
            stripped = stripped[len("info: "):]
        if stripped.startswith(MARK):
            current = int(stripped[len(MARK):].strip())
            continue
        if current is None:
            continue
        sections[current].append(stripped)
    return ["\n".join(section) + "\n" for section in sections]


def module_of(path: str) -> str:
    return path[:-len(".lean")].replace("/", ".")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--print", action="store_true", help="print hashes instead of checking")
    args = parser.parse_args()
    anchors = json.loads(args.manifest.read_text(encoding="utf-8"))["anchors"]
    failures = 0
    for anchor, text in zip(anchors, render_all(anchors)):
        if not text.strip():
            failures += 1
            print(f"ABI EMPTY {anchor['id']}")
            continue
        digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
        if args.print:
            print(f"{anchor['id']} {digest}")
        elif digest != anchor["abi_sha256"]:
            failures += 1
            print(f"ABI DRIFT {anchor['id']}: manifest {anchor['abi_sha256']} != elaborated {digest}")
    if failures:
        print(f"ANCHOR ABI CHECK FAILED ({failures})", file=sys.stderr)
        return 1
    if not args.print:
        print(f"ANCHOR ABI CHECK OK ({len(anchors)} anchors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
