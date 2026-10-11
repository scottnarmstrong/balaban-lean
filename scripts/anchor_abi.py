#!/usr/bin/env python3
"""Compute or check elaborated ABI hashes of frozen anchors.

The ABI of an anchor is the `pp.all` rendering of its elaborated type, plus
its value for a definition anchor. Rendering happens in a temporary Lean file
outside the repository that imports only the anchor's own module, so the
hash detects any change in meaning caused by imports, instances or notation.

Usage:
  scripts/anchor_abi.py --manifest frozen/manifest.json            # check
  scripts/anchor_abi.py --manifest frozen/manifest.json --print    # show hashes

There is deliberately no option that writes the manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def render(module: str, export: str, kind: str) -> str:
    lines = [f"import {module}", "set_option pp.all true", "set_option pp.maxSteps 100000000", "open Lean Elab Command in",
             f"#eval show CommandElabM Unit from do",
             f"  let info ← getConstInfo `{export}",
             "  logInfo m!\"type: {info.type}\""]
    if kind == "definition":
        # Project amendment (BKT surface v1): a `structure` definition anchor has no value;
        # its ABI is its type plus the type of each constructor (which lists every field).
        lines += ["  match info with",
                  "  | .inductInfo v =>",
                  "    for c in v.ctors do",
                  "      let ci ← getConstInfo c",
                  "      logInfo m!\"constructor {c}: {ci.type}\"",
                  "  | _ =>",
                  "    match info.value? with",
                  "    | some v => logInfo m!\"value: {v}\"",
                  "    | none => throwError \"definition anchor has no value\""]
    with tempfile.TemporaryDirectory(prefix="anchor-abi-") as tmp:
        probe = Path(tmp) / "AbiProbe.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                capture_output=True, text=True, timeout=600)
    output = result.stdout + result.stderr
    if result.returncode != 0 or "error" in output.split(":", 1)[0]:
        raise RuntimeError(f"{export}: elaboration failed\n{output}")
    # Strip the temporary file path from each diagnostic so the rendering is stable.
    cleaned = [line.split(": ", 1)[1] if line.startswith(str(probe)) else line
               for line in output.splitlines()]
    return "\n".join(cleaned) + "\n"


def module_of(path: str) -> str:
    return path[:-len(".lean")].replace("/", ".")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--print", action="store_true", help="print hashes instead of checking")
    args = parser.parse_args()
    anchors = json.loads(args.manifest.read_text(encoding="utf-8"))["anchors"]
    failures = 0
    for anchor in anchors:
        text = render(module_of(anchor["path"]), anchor["export"], anchor["kind"])
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
