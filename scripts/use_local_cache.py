#!/usr/bin/env python3
"""Use the Mathlib packages of an already built checkout with the same pin.

Only the ignored Lake override file `.lake/package-overrides.json` is written;
the committed `lake-manifest.json` stays a portable lockfile. A dependency at a
different revision, with tracked modifications, or without a prebuilt Mathlib
cache is rejected. Collaborators without such a checkout run
`lake exe cache get` instead.

Usage: scripts/use_local_cache.py /home/scott/FroehlichSpencer
"""
import argparse
import json
from pathlib import Path
import subprocess


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    checkout = args.checkout.resolve()
    manifest = json.loads((root / "lake-manifest.json").read_text())
    if (checkout / "lean-toolchain").read_text() != (root / "lean-toolchain").read_text():
        raise SystemExit("Dependency toolchain does not match this toolchain")
    overrides = []
    for entry in manifest["packages"]:
        path = checkout / ".lake/packages" / entry["name"]
        if git(path, "rev-parse", "HEAD") != entry["rev"]:
            raise SystemExit(f"Wrong pinned revision: {entry['name']}")
        if git(path, "status", "--porcelain", "--untracked-files=no"):
            raise SystemExit(f"Tracked dependency modifications: {entry['name']}")
        if entry["name"] == "mathlib" and not (path / ".lake/build/lib/lean").is_dir():
            raise SystemExit("Missing prebuilt Mathlib cache")
        overrides.append({
            "type": "path", "dir": str(path), "name": entry["name"],
            "scope": entry.get("scope", ""), "inherited": entry["inherited"],
            "configFile": entry["configFile"], "manifestFile": entry["manifestFile"]})
    destination = root / ".lake/package-overrides.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps({"schemaVersion": manifest["version"],
                                       "packages": overrides}, indent=2) + "\n")
    print(f"Verified {len(overrides)} exact dependency revisions; wrote {destination}")


if __name__ == "__main__":
    main()
