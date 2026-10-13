#!/usr/bin/env python3
"""Size of the Lean development by mathematical section, for docs/PROGRESS.md.

Prints a Markdown table: for each section, the Lean files, lines and declarations
(theorem/lemma/def/structure) under the directories assigned to it. Line counts are a measure of
what exists, not of what is proved correct or of what remains; see docs/PROGRESS.md.

Usage: python3 scripts/progress_table.py [--date]
       python3 scripts/progress_table.py --update docs/PROGRESS.md
           (replaces the text between the markers BEGIN/END GENERATED SIZE TABLE in that file)
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Section -> top-level directories under Balaban/ (a directory belongs to exactly one section).
SECTIONS = [
    ("Frozen model and root statements", ["Frozen", "Model", "Provider"]),
    ("Lattice, analysis, Gaussian and polymer tools", ["Lattice", "Analysis", "Gaussian", "Polymer",
                                                        "Symmetry", "External", "Basic.lean"]),
    ("Green's functions and random walks", ["Green"]),
    ("Background fields and generating sets (P2)", ["Background", "Multiscale"]),
    ("Localization expansions (P3, P6)", ["Localization"]),
    ("Small-field class (P1, P4, P5)", ["SmallField"]),
    ("Fluctuation step and renormalization (P4-P6)", ["Fluctuation", "Flow"]),
    ("Instantiated step at fixed parameters", ["Inhabited"]),
    ("Large-field regions (P5-P7, E9-E10)", ["LargeField"]),
    ("Observables and correlations (P8, P9)", ["Observables", "Correlations"]),
]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |public )*"
                  r"(theorem|lemma|def|abbrev|structure|instance|class)\s", re.M)


def tracked_lean_files():
    out = subprocess.run(["git", "-C", str(ROOT), "ls-files", "Balaban"], capture_output=True,
                         text=True, check=True).stdout.split()
    return [ROOT / f for f in out if f.endswith(".lean")]


def section_of(path):
    rel = path.relative_to(ROOT / "Balaban")
    top = rel.parts[0]
    for name, dirs in SECTIONS:
        if top in dirs:
            return name
    return "Other"


def table(with_date):
    import io
    buf = io.StringIO()
    old = sys.stdout
    sys.stdout = buf
    try:
        render(with_date)
    finally:
        sys.stdout = old
    return buf.getvalue()


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--update":
        path = Path(sys.argv[2])
        txt = path.read_text(encoding="utf-8")
        begin, end = "<!-- BEGIN GENERATED SIZE TABLE -->", "<!-- END GENERATED SIZE TABLE -->"
        i, j = txt.index(begin) + len(begin), txt.index(end)
        path.write_text(txt[:i] + "\n" + table(True) + txt[j:], encoding="utf-8")
        return
    render(sys.argv[1:] == ["--date"])


def render(with_date):
    rows = {name: [0, 0, 0] for name, _ in SECTIONS}
    rows["Other"] = [0, 0, 0]
    for f in tracked_lean_files():
        txt = f.read_text(encoding="utf-8")
        r = rows[section_of(f)]
        r[0] += 1
        r[1] += txt.count("\n")
        r[2] += len(DECL.findall(txt))
    if with_date:
        head = subprocess.run(["git", "-C", str(ROOT), "log", "-1", "--format=%h %cd",
                               "--date=short"], capture_output=True, text=True).stdout.strip()
        print(f"Computed at commit {head}.\n")
    print("| Section | Lean files | Lines | Declarations |")
    print("|---|---:|---:|---:|")
    tot = [0, 0, 0]
    for name in [n for n, _ in SECTIONS] + ["Other"]:
        a, b, c = rows[name]
        if a == 0:
            continue
        tot = [tot[0] + a, tot[1] + b, tot[2] + c]
        print(f"| {name} | {a} | {b:,} | {c:,} |")
    print(f"| **Total** | **{tot[0]}** | **{tot[1]:,}** | **{tot[2]:,}** |")


if __name__ == "__main__":
    main()
