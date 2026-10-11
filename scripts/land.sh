#!/usr/bin/env bash
# Land a worker branch on main, failing closed.
#
# Usage: scripts/land.sh <branch> "<merge message>"
#
# Run in the main checkout. Merges <branch> with --no-ff, resolves a conflict in Balaban.lean
# by the union of import lines (any other conflict aborts), seeds build artifacts from the
# branch's worktree if one exists, then runs: a lexical duplicate-name warning, `lake build`
# (which fails on any real name clash, since Balaban.lean imports every module),
# the module check, and the frozen-anchor guard. Only if every step passes is the merge kept
# and pushed; otherwise the merge is undone (`git reset --keep`, which preserves uncommitted edits
# of document agents under notes/ and review/) and nothing is pushed.
set -euo pipefail
branch=$1; msg=$2
root=$(git rev-parse --show-toplevel); cd "$root"
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || { echo "not on main"; exit 1; }
dirty=$(git status --porcelain --untracked-files=no | grep -v -E "^ ?M (notes|review)/" || true)
[ -z "$dirty" ] || { echo "main has uncommitted changes outside notes/ and review/:"; echo "$dirty"; exit 1; }
start=$(git rev-parse HEAD)
undo() { echo "LANDING FAILED: $1 — undoing merge"; git merge --abort 2>/dev/null || true; git reset -q --keep "$start"; exit 1; }

if ! git merge -q --no-ff "$branch" -m "$msg"; then
  conflicts=$(git diff --name-only --diff-filter=U)
  [ "$conflicts" = "Balaban.lean" ] || undo "conflicts outside Balaban.lean: $conflicts"
  python3 - <<'EOF'
s = open('Balaban.lean').read()
lines = [l for l in s.split('\n') if not l.startswith(('<<<<<<<', '=======', '>>>>>>>'))]
imports = []
for l in lines:
    if l.startswith('public import') and l not in imports:
        imports.append(l)
open('Balaban.lean', 'w').write("module\n\n" + "\n".join(imports) + "\n")
EOF
  git add Balaban.lean && git commit -q --no-edit || undo "could not commit merge"
fi

wt=$(git worktree list --porcelain | awk -v b="refs/heads/$branch" '/^worktree /{w=$2} $0=="branch "b{print w}')
if [ -n "$wt" ] && [ -d "$wt/.lake/build" ]; then
  cp -a "$wt/.lake/build/lib/lean/Balaban/." .lake/build/lib/lean/Balaban/ 2>/dev/null || true
  cp -a "$wt/.lake/build/ir/Balaban/." .lake/build/ir/Balaban/ 2>/dev/null || true
fi

python3 - <<'EOF' || true
import re, pathlib, collections, sys
decl = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |public )*"
                  r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+([A-Za-z_][\w.'₀-₉]*)", re.M)
names = collections.defaultdict(set)
for f in pathlib.Path('Balaban').rglob('*.lean'):
    if 'External' in f.parts:
        continue
    for m in decl.finditer(f.read_text()):
        names[m.group(1)].add(str(f))
dups = {n: fs for n, fs in names.items() if len(fs) > 1}
for n, fs in dups.items():
    print("WARNING possible duplicate (lexical; the build decides):", n, sorted(fs))
sys.exit(0)
EOF

out=$(lake build 2>&1) || { echo "$out" | grep -E "error" | head -20; undo "lake build failed"; }
echo "$out" | grep -E "^warning" | grep -v "declaration uses .sorry" | grep -v "Frozen/Roots" && undo "new warnings" || true
python3 -I scripts/check_lean_modules.py --root . || undo "module check failed"
python3 -I scripts/check_frozen_anchors.py --root . --manifest frozen/manifest.json \
  --statement-closure-timeout 14400 || undo "frozen-anchor guard failed"
git push -q origin main
echo "LANDED $branch at $(git rev-parse --short HEAD)"
