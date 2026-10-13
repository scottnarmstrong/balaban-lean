#!/usr/bin/env bash
# Mirror the pushed `main` of the development repository to the public repository
# scottnarmstrong/balaban-lean, with the directory `sources/` (publisher PDFs of the papers)
# removed from the whole history.
#
# The rewrite (git-filter-repo) is deterministic: the same input history always gives the same
# rewritten commits, so each run reproduces the published history and adds the new commits on top,
# and the push is an ordinary fast-forward. The script never force-pushes; if the public branch has
# diverged it stops with an error.
#
# Only commits already pushed to the development repository's GitHub remote are mirrored
# (refs/remotes/origin/main of the local checkout), so an unverified local merge is never published.
#
# Usage: scripts/publish_public.sh            (run from cron; see the comment at the end)
set -euo pipefail

SRC=/home/scott/Balaban
WORK=/home/scott/Balaban-scratch/public-mirror
FILTER=/home/scott/Balaban-scratch/tools/fr-venv/bin/git-filter-repo
PUBLIC=https://github.com/scottnarmstrong/balaban-lean.git
STAMP=$WORK/last-source-commit

mkdir -p "$WORK"
exec 9>"$WORK/lock"
flock -n 9 || exit 0

git -C "$SRC" fetch -q origin main
src=$(git -C "$SRC" rev-parse refs/remotes/origin/main)
if [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$src" ]; then
  exit 0
fi

rm -rf "$WORK/repo"
git init -q "$WORK/repo"
git -C "$WORK/repo" fetch -q "$SRC" "refs/remotes/origin/main:refs/heads/main"
git -C "$WORK/repo" symbolic-ref HEAD refs/heads/main
(cd "$WORK/repo" && "$FILTER" --path sources/ --invert-paths --force --quiet)
if git -C "$WORK/repo" rev-list --all --objects | grep -q '^[0-9a-f]* sources/'; then
  echo "$(date -u +%FT%TZ) refusing to publish: sources/ still present" >&2
  exit 1
fi
git -C "$WORK/repo" push -q "$PUBLIC" main:main
echo "$src" > "$STAMP"
echo "$(date -u +%FT%TZ) published $(git -C "$WORK/repo" rev-parse --short main) (source ${src:0:7})"

# cron (crontab of the user scott):
# */10 * * * * /home/scott/Balaban/scripts/publish_public.sh >> /home/scott/Balaban-scratch/public-mirror/publish.log 2>&1
