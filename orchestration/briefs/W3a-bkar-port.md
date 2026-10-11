# Brief W3a — port of BKARForestFormula to v4.35.0-rc2 and the module system

**Goal.** Make the BKAR forest interpolation formula available inside this project. Source:
`scottnarmstrong/BKARForestFormula` (public, Lean v4.33.0, Mathlib v4.33.0, **not** modules),
clone at `/home/scott/mining/BKARForestFormula` (55 files, about 18,000 lines; flagship theorem
`BKAR.bkar_formula_forestIndex_cube_contributions`, `BKAR/Formula.lean`). The author pointed to this
repository for reuse; the port is needed by the polymer-expansion theorem PE (roadmap §5,
`notes/phase1/PLAN.md` W3a).

**Ownership.** New directory `Balaban/External/BKAR/` in your worktree
`/home/scott/Balaban-worktrees/W3a` (branch `w3a-bkar-port`), plus one import line
`public import Balaban.External.BKAR` in `Balaban.lean` (create `Balaban/External/BKAR.lean` as the
facade). No other edits.

**Procedure.**
1. Copy `BKAR/**/*.lean` and `BKAR.lean` to `Balaban/External/BKAR/**` and
   `Balaban/External/BKAR.lean`. Rename modules `BKAR.X` → `Balaban.External.BKAR.X` in imports;
   keep the Lean namespace `BKAR` (so declaration names are unchanged).
2. Convert each file to a module: `module` as the first token, `public import` for imports needed
   by the interface, `public section` (or `@[expose] public section` where definitions must unfold
   in downstream proofs), following `/home/scott/.local/share/ai-accounts/claude-2/skills/lean-project-architecture/references/module-system.md`.
3. Add to each file's header comment: ported from `scottnarmstrong/BKARForestFormula` at commit
   `a07f44a`, original license
   (see that repository's LICENSE), and the date.
4. Build bottom-up and repair breakages from Mathlib v4.33.0 → v4.35.0-rc2 (renamed lemmas,
   changed simp sets). Keep statements identical; proofs may change. Never weaken a statement.
5. Port the comparator audit only if cheap; it is not required.

**Checks.** `lake build Balaban.External.BKAR` in your worktree (at most one build at a time; compiles
are throttled machine-wide and may wait for a slot; prefer building one module at a time while
repairing); zero warnings (the original has one `set_option linter...` silence in
`CubePartition/SimplexSector/Singleton.lean`; keep it only if still needed and say so);
`#print axioms BKAR.bkar_formula_forestIndex_cube_contributions` shows only `propext`,
`Classical.choice`, `Quot.sound`; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** The facade builds with the flagship theorem, or a precise obstruction (a lemma
that no longer exists and has no replacement), reported with file and line.

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, zero warnings; frozen files are read-only and are not imported by this
package; no file over 10,000 lines; do not bypass the compile throttle; commit on your branch
only, never push to `main`.

**Handoff.** Files; the list of repaired proofs (file, lemma, what changed); checks and results;
axioms; commit on branch `w3a-bkar-port`.
