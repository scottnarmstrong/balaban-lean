# Brief W41 — large fields, Lean block D: the abstract step counter LF-2 (Part I §I.5)

**Goal.** Formalize block **D** of `notes/phase1/LF-RECONSTRUCTION.md` §I.6 (Part I v1.1, §I.5 and the
parts of §I.4 it needs), namespace `Balaban.LargeField`, files under `Balaban/LargeField/Counter/`:
D1 Lemma V, D2 the constants of §I.1.2 and §I.5.2 as functions of the typing data and λ, D3 growth
(F1)–(F5) and `restart_tStar`, D4 `LamStarConditions` ((Λ0)–(Λ11)) and `exists_lamStar`, D5 `LF2Hyp`
(the abstract history with (G1) seed/attribution maps as data, (G2), (B), (Rg), (K), (H-λ), (H-T),
component data indexed by the `Finset` of components), D6 the budget cases (Lemma I.5.5, §I.5.4:
`sufficient_B7`, pure shadow, cases 1, 2a, 2b, 2c), D7 R-step and base budget, D8 transfer and
frozen step, D9 **`LF2`** (Theorem I.5.4; an internal lemma — never frozen). The abstract counter
must not import the region calculus (block B, being written in parallel by W40); the window-state
bookkeeping it needs (block C: spines, `WState`, `Book`, `tStar`, banks, (T1)–(T7), `k1`, Lemma C4,
Lemma C) — formalize the parts of block C that D uses in abstract form (on an abstract history), in
`Balaban/LargeField/History/` files of your own. Build on block A (`Balaban/LargeField/Geometry/*`).
An independent audit of Part I v1.1 / Part II is running; if a statement of Part I is false as
printed, stop that item and report it with a counterexample. The counting was audited three times;
follow the proof of §I.5 exactly.

**Ownership.** New files under `Balaban/LargeField/Counter/` and `Balaban/LargeField/History/` in your
worktree `/home/scott/Balaban-worktrees/W41` (branch `w41-lf-counter`), plus import lines in
`Balaban.lean`. Worker W40 is writing `Balaban/LargeField/Region/*`; do not touch it. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** D1–D9 with the needed parts of C, or about 4,000 lines, or a precise obstruction.
If you must stop early, D5 + D6 + D9 (the theorem with its case analysis) are the priority.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions (full text of `LF2Hyp` and the statement of `LF2`); main theorem
names with statements; any Part I statement found false; checks and results; axioms; last commit
hash.
