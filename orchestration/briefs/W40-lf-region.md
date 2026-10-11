# Brief W40 — large fields, Lean block B: the region calculus (Part I §I.3)

**Goal.** Formalize block **B** of `notes/phase1/LF-RECONSTRUCTION.md` §I.6 (Part I v1.1, §I.3:
Defs I.3.1–I.3.3, I.3.6, I.3.11 and Lemmas I.3.4, I.3.5, I.3.7–I.3.10, I.3.12, I.3.15, I.3.16), namespace
`Balaban.LargeField`, files under `Balaban/LargeField/Region/`: B1 `RegionStep` and the set functions
(`U`, `Uprime`, `OmegaPrime`, `Omega`, `OmegaDD`, `FZ`, `Z0`, `newCubes`), B2 hull rounds and hull closure
(Lemma I.3.4; v1.1 labels the iterated closure as an extension of P6 p. 22), B3 inclusions (a)–(i),
B4 seeds, B5 attribution (G1) with the v1.1 radius hypotheses (RH), B6 locality, B7
`flowGeneratingSet` into the landed `Balaban.Multiscale.GeneratingSet` (with `R_j ≥ R_base` and the
terminal `Ω_{k+2} = ∅`), removal overwrite, B8. Build on the landed block A
(`Balaban/LargeField/Geometry/*`, W37: `supDist`, `nbhd`, `thick`, `coarsen`, `opening`, `hull`,
`comps`, `nbhd_disjoint_of_comps`, `local_eq_global`) and the W31 Lemma S. An independent audit of
Part I v1.1 / Part II is running; if a Part I statement is false as printed, stop that item and
report it with a counterexample.

**Ownership.** New files under `Balaban/LargeField/Region/` in your worktree
`/home/scott/Balaban-worktrees/W40` (branch `w40-lf-region`), plus import lines in `Balaban.lean`.
Worker W41 is writing `Balaban/LargeField/Counter/*` in parallel; do not touch it. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** B1–B8, or about 2,800 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; any Part I statement found
false; checks and results; axioms; last commit hash.
