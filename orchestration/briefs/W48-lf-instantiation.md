# Brief W48 — large fields, Lean blocks C (geometric) and E: spines, Lemma C, instantiation of LF-2

**Goal.** Connect the landed abstract counter to the landed region calculus, so that `LF2Hyp`'s
proof-step fields are proved for the flow's region history:
1. **Block C geometric parts** (`notes/phase1/LF-RECONSTRUCTION.md` Part I v1.1 §I.4, Lean list C1–C9):
   `RegionHistory` over the landed `RegionStep` (C1: successors, ancestors, lineage,
   `lineage_eq_inter`, `regions_grow` incl. removals), C2 localized histories, C3/C5 the spine
   construction (`stepSpine` by rounds through the hull closure) and **C6 Lemma I.4.8 (spine
   consistency: (3.1) `Z ⊆ N_{ρ_k+4}(spine)` and the event length bound (4.1); point spines are boxes)**,
   C9 the box-cover parts of Lemma C ((a-cover), (b), (d), (e4)) and the clock `b(Z)`.
2. **Block E** (§I.5.7, Lean list E1–E2): `kfhat`, `hLambda_of_flow`, `hT_of_flow` (Lemma I.5.6 from the
   landed `Balaban/Flow/RunningCoefficients.lean`), and the instantiation: for the flow's region history,
   construct `LF2Hyp` (the landed structure in `Balaban/LargeField/Counter/LF2.lean`, W41) with every
   geometric field proved — `spine_contains`, the spine-length part of `book_rule` (from Lemma I.4.8),
   `seed_pos`, the state rules — leaving only `budget` ((B), Lemma B, Part II) and `rg_ripe`/`rg_nonripe`/
   `rg_frozen` ((Rg), LF-4R, Part III) as hypotheses of the instantiation theorem.

Landed inputs: `Balaban/LargeField/Geometry/*` (block A), `Balaban/LargeField/Region/*` (block B: `RegionStep`,
`hullClosure`, `RegionStep.attribution`, locality, `flowGeneratingSet`, overwrite, lineage),
`Balaban/LargeField/Counter/*` and `History/*` (W41: `LF2Hyp`, `WState`, `Book`, T1–T7 relations,
`lemmaV`, `k1`). If a statement of Part I turns out false, stop that item and report it.

**Ownership.** New files under `Balaban/LargeField/History/` (not W41's existing files, which you may
extend only by new lemmas in new files) and `Balaban/LargeField/Counter/Instantiation*.lean` in your
worktree `/home/scott/Balaban-worktrees/W48` (branch `w48-lf-instantiation`), plus import lines in
`Balaban.lean`. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** Items 1–2, or about 4,000 lines, or a precise obstruction. If you stop early,
Lemma I.4.8 and the instantiation of `spine_contains` are the priority.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements (full statement of the instantiation theorem
and its remaining hypotheses); checks and results; axioms; last commit hash.
