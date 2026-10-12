# Brief W55 — large fields: Lemma C (b), (d), (e4), the clock b(Z), localized histories

**Goal.** Finish block C of `notes/phase1/LF-RECONSTRUCTION.md` (Part I v1.2, §I.4): on the landed
`RegionHistory` (`Balaban/LargeField/History/*`, W48 + W53), formalize
1. Lemma I.4.13 (Lemma C) parts (b), (d), (e4) — the box-cover / core statements that Part III consumes
   at ripeness ((RQ1)–(RQ5), Lemma III.1.2: the core used by R is a union of separated boxes, no lineage
   merge in the blocked strip, last-box-entry exception) — and the floor invariant (Def I.4.11, Lemma
   I.4.12) if needed;
2. the clock `b(Z)` rules (Def I.4.6/I.4.7: gain clock beyond `gain_le`, `gain_of_new`);
3. the multi-scale `regions_grow` (Lemma I.4.3 across several scales, with the torus casts
   `Torus (n (j+1+s))` ≅ `Torus (n (j+(s+1)))`);
4. that `localHistory` is again a region history (Lemma I.3.9 at every step).
State exactly what Part III's Lemma III.1.2 needs and prove that form.

**Ownership.** New files under `Balaban/LargeField/History/` in your worktree
`/home/scott/Balaban-worktrees/W55` (branch `w55-lemma-c`), plus import lines in `Balaban.lean`; new
lemmas only (do not change the statements of `LF2Hyp`, `LF2`, `RegionHistory`, `toLF2Hyp`). Workers W50
(`LargeField/Analytic/Constants.lean`, `LargeField/LF1.lean`), W51 (`LargeField/Background/*`), W52
(`Localization/DecoupledBackground*`) are active: do not touch their files. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–4, or about 3,000 lines, or a precise obstruction (a Part I statement
false as printed — quote it with a counterexample).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; last commit hash.
