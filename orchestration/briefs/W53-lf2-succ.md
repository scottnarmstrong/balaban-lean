# Brief W53 — LF-2 interface fix: successors only for non-removed components; Lemma C remainder

**Goal.**
1. **Interface fix.** In the landed abstract counter (`Balaban/LargeField/Counter/LF2.lean` `LF2Hyp`,
   and the numerical `CounterHist` it maps to, W41), the successor map `succ : Comp k → Comp (k+1)` is
   total. A component removed by `R^{(k)}` need not have a successor (its coarsening need not lie in
   `Z^pre_{k+1}`, which can be empty), so W48 had to add the non-source field
   `RegionHistory.removed_succ : (rem k).Nonempty → Nonempty (Comp (k+1))`
   (`Balaban/LargeField/History/RegionHistory.lean`). Change `succ` (and every use: `parts`,
   `mem_parts`, the budget sums, the counting proofs) to act on `{c // c ∉ rem k}`, re-prove `LF2`,
   `counter_main` and the instantiation `RegionHistory.toLF2Hyp` / `flow_counter`, and delete
   `removed_succ`. The statement of `LF2` must otherwise stay the same (say exactly what changed).
2. **Lemma C remainder** (`notes/phase1/LF-RECONSTRUCTION.md` Lemma I.4.13 (b), (d), (e4) and the clock
   `b(Z)` rules), on the landed `RegionHistory`, if budget remains.

**Ownership.** Edits to `Balaban/LargeField/Counter/*` and `Balaban/LargeField/History/*` (W41/W48 files)
in your worktree `/home/scott/Balaban-worktrees/W53` (branch `w53-lf2-succ`). Workers W50
(`LargeField/Analytic/Constants.lean`, `LargeField/LF1.lean`) and W51 (`LargeField/Background/*`) are
active: do not touch their files. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Item 1 (item 2 if budget remains), or about 2,000 lines changed, or a precise
obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; the changed statements (full text of `LF2Hyp` and `LF2` after the change); checks
and results; axioms; last commit hash.
