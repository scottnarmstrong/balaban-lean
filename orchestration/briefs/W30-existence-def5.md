# Brief W30 — background fields V: Theorem 5.2 (I-1) and Def-5

**Goal.** Assemble the existence theorem of the hard-spin background fields and the Def-5
definitions, following `notes/phase1/BACKGROUND.md` v2 §5.2, §5.4 (proof of Theorem 5.2) and §7
(Def-5, Theorems 7.1, 7.2), from the landed pieces:
`Balaban/Background/Approximate.lean` (`lemma53`, `ApproxSetting`, `DataWit`, `approxField`,
`residual`), `ApproxAnalytic.lean` (`approxField_analytic`, `residualRaw_analytic`),
`Contraction.lean` (`Prop51Hyp`, `IsPerturbed`, `prop51_exists_unique`), `ContractionAnalytic.lean`
(`prop51_analytic`), `ContractionCore*.lean`, `Data.lean` (`BgData`, `IsEL`, `IsSmallSolution`,
`IsMinimizer`, domains), `LinearResponse.lean`, `Composition*.lean`.

1. **Theorem 5.2 (1)–(6)**: for data in the domains, `φ = φ₀ + δφ`, `α = 0 + δα` with `(δφ, δα)` the
   Prop 5.1 solution for the residual of Lemma 5.3 — existence of a small solution of (EL), the
   bounds P2 (1.15)–(1.16) (with the constants composed explicitly: `K₁` from `lemma53Const`, `K₂`,
   `c₆`), uniqueness among solutions with `|α|₂ < c₀` (from the uniqueness part of
   `prop51_exists_unique` around `φ₀`; state exactly the local uniqueness class you can prove),
   analyticity on the open union domain (via `prop51_analytic` and `approxField_analytic`), and the
   real-data case.
2. **The minimizer identity (5.3)** `A(σ) − A(φ) = ½⟨σ − φ, H_D(α)(σ − φ)⟩` for `σ` on the sphere and
   the consequence that, for real data, the small solution is the unique global minimizer (needs
   positivity of `H_D(α)` on the relevant space; BACKGROUND v2 §5.4 and the review V-15 note).
3. **Def-5** (§7): `bgField` (dite on `∃! φ, IsMinimizer …`), `bgMult`, `bgFieldC c₀` (dite on
   `∃! s, IsSmallSolution c₀ …`), with **Theorem 7.1** and **Theorem 7.2** (characterization: on the
   domains the `∃!` holds, values satisfy the predicates and bounds, analytic on `𝒟`, agree with
   `bgField` on real data). Rule 4 of AGENTS.md: the definitions land together with their
   characterization theorems, no `Classical.choose` from mere existence.

**Ownership.** New files under `Balaban/Background/` (e.g. `Existence.lean`, `Minimizer.lean`,
`Def5.lean`) in your worktree `/home/scott/Balaban-worktrees/W30` (branch `w30-existence-def5`),
plus import lines in `Balaban.lean`. Worker W28 is writing `Balaban/Background/CompositionDomain.lean`
/ `ScaledComposition.lean`: do not touch those. Small additions to landed `Balaban/Background/*`
files only if unavoidable (say which). Never import `Balaban/Frozen/Roots/*` or
`Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** Items 1–3, or about 3,000 lines, or a precise obstruction (a constant chain or
uniqueness class that does not close — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; full Lean text of `bgField`, `bgFieldC` and Theorems 7.1/7.2; main theorem
names with statements; checks and results; axioms; open questions; last commit hash.
