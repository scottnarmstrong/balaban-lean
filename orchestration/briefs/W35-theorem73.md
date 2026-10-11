# Brief W35 — background fields VII: Theorem 7.3 (I-2 for the actual background fields)

**Goal.** Assemble I-2 / Theorem 7.3 of `notes/phase1/BACKGROUND.md` v2 §7 for the defined
background fields, from the landed pieces: `Balaban/Background/Def5.lean` (`bgField`, `bgFieldC`,
`bgMult`, `bgMultC`, `theorem71`, `theorem72`, `theorem72_real`, `theorem72_analytic`),
`Theorem52*.lean` (bounds `BgBounds`), `Composition.lean`/`CompositionSystem.lean` (`composeField`,
`composeData`, `isEL_compose`, `isSmallSolution_compose`, `compose_eq_of_unique`,
`composedSystem_unique_lt`, `prop64`), `CompositionDomain.lean` (`lemma62`, `lemma63_inDomainC`,
`compWeight_kappa_mem`, `composeData_isReal`), `ScaledComposition.lean` (`scaledComposition`).

Statement (Theorem 7.3, weights (6.1) via `compWeight`): if `𝔹_j ≺ 𝔹′_k` (`Precedes`), the data of
`𝔹′_k` lie in `𝒟_ℝ(𝔹′_k)` with `C₄K₁δ ≤ c₁` (and the smallness hypotheses of `lemma62` supplied by the
Theorem 5.2 constants — prove that they are), then `composeData … (bgField 𝔹′_k …)` lies in
`𝒟_ℝ(𝔹_j)` and `bgField 𝔹_j (composeData …) = restrict (bgField 𝔹′_k …)` (and the multipliers), i.e.
P2 (4.39); the same for complex data with `bgFieldC` (via `lemma63_inDomainC`); and `(Ψ, φ′, α′)` is
the unique solution of `𝒮` with `|α|′₂ < c₀`. Plus Prop 6.4's perturbed version for the increments of
`theorem52_perturb`. Supply every hypothesis of the landed lemmas from the Theorem 5.2 bounds
(`FieldBounds` from `BgBounds`, the (R3)-type bound from `bg_mass_bound`); if a constant does not
close (e.g. `(4d+6)K₁δ ≤ 1` vs `δ ≤ c₁`), adjust the domain constant `c₁` for this theorem and say so.

**Ownership.** New file(s) under `Balaban/Background/` (e.g. `Theorem73.lean`) in your worktree
`/home/scott/Balaban-worktrees/W35` (branch `w35-theorem73`), plus import lines in `Balaban.lean`.
Worker W33 is writing `Balaban/Background/Holder.lean` / `Def5Response.lean`: do not touch. Never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** The statement above (real and complex, uniqueness of 𝒮, perturbed version), or
about 1,500 lines, or a precise obstruction (a constant that does not close — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; constants; checks and results; axioms;
open questions; last commit hash.
