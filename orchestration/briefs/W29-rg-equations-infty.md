# Brief W29 — I-7 at λ = ∞: the RG system, Lemma 3.1, Theorem 3.2 (editable lemma)

**Goal.** Formalize `notes/phase1/SMALLFIELD.md` v2 §3 (I-7; review `SMALLFIELD-review.md`) on top
of the landed `Balaban/Flow/*` (`RGEquations.lean`: `exists_rg_solution`, `TriangularBounds`,
`exists_rg_solution_triangular`; `RGParam.lean`: `exists_rg_solution_triangular_param`,
`rg_solution_real`, `fixedPoint_dist_le`; `RunningCoefficients.lean`: `betaSeq`, `gammaSeq`,
`deltaSeq`, `norm_gammaSeq_le`, `exists_gamma_infty`, `exists_inv_betaSeq_asymptotics`):

1. **The matrix at λ = ∞** (§3.4, P4 (5.21)): the explicit entries `a₁₁ … a₃₃` as functions of
   `(a, v, τ, c₁, c₂, ε)`, and **Lemma 3.1** (coefficient bounds for `a ∈ [9/10, 3/2]`,
   `0 < v ≤ 7/32`, `τ ∈ [0,1]`, `0 < cᵢ < 1/20`, `0 < c₁ − v c₂ < c₁`), concluding
   `TriangularBounds (A …) ε`-type hypotheses for `exists_rg_solution_triangular_param` (check the
   exact field list of `TriangularBounds` and prove exactly those).
2. **Theorem 3.2 (a)–(c)** as an *editable abstract lemma* (review S-05: it is not frozen): with
   (B1) as an explicit hypothesis (the analyticity and bounds of the data `f_u, c₂, v_u` on the
   polydisc, stated abstractly as hypotheses on functions `c, f`), and the (5.29) inequality, derive
   (a) existence/uniqueness/analyticity/realness of `ξ⁰` with `|ξ⁰| ≤ C_ξ β⁻¹ L^{−2γ(k+1)}` from
   `exists_rg_solution_triangular_param` and `rg_solution_real`; (b) the inductive bound
   `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}` assuming each step's (a); (c) `γ_∞`, `δ_∞` with
   `|γ_∞ − 1| ≤ c₈q/(2(1−q))`, `|δ_∞ − 1| ≤ 3c₈q/(2(1−q))`, and the `β_j⁻¹` asymptotics, from the
   landed running-coefficient lemmas (prove the `δ_∞` bound if missing: review S-10).
3. **Lemma 3.3 application** (§3.5): continuity of `ξ⁰` in a parameter given uniform convergence of
   the data (`fixedPoint_dist_le` + uniform bounds), stated abstractly.

**Ownership.** New files under `Balaban/Flow/` (e.g. `MatrixInfty.lean`, `RGInfty.lean`) in your
worktree `/home/scott/Balaban-worktrees/W29` (branch `w29-rg-infty`), plus import lines in
`Balaban.lean`. Small additions to landed `Balaban/Flow/*` only if unavoidable (say which). Never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,000 lines, or a precise obstruction (a coefficient bound of
Lemma 3.1 that fails numerically — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
