# Brief W24 — RG equations with a data-dependent matrix (SMALLFIELD.md (L1), (L2))

**Goal.** Formalize the two Lean requirements of `notes/phase1/SMALLFIELD.md` v2 §3.4 (review
S-03), on top of the landed `Balaban/Flow/RGEquations.lean` (`exists_rg_solution`,
`TriangularBounds`, `TriangularBounds.norm_le`, `TriangularBounds.exists_inverse`,
`exists_rg_solution_triangular`, `rgRadius`):

1. **(L1) `exists_rg_solution_triangular_param`**: as in §3.4 — `A : G → Matrix (Fin 3) (Fin 3) ℂ`
   analytic on the open set `P` with `TriangularBounds (A p) ε` for all `p ∈ P`, the hypotheses of
   the landed theorem otherwise unchanged (`c, f` depending on `(ξ, p)`); conclusion: an analytic
   solution map `ξ_s` on `P`, the equation, uniqueness in the closed ball of radius
   `rgRadius (42κ) c₁₀`, and `‖ξ_s p‖ ≤ 84 η`. Proof route of §3.4: `B(p) = A(p)⁻¹` analytic by the
   explicit triangular formula, `‖B(p) z‖ ≤ 42 ‖z‖` pointwise, then `exists_rg_solution`.
2. **(L2) `rg_solution_real`**: for a conjugate-linear involution `σ` of `G` preserving `P` with the
   conjugation symmetry of `A, c, f`, `ξ_s (σ p) = conj (ξ_s p)`; in particular real for real data.
3. **Lemma 3.3** (stability of the fixed point: `‖ξ_p − ξ_{p'}‖ ≤ 2 sup_{B_{r₀}} ‖Φ_p − Φ_{p'}‖`), as an
   abstract lemma about contractions with Lipschitz constant ≤ 1/2 on a closed ball.
4. If cheap: Lemma 3.1 (the coefficient bounds of the λ = ∞ matrix (P4 (5.21)) for
   `a ∈ [9/10, 3/2]`, `0 < v ≤ 7/32`, …) as a statement about the explicit entries.

**Ownership.** New file(s) under `Balaban/Flow/` (e.g. `RGParam.lean`) in your worktree
`/home/scott/Balaban-worktrees/W24` (branch `w24-rg-param`), plus import lines in `Balaban.lean`.
Small additions to `RGEquations.lean` only if unavoidable (say which). Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3 (4 if cheap), or about 1,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
