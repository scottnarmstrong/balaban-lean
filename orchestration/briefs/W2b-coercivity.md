# Brief W2b — coercivity (G-1) on the torus: block Poincaré, Neumann bracketing, Δ^{(k)} lower bound

**Goal.** Formalize the coercivity layer G-1 of `notes/phase1/GREEN.md` (§1 for definitions and
conventions, §3 for the statement G-1, §4.1 for the complete proofs), starting with the
single-scale case on the torus and building up:

1. **Block Poincaré.** On a block (cube of side `N` in `Torus d ℓ`, `ℓ = N·m`, blocks as in
   `Balaban/Lattice/Blocks.lean`), the Neumann Dirichlet form controls the variance:
   `Σ_{x∈B} (φ(x) − avg_B φ)² ≤ C_d N² Σ_{bonds in B} (φ(x) − φ(y))²` with an explicit `C_d`
   (state the constant you prove; GREEN.md §4.1 gives one).
2. **Single-scale coercivity.** For `a > 0`, `ν ≥ 0`:
   `⟨φ, (−Δ + ν + a Q^*Q) φ⟩ ≥ c(d) min(1, a N²) N^{−2} ‖φ‖²` (or the form GREEN.md states),
   using `latticeLaplacian` (`Balaban/Lattice/Laplacian.lean`) and `blockAverage`/
   `blockPullback` (`Balaban/Lattice/BlockAverage.lean`); the complex-`α` perturbation
   `Re⟨u, H(α)u⟩ ≥ …` for `|α| ≤ c` (G-1(a) at one scale).
3. **The unit-lattice operator.** With `Δ^{(1)} = a − a² Q (−Δ + ν + aQ^*Q)^{−1} Q^*`
   (`blockSpinOperator`, `Balaban/Gaussian/Schur.lean`): the Schur-complement variational form
   `⟨ψ, Δ^{(1)} ψ⟩ = min_φ [a‖ψ − Qφ‖² + ⟨φ, (−Δ + ν)φ⟩]` and the lower bound G-1(b)
   `Δ^{(1)} ≥ γ₀ (−Δ^{(coarse)} + ν')` with GREEN.md's `γ₀` (state exactly what is proved).
4. If budget remains: the multiscale version on generating sets (GREEN.md §1.2–1.3, G-1(a)
   with `ℓ(x)`), or report precisely what definitions it needs that do not exist yet.

Infrastructure (G-1 interface provider work as editable targets; recorded reason: needed by G-2,
G-4 hypotheses, P4 (2.25), (2.49), C9, C13).

**Ownership.** New files under `Balaban/Green/` (names not clashing with the landed
`Coercive.lean`, `CombesThomas.lean`, `Restriction.lean`, `GeometricResolvent.lean`; e.g.
`BlockPoincare.lean`, `Coercivity.lean`, `UnitLattice.lean`) in your worktree
`/home/scott/Balaban-worktrees/W2b` (branch `w2b-coercivity`), plus import lines in
`Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed), e.g.
Poincaré inequalities in `/home/scott/CoarseGraining`, `/home/scott/EllipticRegularity`,
lattice Laplacians in `/home/scott/mining/Frohlich-Spencer`.

**Checks.** `lake build` of your modules only (at most one build at a time; compiles are
throttled machine-wide and may wait; never bypass the throttle); zero warnings; `#print axioms`
standard; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction. GREEN.md is under
independent review (`notes/phase1/GREEN-review.md` when it appears); if you find an error in its
§4.1 proofs, stop and report it with the exact inequality that fails.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
