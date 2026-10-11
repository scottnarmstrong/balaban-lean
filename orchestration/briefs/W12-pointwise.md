# Brief W12 — interior estimates and pointwise bounds (Lemma Loc, Lemma P, Prop 4.8)

**Goal.** Start the pointwise block of the Green's function layer (`notes/phase1/GREEN.md`, final;
§4.5: Lemma K, Lemma Loc, Lemma P, Proposition 4.8 — the main risk of the layer, written at plan
level with the key steps; Section 5 risk notes). Lemma K is landed (W9:
`Balaban/Green/Lattice/*`, `Balaban.LatticeGreen.latticeGreen`, `latticeGreen_equation`,
`latticeGreen_le_rpow`, `latticeGreen_diff1_le_rpow`, `latticeGreen_diff2_le_rpow`).

1. **Lemma Loc (a), (b)** on the unit lattice `ℤ^d` (spacing 1; state the scaling to spacing `η`
   separately as a lemma about rescaled functions): for `−Δu = g` on the `ℓ^∞` ball `B_{2ρ}(x₀)`,
   `ρ ≥ 8`, and `x ∈ B_{ρ/2}`: `|u(x)| ≤ C ρ^{−d/2} ‖u‖_{L²(B_{2ρ})} + Σ_{z∈B_{2ρ}} |C(x−z)| |g(z)|`
   and the gradient version with `∂C`. Proof as in GREEN.md: product cutoff `χ` (one-dimensional
   lattice samples of a fixed smooth profile, or an explicit piecewise-linear one with the needed
   first and second difference bounds), `v = χu`, the representation `v = C * (−Δv)` (from
   `latticeGreen_equation` and finite support), the discrete Leibniz formula, summation by parts,
   and the bounds of Lemma K on the annulus.
2. **Lemma Loc (c)** (Hölder-type difference bound with exponent `1 − θ`, constant `C/θ`), if (a),
   (b) are done.
3. **Lemma P and Proposition 4.8** (G-2(ii) pointwise decay for `u = G_D(α)f`, `f` supported in a
   block) on top of `Balaban/Multiscale/*` (W8a, W8b, W8d: `dirichletOperator`, `agmon_block`,
   `green_G2i`, `sqrt_sqNorm_le_of_supp`), following GREEN.md's recursion (absorbing the block
   term). Stop and report if a step of the plan does not close.

Infrastructure (G-2 provider work as editable targets).

**Ownership.** New files under `Balaban/Green/Lattice/` (Loc) and `Balaban/Multiscale/` (Lemma P,
Prop 4.8) in your worktree `/home/scott/Balaban-worktrees/W12` (branch `w12-pointwise`), plus
import lines in `Balaban.lean`. Copy freely from any of the author's repositories (no attribution
needed), e.g. discrete difference quotients in
`/home/scott/CoarseGraining/Homogenization/Sobolev/Foundations/DifferenceQuotient.lean`, interior
estimates in `/home/scott/EllipticRegularity`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Item 1 at least; then 2–3 as far as possible; about 3,000 lines; or a precise
obstruction (a step of the plan in GREEN.md §4.5 that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; which steps of §4.5 are proved and which
remain; checks and results; axioms; open questions; last commit hash.
