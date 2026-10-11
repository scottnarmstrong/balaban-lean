# Brief W8b — G-2(i): L² Agmon decay of the multiscale Green's function

**Goal.** Formalize G-2 step 1 and step 2 of `notes/phase1/GREEN.md` (final version: §3 statement
G-2(i), §4.2 proof by a quadratic-form Agmon/Combes–Thomas argument with the multiscale path
metric, complex α allowed; §4.3 the scale mismatch via the separation condition; the
path-metric lemmas and counting lemma they use), on top of the landed `Balaban/Multiscale/*`
(W8a: `GeneratingSet`, `dirichletOperator`, `pathDist`, `multiscale_coercive`,
`dirichletOperator_isCoercive`) and `Balaban/Green/*`:

1. **Path-metric lemmas** (§1.4, §4.2): Lipschitz property of `x ↦ pathDist x y₀` across a bond
   (cost `≤ 1/ℓ(b)`), the comparison with block distances needed in §4.2–4.3, and the separation
   consequence `d(y, y') ≥ ϱ(|j − j'| − 1)₊` (Lemma 4.3).
2. **Agmon estimate (G-2(i)).** For `f` supported in a block `Δ(y')` and `u = G_D(α) f`, the
   weighted `L²` bound `‖e^{ε d(·, y')} ℓ^{−1} u‖ + ‖e^{ε d(·,y')} ∂u‖ ≤ C ‖ℓ f‖`-type estimate of §4.2
   with GREEN.md's explicit `ε₀(d)` (state exactly what §4.2 proves; conjugate by
   `e^{ε d(·,y')}` — a truncated version of `pathDist` if needed to stay finite — and absorb the
   commutator errors with `multiscale_coercive`). Then the block-to-block form
   `‖χ_{Δ(y)} G_D(α) χ_{Δ(y')}‖ ≤ B₀ e^{−γ₀ d(y,y')} (ℓ_{j'}/ℓ_j)`-type bound of G-2(i).
3. **Scale mismatch (§4.3)** under the separation condition.
4. If budget remains: G-2(vi) (single-variation locality with analyticity in α).

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `PathMetricBounds.lean`, `Agmon.lean`,
`ScaleMismatch.lean`) in your worktree `/home/scott/Balaban-worktrees/W8b` (branch
`w8b-agmon`), plus import lines in `Balaban.lean`. Small additions to landed files only if
unavoidable (say which). Copy freely from any of the author's repositories (no attribution
needed); a continuum Agmon template is in `/home/scott/Superdiffusion*` (`agmonRate`,
`setIntegral_sq_le_exp_of_agmonMass`).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction (an inequality of
§4.2–4.3 that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
