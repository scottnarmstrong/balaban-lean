# Brief W7 — holomorphy toolkit: Cauchy estimates, analytic contraction with explicit radii

**Goal.** The analytic tools every localization bound, the RG equations and the extraction of
correlation functions from Root-F use (roadmap §7.3 item 3; T1 of §5):

1. **Cauchy estimates in finite dimension.** For `f : E → F` (`E` a finite-dimensional normed
   ℂ-space, `F` a complex Banach space) analytic on the ball `B(z₀, R)` (any norm on `E`, stated
   for the sup norm on `ι → ℂ` and for general `E`) with `‖f‖ ≤ M` there:
   `‖f(z) − f(z₀)‖ ≤ M‖z − z₀‖/(R − ‖z − z₀‖)`; the derivative bound
   `‖Df(z)‖ ≤ M/(R − ‖z − z₀‖)`; the bound on the `n`-th Taylor coefficient along a direction;
   and the "first-order vanishing" form: if moreover `f(z₀) = 0`, then
   `‖f(z)‖ ≤ 2M‖z − z₀‖/R` for `‖z − z₀‖ ≤ R/2`. Also the polydisc versions (radii `r_i` per
   coordinate) and the mixed derivative bound `|∂_{z_i}∂_{z_j} f(z₀)| ≤ M/(r_i r_j)`, which is what
   extracting two-point functions from a generating functional needs.
2. **Analytic contraction with parameters.** Let `P` be an open set in a finite-dimensional
   ℂ-space, `B` the closed ball of radius `r` in a finite-dimensional ℂ-space, and
   `T : B × P → B` analytic with `‖T(ξ, p) − T(ξ', p)‖ ≤ θ‖ξ − ξ'‖`, `θ < 1`. Then the fixed point
   `ξ*(p)` exists, is unique in `B`, and is analytic in `p` on `P`, with explicit bounds
   `‖ξ*(p) − T(0, p)‖ ≤ θ r`-type estimates. Also the version with real-analytic restriction to
   real parameters (used for P4 §5, (5.23)–(5.27), and P2 Prop 1.1).
3. **Infinite products.** If `|ξ_k| ≤ c q^k` with `q < 1` and `c` small, then
   `γ_k = ∏_{j ≤ k}(1 + ξ_j)^{−1}` converges to `γ_∞` with `|γ_∞ − 1| ≤ 2c/(1 − q)` and
   `|γ_k − γ_∞| ≤ 2c q^{k+1}/(1−q)` (P4 (5.31)–(5.33): existence of `γ_∞`, `δ_∞`).

Infrastructure; recorded reason: needed by I-1, I-4, I-6, I-7, PE and the extraction of Root-C
from the flow (`notes/phase1/PLAN.md`).

**Ownership.** New files under `Balaban/Analysis/` in your worktree
`/home/scott/Balaban-worktrees/W7` (branch `w7-holomorphy`), plus their import lines in
`Balaban.lean`. No other edits.

**Sources to reuse.** Mathlib first (`Mathlib/Analysis/Complex/CauchyIntegral.lean`,
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, `DifferentiableOn.analyticOnNhd`,
`AnalyticOnNhd`, `HasFPowerSeriesOnBall`, `ContractingWith`,
`Mathlib/Analysis/Calculus/ImplicitFunction*`); the standard reduction to one variable along
complex lines `λ ↦ f(z₀ + λv)`. **Copy only from public repositories** (with attribution):
Mathlib, `scottnarmstrong/Frohlich-Spencer` (clone `/home/scott/mining/Frohlich-Spencer`),
`scottnarmstrong/AVAnomalousDiffusion` (`/home/scott/AVAnomalousDiffusion`),
`scottnarmstrong/CoarseGraining` (`/home/scott/CoarseGraining`). Do **not** copy code from private
repositories (`AVAnomalousRegularization-dev`, `KPZ`, `EllipticRegularity`, `FroehlichSpencer`).

**Checks.** `lake build` of your modules only, in your worktree (at most one build at a time;
compiles are throttled machine-wide and may wait for a slot; never bypass the throttle); zero
warnings; `#print axioms` on the main theorems shows only `propext`, `Classical.choice`,
`Quot.sound`; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Items 1–3 proved, or a precise obstruction. Budget about 2,000 lines.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module (`module` header, `public import`
for the interface, `@[expose]` where bodies must unfold); no `axiom`, no `sorry`/`admit`, no
heartbeat overrides, no placeholder definitions, zero warnings; frozen files are read-only and are
not imported by this package; no file over 10,000 lines; do not bypass the compile throttle;
commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
