# Brief W13b — uniqueness of the infinite-volume limits of G-5

**Goal.** Upgrade the landed `Balaban.Green.infiniteVolume_limits` (W13,
`Balaban/Green/InfiniteVolume.lean`: subsequential limits of `aGQ*`, `Δ_tr`, `C_tr` along tori of side
`L·M_n`, `M_n → ∞`) to genuine limits: for every `ν ∈ [0, 2]` the entries converge along **every**
sequence of tori with side `→ ∞` (in the block structure used there), the limit does not depend on
the sequence, and it satisfies the decay and Lipschitz bounds. Route (GREEN.md G-5(b) and
re-review F-18): compare two tori through a common box with the geometric resolvent identity
(landed `Balaban.Green.greenFn_resolvent_identity`, `domain_difference`, `perturbation_tails`), using
the block decay `oneScale_blockDecay` (fine operator, block sources) and `coarseGreen_decay`
(coarse operators) to show the difference of corresponding entries is `≤ C e^{−c·(distance to the
box boundary)}`, hence Cauchy. Identify the entries across tori by the box embedding (you may
reuse `Balaban/Correlations/Box.lean` from W11). If a cleaner route exists (the limit solves the
infinite-volume equation `H_ℤ K = 1_block` and decaying solutions are unique, via a maximum
principle or coercivity on `ℓ²(ℤ^d)`), use it and say why.

**Ownership.** New files under `Balaban/Green/` (e.g. `InfiniteVolumeUnique.lean`) in your worktree
`/home/scott/Balaban-worktrees/W13b` (branch `w13b-limits`), plus import lines in `Balaban.lean`.
Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Uniqueness and full convergence for `C_tr`, `Δ_tr` and `aGQ*`, or about 1,500
lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
