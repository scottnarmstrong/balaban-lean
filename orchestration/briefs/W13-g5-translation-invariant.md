# Brief W13 — G-5: translation-invariant one-scale operators (extended mass range)

**Goal.** Formalize G-5 of `notes/phase1/GREEN.md` (final; §3 statement, §4.7 proof reduction)
with the mass range extended to `ν_j ∈ [0, 2]` as `notes/phase1/CORRELATIONS.md` (revised, §2.1
I-G, D-03) requires:

1. On the torus `T^{(j)}` (any volume; and on ℤ^d as limits) with
   `G_j = (−Δ^η + a_j Q_j^*Q_j + ν_j)^{−1}`, `a_j ∈ (1/2, 3/2)` (or the range CORRELATIONS.md D-08
   fixes), `ν_j ∈ [0, 2]`, `Δ^{(j)}_tr = a_j − a_j² Q_j G_j Q_j^*`, `C^{(j)}_tr = (Δ^{(j)}_tr + aL^{−2}Q^*Q)^{−1}`:
   (a) `|a_j G_j Q_j^*(x, y)| ≤ c e^{−δ|x − y|}` and `|C^{(j)}_tr(y, y')| ≤ c e^{−δ|y − y'|}`, uniformly in
   `j`, the volume and `ν_j`, with `c, δ` depending on `d, L` only;
   (b) Lipschitz dependence on `ν_j` in the kernel norm of (a);
   (c) infinite-volume limits (tori of growing side) satisfying (a), via the geometric resolvent
   identity at fixed `j` (GREEN.md G-5(b), re-review F-18).
2. Reduction as in GREEN.md: unit-scale decay from the landed G-4
   (`Balaban.Green.combesThomas`, `combesThomas_restrict`, `perturbation_tails`,
   `domain_difference`, `ballSum_L1Torus`), the coercivity of `Δ^{(j)}_tr + aL^{−2}Q^*Q`
   (landed `unconstrainedUnitOperator_lower`, `blockHamiltonianC_isCoercive`), and for
   `a_j G_j Q_j^*` the block decay (`green_G2i` with all `Ω_j` = whole torus, i.e. the single-scale
   case) — state precisely which norm the fine-to-block kernel bound is in.

Infrastructure (I-G of CORRELATIONS.md; recorded reason: Root-C's leading term, P9 (4.12)–(4.17)).

**Ownership.** New files under `Balaban/Green/` (e.g. `TranslationInvariant.lean`,
`MassLipschitz.lean`, `InfiniteVolume.lean`) in your worktree
`/home/scott/Balaban-worktrees/W13` (branch `w13-g5`), plus import lines in `Balaban.lean`. Copy
freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1(a)–(c), or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
