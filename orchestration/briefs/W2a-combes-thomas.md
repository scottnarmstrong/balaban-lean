# Brief W2a — Combes–Thomas bounds for exponentially decaying, non-Hermitian kernels

**Goal.** A general operator-norm Combes–Thomas theorem on a finite index set: if `A` is an
operator on `ι → ℂ^n` (or `ι → ℂ`; `Fintype ι`), with matrix entries bounded by
`|A(x,y)| ≤ c₀ e^{−δ₀ ρ(x,y)}` for a pseudometric `ρ` with uniformly bounded "ball sums"
`sup_x Σ_y e^{−δ ρ(x,y)} ≤ K(δ)`, and `Re A ≥ γ₀ > 0` (as a quadratic form), then for every
`t ≥ 0` the inverse `(A + t)^{−1}` exists and its entries satisfy
`|(A+t)^{−1}(x,y)| ≤ c₁ (γ₀ + t)^{−1} e^{−δ₁ ρ(x,y)}` with `c₁, δ₁ > 0` depending only on
`c₀, δ₀, γ₀` and the ball-sum function `K`. Also: the domain-restricted version (`A_Λ` for
`Λ ⊂ ι`, the same constants); the perturbation bound; and the geometric resolvent identity
relating `(A_Λ)^{−1}` and `(A_{Λ'})^{−1}`. This is G-4 of the roadmap (`review/FORMALIZATION_ROADMAP.md`
§3.4: E3 §5, (5.8), (5.10) as an interface, proved by our own route). Infrastructure; recorded
reason: needed by G-4, G-5, P4 (2.23)–(2.25), P9 (4.12)–(4.17) (`notes/phase1/PLAN.md`).

**Ownership.** New files under `Balaban/Green/` in your worktree
`/home/scott/Balaban-worktrees/W2a` (branch `w2a-combes-thomas`), plus their import lines in
`Balaban.lean`. No other edits.

**Starting point (copy and generalize, with attribution in the module docstring).**
`/home/scott/mining/Frohlich-Spencer/FroehlichSpencer/Infra/Green/{Basic,CombesThomas,CombesThomasGap,Iteration}.lean`
and `/home/scott/mining/Frohlich-Spencer/FroehlichSpencer/Infra/Resolvent/Basic.lean` (read-only clone of the public repository `scottnarmstrong/Frohlich-Spencer` at commit `b47bc3d`; cite that repository and commit in attributions, never the private development checkout `/home/scott/FroehlichSpencer`). Its `combesThomas_core` assumes a
Hermitian kernel of range one in a pseudometric, a real potential and `Im z ≠ 0`; the Hermitian
hypothesis is used only in `norm_weightPerturbation_le` and for column sums. Replace range one by
exponentially weighted row and column sums, drop the Hermitian hypothesis (use the lower bound
`Re A ≥ γ₀`, so `‖(A+t)^{−1}‖ ≤ (γ₀+t)^{−1}`), and allow `t ≥ 0` in place of `Im z ≠ 0`. Do not add
a Lake dependency on it.

**Method (standard).** Conjugate by `e^{ε ρ(x, y₀)}` (weights bounded by the triangle inequality);
the conjugated operator differs from `A` by an operator whose norm (Schur test on row and column
sums) is `≤ C(ε) → 0` as `ε → 0`; choose `ε` so that this is `≤ γ₀/2`; then the conjugated
inverse has norm `≤ 2/(γ₀ + t)`, and entries follow.

**Checks.** `lake build` of your modules only, in your worktree (at most one build at a time;
compiles are throttled machine-wide and may wait for a slot; never bypass the throttle); zero
warnings; `#print axioms` on the main theorems shows only `propext`, `Classical.choice`,
`Quot.sound`; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** The main theorem, the restricted version and the resolvent identity proved,
or a precise obstruction. Budget: about 1,500 lines.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module (`module` header, `public import`
for the interface, `@[expose]` where bodies must unfold); no `axiom`, no `sorry`/`admit`, no
heartbeat overrides, no placeholder definitions, zero warnings; frozen files are read-only and are
not imported by this package; no file over 10,000 lines; do not bypass the compile throttle;
commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
