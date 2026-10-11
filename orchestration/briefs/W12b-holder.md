# Brief W12b — third differences of the lattice Green's function, Lemma Loc (c), Prop 4.9 (G-2(iii))

**Goal.** Complete the pointwise block of `notes/phase1/GREEN.md` (final; §4.5 Lemma K third
differences, Lemma Loc (c), Proposition 4.9):

1. **Lemma K, third differences.** `|∂_μ∂_ν∂_λ C(x)| ≤ c⟨x⟩^{−d−1}` for the landed
   `Balaban.LatticeGreen.latticeGreen` (W9, `Balaban/Green/Lattice/*`), all directions and forward /
   backward differences. W12 reports that the landed heat-kernel estimate
   `heatDiffProd_integral_bound` accepts per-coordinate difference orders ≤ 2 only; either extend the
   one-dimensional heat-kernel bounds to third differences (`|∂³q_t(n)| ≤ c t^{−2} e^{−c′ min(n²/t,|n|)}`
   by the same contour shift) or reduce a pure third difference in one direction to mixed ones via
   `−ΔC = δ₀` away from 0 (W12's suggestion). Choose the cheaper route.
2. **Lemma Loc (c)** (GREEN.md §4.5): for bonds `b, b′` in direction `μ` at `x, x′ ∈ B_{ρ/2}`,
   `r = |x − x′| ≤ ρ/4`: `|∂u(b) − ∂u(b′)| ≤ C ρ^{−1−d/2} (r/ρ) ‖u‖_{L²(B_{2ρ})} + Σ_z |∂C(x−z) − ∂C(x′−z)| |g(z)|`,
   and the bound of the last sum by `(C/θ) G_∞ r^{1−θ} ρ^θ` for `|g| ≤ G_∞`, each `θ ∈ (0,1)`. Reuse the
   landed `Balaban/Green/Lattice/Loc*.lean` (cutoff, Leibniz remainder on the kernel,
   `sum_kernel_remainder`).
3. **Proposition 4.9 (G-2(iii))**: the Hölder bound for `∂u`, `u = H_D(α)^{−1} f`, exponent `1 − θ`,
   constant `B_θ = C(d, L)/θ`, on top of the landed `Balaban/Multiscale/Pointwise*.lean`
   (`prop48`, `lemmaP`, `PtSetting`).

**Ownership.** New files under `Balaban/Green/Lattice/` and `Balaban/Multiscale/` in your worktree
`/home/scott/Balaban-worktrees/W12b` (branch `w12b-holder`), plus import lines in
`Balaban.lean`. Small additions to landed files allowed (say which). Copy freely from any of the
author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–3, or about 3,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
