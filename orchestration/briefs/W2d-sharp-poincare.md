# Brief W2d — sharp (d-free) block Poincaré and d-free coercivity constants

**Goal.** The landed block Poincaré inequality `Balaban.blockPoincare`
(`Balaban/Green/BlockPoincare.lean`) has constant `(d/2)·N²`. GREEN.md §4.1 (Lemma 4.1) uses the
sharp `d`-free block gap `−Δ^N_block ≥ 4N^{−2}(I − P_block)` (one-dimensional Neumann gap
`4 sin²(π/2N) ≥ 4/N²`, tensorized over directions). The `d`-dependence propagates into
`coerciveConst d`, the multiscale coercivity (`Balaban.Multiscale.multiscale_coercive`), the
x-variant (`xDirichletOperator_isCoercive`, whose admissible `α₀` range then misses P3's
`a_{k+1}L^{−2}/12` — GREEN.md re-review N-1), and the Agmon rates.

1. **Sharp block Poincaré.** `Σ_{x∈B} |φ(x) − avg_B φ|² ≤ (N²/4) Σ_{bonds inside B} |φ(x) − φ(y)|²`
   for every block `B` of side `N` in `Torus d ℓ` (`ℓ = N·m`), any `d ≥ 1`. Route: the 1D discrete
   Neumann Poincaré with constant `1/(4 sin²(π/(2N)))` (or any proof of the `N²/4` bound, e.g. via
   the eigenvectors `cos(π k (x+1/2)/N)` or a direct telescoping/Hardy argument that gives `N²/4` —
   check which constant you can prove cleanly; `≤ N²/2` is acceptable if `N²/4` is costly, as long
   as it is `d`-free), then tensorize (the variance of a product-structure block decomposes by
   directions).
2. **d-free coercivity.** New theorems (do not edit landed statements; add `_sharp` versions):
   `multiscale_coercive_sharp` with a constant `c₁` independent of `d` (state it), and the x-variant
   `xDirichletOperator_isCoercive_sharp` with the admissible range `|α₀| ≤ a_{k+1} L^{−2}/12` on
   `Ω_{k+1}` (re-review N-1), if it now follows; otherwise state the range you get.
3. If cheap: the corresponding `_sharp` Agmon rate `agmonRate_sharp` (independent of `d` through
   `c`), without redoing the whole Agmon development — only if the landed proofs take `c` as a
   parameter (W14 added `agmon_energy_gen`, `green_G2i_gen` with a free constant `c`).

**Ownership.** New files under `Balaban/Green/` and `Balaban/Multiscale/` (e.g.
`BlockPoincareSharp.lean`, `CoercivitySharp.lean`) in your worktree
`/home/scott/Balaban-worktrees/W2d` (branch `w2d-sharp-poincare`), plus import lines in
`Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–2 (3 if cheap), or about 1,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
