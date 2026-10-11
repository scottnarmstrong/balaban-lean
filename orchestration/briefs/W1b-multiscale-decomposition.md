# Brief W1b — the exact multiscale decomposition of the lattice Green's function

**Goal.** Iterate the landed Gaussian block-spin identity (`Balaban/Gaussian/BlockSpin.lean`,
`integral_blockSpin`, `integral_blockSpin_comp`, `blockSpinOperator_comp_inv`; `Balaban/Lattice/`)
to obtain the exact finite multiscale decomposition of the covariance `(−Δ + ν)^{−1}` on the torus,
as used in P9 (4.12)–(4.17) (Root-C's leading term) and E3 (3.8).

Statements (fix conventions in the module docstrings, consistent with W1's `blockMap`,
`blockAverage`, `latticeInner`):

1. **One step.** On the torus `Torus d ℓ` with `ℓ = L·m`, for `A = −Δ + ν` (`ν > 0`; the
   nearest-neighbour lattice Laplacian, `−Δφ(x) = Σ_μ (2φ(x) − φ(x+e_μ) − φ(x−e_μ))`, matching the
   frozen energy `Balaban/Frozen/Model/Energy.lean`) and `a > 0`:
   `A^{−1} = G + G a Q^T Δ^{−1} ... ` — precisely the decomposition
   `A^{−1} = (A + aQ^TQ)^{−1} + H Δ^{−1} H^T` with `H = a(A + aQ^TQ)^{−1}Q^T` and
   `Δ = a − a²Q(A + aQ^TQ)^{−1}Q^T` (the covariance splitting behind one RG step: fluctuation
   covariance plus the covariance of the minimizer `Hψ` of the block field). Prove it as a matrix
   identity from W1's Schur/Woodbury results.
2. **Iteration.** For `k` steps with block factor `L` (`ℓ = L^k·m`) and scale-dependent `a_j`, the
   telescoped decomposition
   `A^{−1} = Σ_{j=0}^{k−1} H_{0..j} C^{(j)} H_{0..j}^T + H_{0..k} Δ_k^{−1} H_{0..k}^T`,
   with `C^{(j)} = (A_j + a_j Q^TQ)^{−1}` the fluctuation covariance at step `j` and `A_{j+1}` the
   effective operator after `j+1` steps (written on the coarse torus, rescaled as P9 (4.13)
   requires, or unscaled with the scaling stated separately — choose and document).
3. **Positivity and symmetry** of every term; the effective operators are positive definite.

Infrastructure; recorded reason: needed by C-2 (Root-C), G-6, and the small-field flow
(`notes/phase1/PLAN.md` W1 target 6).

**Ownership.** New files under `Balaban/Gaussian/` (e.g. `Multiscale.lean`) and
`Balaban/Lattice/` (e.g. `Laplacian.lean` for the torus Laplacian as a matrix) in your worktree
`/home/scott/Balaban-worktrees/W1b` (branch `w1b-multiscale`), plus their import lines in
`Balaban.lean`. Do not edit the W1 files except to add small missing lemmas (say which).

**Sources.** P9 pp. 517–519 ((4.12)–(4.18)), P1 §1 (pp. 103–110), E3 §3 ((3.8)); reviews
`review/papers/P9-*.md`, `P1-*.md`, `E3-*.md`. Copy freely from any of the author's repositories
(no attribution needed): e.g. lattice Laplacians in `/home/scott/mining/Frohlich-Spencer`
(`FroehlichSpencer/BKT/FiniteGraph/{Laplacian,Green}.lean`, `FroehlichSpencer/Surface/*`).

**Checks.** `lake build` of your modules only (at most one build at a time; compiles are throttled
machine-wide and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Items 1–3, or a precise obstruction. Budget about 1,500 lines.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only and not
imported except the frozen definitions (never `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`);
no file over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
