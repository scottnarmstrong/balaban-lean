# Brief W1 — lattice blocks, block averaging, exact Gaussian identities

**Goal.** Build the infrastructure every later component uses: block hierarchies on the frozen
torus, the block-averaging operator and its adjoint, finite-dimensional Gaussian integrals with
determinants, and the exact Gaussian block-spin (Schur complement) identity of Balaban's
renormalization transformation. This is off-frontier infrastructure (recorded reason: needed by
G-1…G-6, I-1, I-4, the small-field flow and Root-C; `notes/phase1/PLAN.md`).

**Ownership.** New files under `Balaban/Lattice/` and `Balaban/Gaussian/` in your worktree
`/home/scott/Balaban-worktrees/W1` (branch `w1-lattice-gaussian`), plus the import lines for them
in `Balaban.lean`. No other edits.

**Frozen files (read only).** `Balaban/Frozen/**`. Your torus is `Balaban.Torus d ℓ = Fin d → ZMod ℓ`
(`Balaban/Frozen/Model/Torus.lean`). Do not import anything under `Balaban/Frozen/Roots/` or
`Balaban/Provider/` (quarantined drafts).

**Sources.** P1 §1 (pp. 103–110: the block averaging `Q`, (1.11), the renormalization
transformation `T`, normalization (1.12)) and P2 §1; P4 (2.23)–(2.25), (5.12)–(5.13) (Woodbury);
E3 (3.8) (composition of block transformations); P9 (4.12)–(4.17) (`H_j`, `C^{(j)}`, the exact
decomposition of `Δ^{-1}`). Reviews: `review/papers/P1-*.md`, `P2-*.md`, `P4-*.md`, `E3-*.md`,
`P9-*.md`; roadmap `review/FORMALIZATION_ROADMAP.md` §3.4 (G-6) and §7.3 items 1 and 4.

**Targets, in order** (each an editable working target; state each theorem in the form the
sources use it; choose and document conventions in each file's module docstring):

1. Blocks of side `L^j` on `Torus d ℓ` when `L^j ∣ ℓ`: the block map to `Torus d (ℓ / L^j)`, its
   fibres (cardinality `L^{jd}`), compatibility of scales (`block_{j+k} = block_k ∘ block_j`).
2. Block averaging `Q` (average over an `L`-block) and its adjoint `Q*` for the weighted inner
   products of P1 (lattice spacing `η`, weight `η^d`); `Q Q* = I`; `Q* Q` is the orthogonal
   projection onto block-constant fields; `Q_j = Q ∘ ⋯ ∘ Q` averages over `L^j`-blocks.
3. Gaussian integrals on `Fin n → ℝ` (or `ι → ℝ` with `Fintype ι`) for a real symmetric positive
   definite `A`: `∫ exp(−½⟨φ, Aφ⟩ + ⟨J, φ⟩) dφ = (2π)^{n/2} (det A)^{−1/2} exp(½⟨J, A^{−1}J⟩)`
   with complex `J`; the normalized Gaussian measure with covariance `A^{−1}`; its moments of
   order ≤ 2. Survey first (do not rebuild what exists): Mathlib (`multivariateGaussian`,
   `integral_cexp_neg_sum_mul_add`, `Matrix.PosDef`), `/home/scott/FroehlichSpencer/FroehlichSpencer/FS82/Gaussian/*`,
   `/home/scott/mining/DOZZ/GaussianFields/*`, `/home/scott/KPZ/Lean/Phi4/Phi4/Law/{ProductGaussian,GaussianIBP}.lean`.
   Copy and adapt (with attribution in the module docstring), do not add Lake dependencies.
4. Schur complement and Woodbury identities for finite matrices (check Mathlib first).
5. The Gaussian block-spin identity: for `A` positive definite on fine fields and `a > 0`,
   `∫ exp(−½⟨φ, Aφ⟩ − (a/2)‖ψ − Qφ‖²) dφ = C · exp(−½⟨ψ, Δψ⟩)` with
   `Δ = a − a² Q (A + a Q*Q)^{−1} Q*`, the minimizer `φ = (A + aQ*Q)^{−1} a Q* ψ`, and the
   positivity `Δ > 0`; the composition of two such steps (E3 (3.8)).
6. If time remains: the exact multiscale decomposition of `(−Δ + ν)^{−1}` on the torus by iterating
   5 (P9 (4.17)), stated for a finite number of steps.

**Checks.** `lake build` of your modules only, in your worktree (at most one build at a time;
compiles are throttled machine-wide and may wait for a slot); zero warnings; `#print axioms` on
the main theorems shows only `propext`, `Classical.choice`, `Quot.sound`;
`python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Targets 1–5 complete, or a precise obstruction (state it and stop). Budget:
stop and report after about 3,000 lines or if a target needs a change of conventions affecting
other packages.

**Hard rules** (from `AGENTS.md`, verbatim in substance): every `.lean` file is a module (`module`
header, `public import` for the interface, `@[expose]` where bodies must unfold); no `axiom`, no
`sorry`/`admit`, no heartbeat overrides, no placeholder definitions, zero warnings; frozen files
are read-only; no file over 10,000 lines; do not bypass the compile throttle; commit on your
branch only, never push to `main`.

**Handoff.** Files; conventions chosen; the main theorem names and statements; exact checks and
results; axioms; open questions. Commit on branch `w1-lattice-gaussian` and report the commit.
