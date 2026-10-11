# Brief W18b — G-2(vi′): locality and analyticity of the constrained sandwich Π

**Goal.** Formalize G-2(vi′) of `notes/phase1/GREEN.md` (§3 statement, marked PENDING there because
only the kernel-algebra outline of §4.6 exists; the outline is the proof route). Consumer: the
locality of the constrained covariance `C^{(k)}` in the data (GREEN.md C17, G-4 applied to
P4/P3 (i)), used by the localization of the effective actions.

For `(φ₀, α)` and `(φ₀′, α′)` both satisfying the hypotheses of G-2(v) (the landed `Standing`
structure, `Balaban/Multiscale/ConstraintSandwich.lean`) and equal off a set `Z ⊂ Ω₁`
(`φ₀ = φ₀′`, `α = α′` off `Z`), with `Π = G φ₀ [φ₀·Gφ₀]⁻¹ φ₀·G` (`constrainedOp`):

1. **Kernel algebra.** Define the block-decay class `𝒜_γ(C)` of GREEN.md §4.6
   (`‖χ_y ℓ⁻¹Tℓ⁻¹ χ_{y'}‖ ≤ C e^{−γ d(y,y')}` for blocks `y, y'`, `d` = `pathDist`) and prove: `G ∈ 𝒜_{γ₀}`
   (from `green_G2i`/`green_blockNorm_le`), block-diagonal multiplication operators are in every
   `𝒜_γ`, composition `𝒜_γ(C₁)·𝒜_γ(C₂) ⊂ 𝒜_{γ/2}(C′C₁C₂)` (Lemma 4.4 summation, landed as the
   counting lemma in `Balaban/Multiscale/Counting.lean`), and the operator `K(φ₀)Gφ₀` (landed
   commutator form) in `𝒜_{γ₀}(cδ₀)`; then `M⁻¹ ∈ 𝒜_{γ′}` for `M = φ₀² − K(φ₀)·Gφ₀` (Neumann series
   in the algebra; the landed `constraintM_isUnit` gives invertibility).
2. **Locality (vi′).** `‖χ_{Δ(y)}(Π − Π′)χ_{Δ(y')}‖ ≤ B ℓ_j ℓ_{j'} e^{−γ₀′(d(y,Z)+d(y',Z))} e^{−γ₀′ d(y,y')}`
   by telescoping `Π − Π′` into products with exactly one difference factor (`G − G′`: landed
   `green_sub_green_le_sum` / G-2(vi); `φ₀ − φ₀′`, `φ₀² − φ₀′²`: supported in `Z`;
   `K(φ₀) − K(φ₀′)`: coefficients differ only on `Z⁺`). State the constant dependence (`d, L, N`
   is acceptable).
3. **Analyticity.** `Π` is analytic in `(φ₀, α)` (finitely many complex variables) on the open set
   where the `Standing` hypotheses hold strictly, using `Balaban/Multiscale/Analyticity.lean`
   (`analyticAt_inv_apply`) for both inverses.
4. If budget remains: the same locality for the unit-lattice entries `Q_k(Π − Π′)Q_k^*`.

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `KernelAlgebra.lean`,
`ConstraintLocality.lean`) in your worktree `/home/scott/Balaban-worktrees/W18b` (branch
`w18b-constrained-locality`), plus import lines in `Balaban.lean`. Small additions to landed files
only if unavoidable (say which). Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.
Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction (a step of the §4.6
outline that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
