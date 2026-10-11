# Brief W10 — basic properties of the frozen model (CORRELATIONS packages A and B)

**Goal.** Prove the basic facts about the frozen model definitions (`Balaban/Frozen/Model/*`:
`Torus`, `aprioriMeasure`, `energy`, `partitionFunction`, `gibbsExpectation`, `onePoint`,
`twoPointTruncated`) that every later argument uses, following `notes/phase1/CORRELATIONS.md`
(revised) §0.1, Lemma 0.1, Lemma 0.2, Prop 1.4 and §6 packages A and B:

**Package A (sphere measure and symmetries).**
1. `volume.toSphere` on `EuclideanSpace ℝ (Fin N)` (`N ≥ 1`) is a finite measure with positive
   total mass; `aprioriMeasure d N ℓ` is a finite measure with positive mass (`Measure.pi`).
2. `O(N)` invariance: for `R` a linear isometry of `EuclideanSpace ℝ (Fin N)`, `volume.toSphere`
   is invariant under the induced map of the sphere (via volume preservation of
   `LinearIsometryEquiv` and the polar/`homeomorphUnitSphereProd` structure — or copy the
   author's `orthogonalSphereSurfaceMeasure_invariant` from
   `/home/scott/Intermittency/Lean/Intermittency/Analysis/OrthogonalSphereMeasureInvariance.lean`;
   copying from any of the author's repositories is allowed, no attribution needed); the
   product statement for `aprioriMeasure` (`Measure.pi` transport).
3. Symmetries of the model (Lemma 0.2): `energy` and the Gibbs weight are invariant under
   simultaneous rotation `φ ↦ Rφ`, `h ↦ Rh`, and under torus translations; consequences:
   `onePoint (Rh) = R onePoint h`, `twoPointTruncated` covariance, translation invariance,
   and for `h` fixed by a reflection the block structure (`⟨φ_x⟩ ∥ h`;
   `G = G_tr (I − h⊗h) + G_lg h⊗h` with `G_tr, G_lg` scalars depending on `x − y`) — state
   exactly what Lemma 0.2 claims and prove it for `N ≥ 2`.

**Package B (the partition function).**
4. `partitionFunction` is entire in `g` (as a function on `Torus d ℓ → Fin N → ℂ`), real and
   positive at `g = 0` (equal to `∫ e^{−βH}`), with `Re(Z(g)/Z(0)) > 0` on
   `Σ_x Σ_i |g x i| < 1` (because `|Im⟨g,φ⟩| < 1 < π/2`), so `Complex.log (Z g / Z 0)` is analytic
   there (Lemma 0.1).
5. Derivatives at `g = 0` (Prop 1.4): the first derivative of `log(Z(g)/Z(0))` in the direction
   `δ_x e_i` is `onePoint … x i`; the mixed second derivative in `δ_x e_i`, `δ_y e_k` is
   `twoPointTruncated … x y i k` (use `hasFDerivAt_integral_of_dominated_of_fderiv_le` or
   differentiation under the integral for finite products of compact factors).

**Ownership.** New files under `Balaban/Model/` (non-frozen; e.g. `SphereMeasure.lean`,
`Symmetry.lean`, `PartitionFunction.lean`, `Derivatives.lean`) in your worktree
`/home/scott/Balaban-worktrees/W10` (branch `w10-model-basics`), plus import lines in
`Balaban.lean`. You import the frozen *definitions* (`Balaban.Frozen.Model.*`); never
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–5, or about 2,000 lines, or a precise obstruction (e.g. a Mathlib gap
for `toSphere` — state it).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
