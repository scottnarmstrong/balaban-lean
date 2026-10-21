# BASE-ORCHC — the first step (blocker 1, A3-1/A3-2): design and work queue (ORCH-C, 2026-10-21)

Status at start (main `e1645f6c`): the assemblies are landed (W1148): `basePreStepInput_of_parts`,
`baseFlatStepInput_of_parts`, `baseStepInput_of_maps` (`Spine/BasePre.lean`, `BaseFlat.lean`) prove the two inputs from
a first-step map `Γ : BaseMap` (record `BaseRaw`: `z₁, R, geo, cs, P, sf, κK, SD, KD, KDgam, B, St, vc, Ev`) and the
parts `BaseSFInput`, `BaseConstsInput`, `BaseCorrInput`, `BaseFormInput`, `BaseBdryInput`, `BaseOpBoundInput r`,
`BaseCoherenceInput r`, `BaseVacuumInput` (and the flat variants). What is open is `Γ` and the parts.

## 1. The record `Γ`, field by field

| field | object (source) | how the parts about it are proved | who |
|---|---|---|---|
| `R, geo, cs, P` | the constants of Definition II.1.1 at the running constants of `sf` (LFR §II.1.1, D-IV.2, D-IV.11) | `BaseConstsInput`, `BaseOpBoundInput r` follow from the choice and the facts of `sf` (`Rep.opBound_of_data_le`) | C1 |
| `sf` | the scale-1 small-field data of the first fluctuation integral (Prop. II.7.9; P4 (2.42)–(2.54); LF-BASE-KF0 Part A) | the SF parts are the general step's predicates at `k = 0` (§2) | §3 |
| `SD` | step data whose scale-0 kernels are the base kernels `K₀ = gaussProd · Σ_w F^w K̃^w e^{b₀}` (Def. II.7.6, (II.7.4)) | `Γ.SD nK := baseStepData_at_class … (inp nK)` with `inp` the physical carrier (`Spine/BaseCarrier.lean`); `BaseKernelInput` by construction; (S2) is Lemma II.7.8 | §4 |
| `κK, KD, KDgam` | no kept data at scale 1 (Lemma II.7.7 (c), II.7.2 (c)) | canonical empty kept data, `γ_i = log 5 + A₃' λ̂_i^{p_R}` | queue Q2 |
| `B` | `ℬ^{(1)}`: polymers of the first SF integral meeting `Z₁` and `Z₁^c` (P6 p. 14 at `k = 0`) | `BaseBdryInput` (D7, rate `3κ/2`, `B_st`) | after §3 |
| `St, vc` | the source form of `ℰ^{(1)}` and the limits of P1 (3.106)–(3.110) | `BaseCorrInput` (`D1CorrLim`) | after §3 |
| `Ev` | `E₀ = 0`, `E₁` the vacuum constant of the first step | `BaseVacuumInput` | queue Q3 |

## 2. The small-field part as the general step at `k = 0`

The general small-field step is split on a map `Φ : SFData k → SFData (k+1)` into the predicates `SFInheritQ`,
`SFNewLevelQ`, `SFRenormQ Pc`, `SFDensityQ`, `SFRemainderQ fac`, `SFCoherenceQ` (`Spine/SFStep.lean`), assembled by
`sfSucc_clauses` / `sfFlatSucc_clauses` (`Spine/SFStepClauses.lean`, `FrozenSFClauses.lean`). These predicates read the
input data only through the inherited levels `j ≤ k`, of which there are none at `k = 0`. So `BaseSFInput` and
`BaseFlatSFInput` are replaced by the same predicates applied to `(bareSF β ν, Γ.sf)` at `k = 0`, plus the base facts
(`β₀ = β`, `ν₀ = ν`, `a₁` free flow, `z₁ = sf.z 1 > 0`, (I.2) at `0` from the typing facts), assembled by a `k = 0`
analogue `sfBase_clauses` (no splice: every clause of scale 1 is the new level's). Then row (a) is literally A4-1b–f at
`k = 0` for the first-step map, and the provider's `Φ` at `k = 0` is the first step.

## 3. The first fluctuation integral (row (a)) — what is base-specific

All-good sector, then a region `Z₁^c`. With `θ = z₁ψ₁` and `A₁(φ;θ) = H(φ) + (aL^{d-2}/2)Σ_y|θ_y − Qφ(y)|²`:
`ρ₁ = const · e^{-βA₁(e_θ;θ)} · ∫ e^{-(β/2)⟨w,H_α w⟩ + ⟨g,φ⟩} χ dσ`, `w = φ − e_θ` (chord identity, exact), and by the chart
(LF-BASE-KF0 (A.3)) the integral is `β^{-m/2}(2π)^{m/2} det(C_e)^{1/2} ∫ J(v) e^{-⟨v,Hz⟩−½⟨z,Hz⟩+⟨g,φ⟩} χ dγ(ψ')`,
`v = Q_e C_e^{1/2} ψ'`. Base-specific ingredients and their state:
- background `e_θ`, `α_θ` at level 1: landed (`baseBackground_analytic_localB`, `decBg_one_eq_bgField_of_inDomainR`,
  `baseSectorDatum_decBg_one`); two tori: C3.
- covariance family `C_e(s)`, square root, exact core agreement, decay: landed (`baseCovX_*`, BASEX.md); two tori: C3;
  logarithm only at the physical point (`baseCovX_log`; `baseCovX_log_not_integrable` off it): the determinant needs its
  own localization (open; design below).
- chart interaction: pointwise local form landed (`Base/BaseRemainderLocal.lean`); the LabelAct assembly is landed as a
  template (`baseActivity_LabelAct`, `baseActivity_LabelAct_parametrix`); the activities themselves (analytic in the
  background and in `s`, `DepOn`, bound) are open.
- the generic layer (LabelAct, `marked_cubes_explicit`, `marked_cubes_two`, `gsumCoeff`, Mayer/PE) is abstract in the
  measure and the activities and applies as it stands.
- RG at scale 1: regime (B) P4's system (the general `rg_step_infty` pattern), regime (A) the ν-free system.

### 3.1 Leaves of row (a), in order (all-good sector first, then a region)
- (a1) exact identity of the all-good sector: `ρ₁ = c · e^{-βA₁(e_θ;θ)} · det(C_e)^{1/2} · ∫_{|ψ'_x|<p₁} J e^{-V} dγ` (chord
  identity `action_sub_eq_chord_quadratic`, chart `ChartIntegral.lintegral_sphere_pi_eq_gaussian_sqrt`, `BaseChartRetained`),
  and `A₁(e_θ;θ)` = the class action at scale 1 at the level-1 background (`baseOp_baseHamiltonian_one`,
  `decBg_one_eq_bgField_of_inDomainR`; units of `expo2`).
- (a2) the chart interaction `V = Σ_x V_x(e, α, v)`, `v = Q_e C_e^{1/2} ψ'`, `V_x = Σ_y v_x·H_{xy} z_y + ½ Σ_y z_x·H_{xy} z_y
  − log J_x(v_x) − β^{-1/2} g_x·(v_x + z_x)` (+ the ν-term in regime (A)), `H = G_α^{-1}` of range `L`; pointwise forms landed
  (`BaseRemainderLocal`).
- (a3) decoupled chart activities: `V_x(s, ψ') := V_x(e(s), α(s), C^{1/2}(s; e(s), α(s)) ψ')` with the level-1 decoupled
  background and `baseCovX_sqrt`; (AE1) analytic in `s` on `|s_P| < e^κ` and in the data, bounded by `C β^{-1/2} p₁³` on
  the cutoff; (AE2) exact agreement when `s` and the data agree near `x` (`baseCovX_sqrt_exact`,
  `baseBackground_value_cross_localB`); abstract Lemma AE with data (`Localization/I5Param.lean`,
  `abstract_expansion_on`) gives `V_x = Σ_{Y ∋ x} V_{x,Y}`, `DepOn Y`, `‖V_{x,Y}‖ ≤ C e^{-κ' d(Y)}`; `LabelAct` by
  `baseActivity_LabelAct(_parametrix)`.
- (a4) `μ_b` := the normalized Gaussian of `ψ'` on the block `b` restricted to `|ψ'_x| < p₁` (its normalization goes to the
  vacuum constant; the complement is the `𝖱₁` record); `marked_cubes_explicit` gives `∫ e^{-V} dμ = exp Σ_Y Pst(Y)` and the
  source marks; analyticity of `Pst` in the data by parameter integrals (`Polymer/LaplaceAnalytic`).
- (a5) determinant: `½ log det C_e = -½ tr log A_e`, localized through a shifted logarithm of the decoupled family,
  `Λ(s) := ∫₀^∞ ((1+x)^{-1} c(s) − C_x(s)) dx`, `c(s) = P_e + (Σ_z s_z χ_z) Q_e` the large-`x` coefficient (BaseXLog
  docstring); needs `‖C_x(s) − (1+x)^{-1} c(s)‖ ≤ B (1+x)^{-2}` on `DecDom`; `Λ(1) = log A_e`; then the rooted trace and
  the mixed differences as in `DetCauchyActivity`.
- (a6) RG at scale 1: constants of the local terms → `E₁`; relevant parts → `ξ^{(0)}` (`β₁, ν₁, z₁`); the rest → `ℰ^{(1)}`
  with (H.5) by construction; regime (B) first (P4's system), then regime (A) (ν-free).
- (a7) the class clauses of the level-1 terms (`SFNewLevelQ` at `k = 0`: term clauses on `sfDom`, `GsSpecStrong`,
  `HatSpec`, `TorusIndep`), `SFRenormQ`, `SFDensityQ`, `SFRemainderQ preFac`, `SFCoherenceQ`.
- (a8) a region `Z₁^c` with retained spins on `Ω₁^c` (`baseChartIntegral_retained`): the polymers meeting `Z₁` split into
  `b₀` (inside) and `ℬ^{(1)}` (crossing), P6 p. 14 at `k = 0`.

## 4. The base kernels (row (b)) and the transform relation (row (c))
`K̃^w e^{b₀}` populates the R7 carrier (`BaseSmallFieldInput.Kphys`); open: its definition from (II.7.4)/(II.7.6) with the
cutoff transfer (CT, `bondCross`), the D4 cross-witness identity, (S2) = Lemma II.7.8 (gains: P landed, Q/R/S = C2).
(c) `D1PreForm2`: insert the base decomposition into (II.7.1); `baseRho1_eq_sum_firstP` and `baseRetained_disintegrate`
are landed.

## 4a. Findings
- (C2) **The constant `A₃` of the first-component gain.** LFR row 9 sets `A₃ = ¼ min{8γ₀A₀²/(6^d(9K₁)²), A₁²/8}` from
  P6 (3.7)–(3.8). The landed bridge from a failed `χ_1`-type test to a `Ψ̃` violation (`R/ChiBridge.lean`) forces the
  tolerance `θ = δ/(6K₁)` (the lift loses a factor 3), so half of `𝒜₁` pays only `γ₀ p₀²/(288 a K₁²)` per cube before the
  `6^d` overlap: short of the source by about `14a` (`𝖰₁`) and `72a` (`𝖲₁`). Either the bridge constants are sharpened or
  `A₃` is taken smaller (`A₃ = S.A3` is a field of the typing, chosen in A1′); whether a smaller `A₃` is compatible with
  the lower bounds the budget (`S.Good`, Lemma II.5.12) puts on it is to be checked in A1′.
  *Resolved (C2, `Base/BaseA3.lean`, `notes/phase1/BASE-A3.md`):* `Typing.A3` is free (`Typing.Ok` asks `A3 > 0`; the
  prefix witness has `A3 = 1`; the LF-2 conditions bound `λ_*` from below, not `A₃`). The weaker gains raise the lower bound
  on `A₀` instead (`exists_A0_for_A3`). Open for A1′: that `A₀` can be raised in the prefix (row 9 `A₀ = 4K₂B₅A₁`,
  (Λ23) `A₁/A₀` small); the mixed bridge for `𝖰₁`.
- (C3) The two-torus x-chain of `Polymer/TwoTorusXGreen.lean` needs `XSetting` (mass bound `νL^{2K} ≤ 1`), false at the
  shifted mass `ν + x`; it is re-proved for `Dec2.XCover` in `Base/BaseTwoTorus*.lean`, the landed lemmas to become its
  instances.

## 4b. Dependencies of row (a) on the other blockers
Row (a) is A4-1b–f at `k = 0`. Its term construction meets the open problems of the general provider `Φ`: the terms of the
new level on the local generating sets `𝔹_1(X̂)` (ruling R13; blocker 6 at `k = 0`), the RG extraction (A4-1c), the
remainders `ℛ^{(1)}` (A4-1e), and in regime (A) the ν-free system (blocker 2). The base-specific inputs (covariance,
determinant, chart, kernels) are built here; the parts are stated as the general predicates at `k = 0` so that work on `Φ`
transfers. Blocker 1 closes only with, or after, the general small-field provider.

*Alternative for the covariance (route FR-1, recorded, not chosen yet).* As in `KF0-FR.md`, whiten with a finite-range
polynomial `C_R(e) = p_R(A_e) ≈ A_e^{-1/2}` instead of the decoupled square root: the Gaussian becomes the product
measure times `exp(-½⟨ψ', Q_R ψ'⟩)`, `Q_R = C_R A_e C_R − 1` of range `O(R)` and row sums `O(q^R)`, all chart activities
are finite range, and the block gas of route FR (`KF0FRGas`, `mayerGen_pe`, `Polymer/LaplaceAnalytic`) applies; the
determinant `log det C_R(e) = tr (log ∘ p_R)(A_e)` localizes exactly by telescoping Chebyshev approximants
(`Σ_n tr (f_n − f_{n−1})(A_e)`, term `n` of range `O(n)` and size `O(ρ^n)`). The background `e(θ)` still needs the
decoupled background and Lemma AE (or the local generating sets of blocker 6). Decide after C3's shifted logarithm.

## 5. Queue
- C1 (running): constants, `BaseConstsInput`, `BaseOpBoundInput`, assemblies without `hC`, `hO`.
- C2 (running): `𝖰₁, 𝖱₁, 𝖲₁` gains.
- C3 (running): two-torus agreement of `baseCovX`, its square root, the level-1 background.
- Q1: `sfBase_clauses`, the base SF sub-inputs on `(bareSF, Γ.sf)`, `baseSFInput_of_parts`, flat analogue.
- Q2: kept data at scale 1 (empty), `κK`, `KDgam`.
- Q3: the vacuum flow `Ev` and `BaseVacuumInput` once `SD`'s vacuum constants are fixed.
- Q4 (ORCH-C design): the first-step activities (chart terms on the base covariance) as `LabelAct`; determinant
  localization; then the level-1 terms.
