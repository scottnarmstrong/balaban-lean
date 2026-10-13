# GENDN: removing the fixed dimensions and spin count

13 October 2026. Source tree /home/scott/Balaban was read only. **PROVED** means a landed statement or a calculation from its
definition. **OPEN** means a needed general physical or geometric theorem. **REFUTED** means a stated inference does not follow.
File.declaration references below were checked by `rg`; names in the leaf table are proposed.

## Frozen prefix and block scale

**PROVED.** Frozen/Roots/LogPartitionMultiscale.lean states the quantifier prefix exactly:

```lean
theorem logPartition_multiscale (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
```

Thus L may
depend on d,N,δ,κ,c₉ and is fixed before β,ν,h. The frozen proof is `sorry`, so this is a target quantifier order, not an
existence result. **OPEN verdict.** Nothing inspected proves that L=3 works for every d≥3. Nothing inspected proves that L=3 fails
for large d either. The safer Root-F strategy chooses one odd L≥3 after κ,c₉ and then uses it in every lane. **REFUTED:**
fixed-three arithmetic alone supplies this choice for general d,N.

**OPEN source threshold.** The P5–P7 text layers did not yield an explicit bound $L_0(d)$; P4's scan OCR is unreliable. The
paper's large-block convention therefore gives no checked license here to set $L=3$, nor a checked formula for $L_0(d)$.

**PROVED.** General `Localization.MooreDegree.layer_not_near` assumes d≤ϱL²; a larger separation parameter ϱ can pay that premise
at L=3. Other visible constraints include 4L²≤L^m₁ and cstarX·exp(N₀κ)≤L^m₁, both payable by m₁ for any L>1. The factor 4d(2L+1)^d
κdec is payable by choosing κ large. The values aEnt d L, coerciveConst d, gamma1 d and Green constants enter finite thresholds
and positive small-radius choices. No `L²>2d` hypothesis was found on the inspected tower path. This does not prove simultaneous
feasibility of the full physical step.

**PROVED.** `Fluctuation.DetCollarHull.collarBase` fixes box base b−a for a box of side La.
`DetCollarHullSymm.collar_image_reflect` and `detCollarHull_cubeAct_genSymm` assume L=3. The reflection of [b−a,b−a+La) has base
c−b−(L−1)a; the collar of the reflected cube has base c−b−2a. These agree exactly for L=3. **OPEN chosen-L repair.** For odd
L=2q+1, base the box at b−qa. Then the reflected base is c−b−(L−q)a=c−b−(q+1)a, which is the box based on the reflected cube.
Reprove containment, hull geometry, size, fibre, decay and grouped symmetry. The current general `detCollarHull_isDj` and
`detCollarGrouped_bound` concern the old hull; their constants cannot be silently reused.

## Specialization inventory

| Source | Fixed essential step; general or incidental part | Status |
|---|---|---|
| `I5Inhabited.GP`, `G0`, `rhoSep`, `exists_m₁`; `Prop33CloseWitness.nuW` | The I-5 witness uses d=L=3, N₁=6, K=2; the physical mass instance `nuW=1/81` and spin-two step are separate. `rhoSep` and exponential growth use 3. General `levelGS` exists. | Fixed witness **PROVED**; general one **OPEN**. |
| `InteractionLevelPair.Gp`, `Hm` | The consecutive-level pair used by the physical tower fixes d=L=3, N₁=9, K=2; its abstract `flCore_level_eventually` is general. | Pair witness **PROVED**; general family **OPEN**. |
| `StepRegWitness.exists_witness_params` | Type fixes 3,3,2; `witB5`, `witK2`, `fluctRadius 3 3 2` are fixed. General positivity and `exists_deltaStar` underlie the radius selection. | General theorem **OPEN**. |
| `StepActivityDirectPhysicalRates.tower_core_rates` | N is a binder, d=L=3 in all 21 clauses. 40000, 9261, 4116 and `norm_num` are fixed certificates; `decSpecs_exists`, `Dec2.decSpecs_exists` and `flCore_level_eventually` are general. | General theorem **OPEN**. |
| `TowerCoreRatesAtLeast.tower_core_rates_at_least`; `TowerCoreRatesRen.tower_core_rates_at_least_ren`; `TowerCoreRatesRenSol.tower_core_rates_at_least_renSol`; `TowerCoreRatesTwoRadii.tower_core_rates_at_least_two` | Repeat 3,3, then add κmin, solution, and doubled-radius margins. Additional t↓0 arguments are symbolic after positivity. | General variants **OPEN**. |
| `LevelStepSetting.lvTop`, `lvLow`, `hatStepK` | Types fix 3,3,2. `hatStepK_betaU` proves β_k=β3^k; for general d,L the definition gives β_k=βL^{k(d−2)}. `unitBg` and `levelGS` are general. | General setting **OPEN**. |
| `LevelRayTower.flCore_level_transfer`, `scale_C_items` | Transfer is general in d,L,N with supplied hypotheses. Scale theorem fixes 3,3,2, β3^k, `lvCpsi`, `lvR`, `lvKappa`, and √2. | Transfer **PROVED**; scale theorem **OPEN**. |
| `InteractionLevelPair.flCore_level_eventually` | Already general in d,L,N; its use by fixed `tower_core_rates` is incidental. | **PROVED** conditional interface. |
| `DetCauchyBgActivityWitness.detDeg_three_rate`, `DetOutputTermsWitness.log_detDeg_three_lt` | 214991878, 57 and 18=2dL are fixed arithmetic. `P6PairParamDegree.detDeg_eq` is general. | Symbolic rate **OPEN**. |
| `DetCollarHull.*`, `DetCollarHullSymm.*` | Old hull geometry, size and fibre allow d variable, L≥3. Reflection/grouped symmetry require L=3. | General bounds **PROVED**; chosen-L symmetry **OPEN**. |
| `DetPackageFromTower.detHullThreshold`, `towerDetHullRate_ge`; `StepOutputConsts.stepOutput_consts_exists_ge`; `StepOutputPhysical.stepOutputPhysical` | 3375=c1 3 3, 60750=cG 3 3·c1 3 3, 60751=1+60750, 214991878=detDeg 3 3+1, 18=2dL. `StepOutputConsts d L` itself is general. | General scalar ledger **OPEN**. |
| `LevelLocalCover.levelLocalCover` | Already general in d,L,N; assumes 1≤m₀ and L^m₀∣N₁, not 5<N₁ or no-wrap. For m₀=1 it requires L∣N₁. | **PROVED** conditional on `DGSetting`. |
| `StepTower`, `StepTowerRen`, `StepTowerRenEnd`, `StepTowerRenSol`, `StepTowerTheta` | All record field types inherit 3,3,2; `StepTower.core` is `Nonempty (FlCore 2 …)`. | Parametric records **OPEN**. |
| `DetRotationWitness.rotQuarter` | Concrete matrix `!![0,-1;1,0]` and `Fin.sum_univ_two` prove one O(2) test, not arbitrary O(N). | Example **PROVED**; general transport **OPEN**. |

**PROVED cover correction.** `LevelLocalCover.nbhd_eq_univ` makes the neighbourhood the whole torus when N₁≤(2L−1)L^m₀;
`nbhdF_ne_univ` uses the strict reverse inequality to show it is proper. Neither inequality is in `levelLocalCover`. The 5<N₁
premise enters concrete `LevelStepSetting.dgSetting_lv` and `opSetting_lv`. A general no-wrap application must state its own N₁
threshold.

## Six symbolic replacements

**OPEN tower_core_rates_general.** Given d≥3,L≥3,N≥2, κ₀≥aEnt(d,L)+2, κdec≥3κ₀+c1(d,L)+5 and κmin, return m₁,c,BG,κ,t,c₂,BG₂,δc
with the 21 clauses of `tower_core_rates` at d,L,N plus κmin≤κ. They are: m₁≥4, t>0, FlCore; κ₀≥0, κdec≥3κ₀+3; the 4d(2L+1)^d
rate, κ-one and logarithmic bounds; c7 cap and cstarX·exp(N₀κ) block cap; domain, coercivity and δc² margins; five t caps (2t,
cK2·2t, cK2·t, cK2′·t, background-1); entropy bound, output-rate relation and nonnegative famConst. Replace `log 9261≤9260` by log
A≤A−1 for A=(2L+1)^d L^d>0, or simply choose κ above 2+4log A. Choose κ above the finite rate, c7, determinant and hull
thresholds, then m₁, δc and t in that order. The general positivity inputs are landed; simultaneous assembly is **OPEN**. The
fixed 40000 must not be used as a universal bound.

**OPEN witness_params_general.** Replace `witB5`, `witK2` and `fluctRadius` by d,L,N versions and return the inequalities of
`exists_witness_params` with arbitrary prescribed lower T. The proof uses `pow_unbounded_of_one_lt` for L>1, positive `deltaStar`,
`bgC0`, `bgC1`, `thm73C3`, `coerciveConst`, `bgK1`, a positive minimum for δ′, and a large T for finite witness constants. The
fixed N₁=6 example is not an all-torus step producer.

**OPEN det_rate_general.** `P6PairParamDegree.detDeg_eq` gives D=detDeg d L=3(L+4)^d+9(L+9)^d(8L)^d. For κ>log2+2log(D+1),
exponentiation gives 2(D+1)² exp(−κ)<1. Any κ₀ strictly above this threshold yields the inequality for κ≥κ₀. Also choose κ′≤λdet,
λdet=(κ−log2−2log(D+1))/(2dL). This uses symbolic log monotonicity, not the fixed 57 check.

**OPEN det_rate_hull_general.** Put B=cG(d,L)c1(d,L) and κout=3κdec/2. Set κhull=2dL(1+B)(κout+c1(d,L)log2)+log2+2log(D+1), adding
positive slack when a strict determinant premise is required. If κ≥κhull, then λdet/(1+B)−c1(d,L)log2≥κout. This is the closed
form behind `detHullThreshold`, `hullRate_ge_of_le` and `StepOutputConsts.stepOutput_consts_exists_ge`. The scalar algebra is
routine; the chosen-L hull B/fibre proof is **OPEN**.

**OPEN scale_C_items_general.** Define d,L,N variants of `lvKappa`, `lvCpsi`, `lvR` using √N, `covSupMaxC d L N κ`, and
b=βL^{k(d−2)}. Retain `pLog A₁ p b`, strict `RayData` disc and both inequalities of `scale_C_items`. For fixed d,L,N,κ,t,
`pLog_le_mul_sqrt` provides a scale-independent β₀ with p₁≤c₀√b. The radius algebra re-instantiates; general `hatStepK_betaU`,
`compWeight_three_mem` and typed RayData need new bridges. **REFUTED:** b=βL^k is the physical β_k for d>3.

**PROVED conditional cover input.** `LevelLocalCover.levelLocalCover` already supplies block and source-site covers at chosen
d,L,N from DGSetting, IsLevel, 1≤m₀ and L^m₀∣N₁. For a proper local neighbourhood also impose (2L−1)L^m₀<N₁ using `nbhdF_ne_univ`.
For the full step retain the concrete generating-set size premises separately. No new proof of `levelLocalCover` is called for.

## N and migration

**PROVED.** `tower_core_rates N` and `flCore_level_eventually` already carry arbitrary N. `LevelStepSetting.hatStepK` uses `hN2`,
`unitVec hN2` and `unitBg`; the general unit-vector construction accepts 2≤N. Fixed constants in `StepRegWitness`,
`LevelRayTower`, `StepTower` and `StepOutputPhysical` still mention 2. The transverse sector has N−1 modes, so covariance and
determinant constants must retain N even though `detDeg d L` has no N argument. `DetRotationWitness.rotQuarter` is only a Fin 2
example; physical O(N) source/class/measure transport remains **OPEN**.

**OPEN StepTowerG target.** Define `StepTowerG (d L N : ℕ) (κmin : ℝ)` with 3≤d, 3≤L, 2≤N, one chosen full-level pair, and general
fields corresponding to `StepTower`, `StepTowerRenSol` and the output ledger. For odd-L symmetry attach `Odd L` or a centred-hull
witness. Prove `exists_stepTowerG` after the level-pair, numeric, determinant and hull leaves. It is a producer at a chosen L, not
an assertion uniform over all L≥3.

**PROVED inventory size.** Literal `rg` in read-only Inhabited Lean finds 31 files mentioning `StepTower`, 19 mentioning
`hatStepK`, and 50 mentioning one of `StepTower`, `hatStepK`, `StepSetting 3 3`. Those 50 files total 13,257 source lines.
Fixed-typed examples are `StepTowerScale.detExpansionLocC_scale_fromTower`, `ChartDetJointFromTower.stepPieces_fromTower`,
`DetPackageFromTower.detPackage_fromTower`, `StepPiecesRenSol.stepPieces_fromTowerRenSol`,
`MarkedRootAssemblyFromTower.markedRootAssembly_zero_fromTower` and `SourceWitnessJoint.sourceWitness_fromTower`. Changing the
numeric witness alone cannot change these result types.

**Recommendation B, OPEN implementation.** Keep the existing 3,3,2 files as an instance while adding general records and
endpoints. Estimate 8–12 initial numeric/setting modules, 1,500–3,000 lines, then 35–50 endpoint modules or adaptations,
6,000–12,000 lines. The 50-file/13,257-line search is an envelope, not a measured diff. Option A edits those landed files in place
with similar proof volume and a much larger re-elaboration surface while chosen-L geometry is open. Once general endpoints work,
make the old proofs corollaries to avoid permanent duplication.

| Ordered proposed leaf | Exact output and dependency | Size / assignment / start |
|---|---|---|
| `det_rate_general` | General D, z<1 and log rate from `detDeg_eq`. | ≤120 lines; **OPEN**, Sonnet, pure symbolic; now. |
| `det_rate_hull_general` | Closed κhull and `StepOutputConsts d L` scalar algebra, with an abstract hull B. | ≤180 lines; **OPEN**, Sonnet, pure symbolic; now. |
| `witness_params_general` | d,L,N positive radii and arbitrary lower T. | ≤250 lines; **OPEN**, strong; now. |
| `level_setting_general` | General lvTop/lvLow, hatStepK, β_k identity, and a ϱ meeting all separation bounds. | ≤280 lines; **OPEN**, strong; now. |
| `level_covers_general` | FlCore and block/source covers from `flCore_level_eventually` and `levelLocalCover`; keep N₁ premises separate. | ≤240 lines; **OPEN**, strong; after setting. |
| `tower_rates_general` | General 21-clause core at prescribed κmin. | ≤300 lines; **OPEN**, strong; numeric skeleton now. |
| `tower_margins_general` | Renormalized-solution and doubled-radius variants of the core tuple. | ≤280 lines each; **OPEN**, strong; after core. |
| `scale_C_items_general` | β₀ and RayData at b=βL^{k(d−2)}. | ≤300 lines; **OPEN**, strong; after setting. |
| `collar_centered_geometry` | Odd-L box definition, containment, polymer property and size bound. | ≤280 lines; **OPEN**, strong; now. |
| `collar_centered_fibre` | Fibre cardinality and regrouped decay at the centred hull with explicit B. | ≤260 lines; **OPEN**, strong; after geometry. |
| `collar_symm_chosenL` | Reflection and grouped symmetry of the centred hull. | ≤280 lines; **OPEN**, strong; after geometry. |
| `exists_stepTowerG` | General record and producer with every field discharged. | ≤300 lines per record layer; **OPEN**, strong; after leaves. |
| `detPackage_fromTowerG`, `sourceActivity_fromTowerG`, `markedRoot_fromTowerG` | Separate general endpoints, each using the same tower and covers. | ≤300 lines each; **OPEN**, strong; integration after tower. |

**Scope.** This plan generalizes the numerical zero-class tower. It does not construct arbitrary-class, large-field, final-step,
O(N)-transport or torus-coherent Root-F coefficients.
