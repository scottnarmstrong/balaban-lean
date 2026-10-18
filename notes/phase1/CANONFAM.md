# CANONFAM (W1077, notes only): are the choices behind the coefficient family `e` canonical?

Scope: `e0CoeffFamily_class_exists_tower_struct_step` (`Inhabited/StepTowerChainStep.lean:49`, W1069 `…_collar_classEps` and the
`_agree_collar` cores are instances of it) down to `E0CoeffFamilyGCore`, `E1CoeffFamilyGCore`, `ZeroSourceActivityCommonCore`.
Read from source; nothing was built. Items marked (?) were not traced to the end.

## Where `e` comes from
The step theorem is `…_struct_step_decoupled` followed by the `β₀` choice, then `…_struct` / `…_struct_onSet`
(`StepTowerChainStruct.lean:59,178,278–285`), which call `e0CoeffFamily_value_fromTowerG_core`
(`E0CoeffFamilyGCore.lean:162`, proof at 397–484). That core shows `e θ C = dz θ C + c θ C` (`:458`, `fun θ C => dz θ C + c θ C`,
`rfl`), with `c` given by `gsumCoeff` (clause `hc`, visible in `E0CoeffFamilyG.lean:100–115`) and `dz` by `detParamFamily`
(`E0CoeffFamilyGCore.lean:50`). So the formula already exists one level below the chain theorem. The chain theorem
(`StepTowerChainStep.lean:122–170`) then forgets it: `∃ e B`, constrained by analyticity, locality, bound, support, and the SUM
identities (`E0locJ = Σ e`, `densE0 = Σ e`).

## Table of choices (outermost first)
Quantifier order in the landed statement: `κmin, T, δ₃, δfl, κdec, β₀` (all torus-free, chosen before `k, N₁, ν, β, p₁`),
then `Jr` (per `S`, i.e. per `N₁, k, ν, β, p₁`), then `C, z`, then `Gk, Gj, X₀, X₁f`, then `e, B`.

| # | Choice | Where | Chosen from | Unique/canonical? | Depends on torus / family / β,k |
|---|---|---|---|---|---|
| 1 | `T : StepTower κmin`, `κmin, δ₃, δfl, κdec, β₀` | `StepTowerChainStep.lean:49,167–169`; `exists_stepTower_collar*` (W1069) | existence of thresholds | NOT canonical, but torus-free and chosen once | none: they precede `N₁`. This is the part that already agrees across tori |
| 2 | `Jr : S.JointRep T.t (2p₁)` (`F₀, Mx, Pc, Fb` analytic maps) | `StepComplexJoint.lean:198`, `nonempty_jointRep`; `E1CoeffFamilyGCore.lean:310` | `exists_analytic_bgC`, `exists_analytic_hatCovSqrt`, `exists_analytic_composeField`, `theorem72_analytic` (Classical.choose via `obtain`) | Values on the real chart are forced by `F₀_eq, Mx_eq, Pc_eq, Fb_eq` (unique small solution, `bgFieldC_eq_of_le`; `hatCovSqrt`; `composeData`). Off the real chart it is only the analytic continuation: determined if the real slice `rawOf D` determines analytic functions (identity theorem; needs connectedness of `XiCRaw`, (?)) | per torus (`N₁`), `k, ν, β, p₁`; no family dependence |
| 3 | `E : DetExpansionLocC …` and `dz` | `E0CoeffFamilyGCore.lean:415–419` (`obtain ⟨E, hEterm⟩`, `detParamFamily`; `Classical.choose hmem` at `:71`) | `detExpansionLocC_scale_of_towerG`; `choose` of the analytic extension in `detParamFamily` | `E.term D' C = Σ_y detActivityBg …` is an explicit formula (`hEterm`); `dz` is the formula at the unique `D` with `rawOf D = θ` (`BgData.eq_of_raw`, `:81`). Canonical on the chart, no free choice | torus: yes (blocks `blockU z`); no family, no extra dependence on `k, β` beyond the formula |
| 4 | `F₁, Sol` (marks background and fluctuation maps per block) | `E1CoeffFamilyGCore.lean:309` via `e1MarkParam_pairs_fromTowerG` (`E1CoeffFamilyGFields.lean:55,138`), `markCorrFamily_fromTowerG` (`DecMarkCorrFamilyFromTowerG.lean:32`) | existence of maps with the defining property of the decoupled solution on the union domain | values on the domain are unique (defining property = unique small solution); outside the domain arbitrary but unused (the `Fk` premises of the step theorem already say "the composed datum does not depend on the choice") | one family `(F₁,Sol)` chosen BEFORE all parameters and roots (comment at `E1CoeffFamilyGFields.lean:44`): hence not even torus-uniform as a choice, but canonical in value |
| 5 | `I0` (direct-terms record), `Lab₀ = thickLabels I0.𝒴 I0.dom`, `Lb` | `E1CoeffFamilyGCore.lean:310,317`; `ZeroSourceActivityCommonCore.lean` doc: domains `I.𝒴` = polymer domains of local covers | `zeroSourceActivity_common_fromTowerG_core` | combinatorial and explicit (polymer domains); canonical | torus: yes; invariant under spin rotations (they do not move cubes) |
| 6 | `A₀ : physParam → ℂ → LabelAct …` (activities `H(Y;Φ)`), `εH` | `E1CoeffFamilyGCore.lean:312` (`hcom`), `hdat` at `E0CoeffFamilyG.lean:96–103` | `activityFamilyAnalytic_of_witnessG_rho`, `segAct_hW_of_parts` (`ActivityFamilyAnalytic.lean:246`) | At zero source the term of each `Y` is the explicit potential part `-β Σ_z [Y∈polyDom_z] σ∫ω ∂_w³ evTerm_z(Y)` (doc of `ZeroSourceActivityCommonCore`), so per-`Y` canonical there. For general `θ=(raw,g)` the statement `hdat` gives only `WoneC = Σ_y H y` a.e. (a SUM over labels): per-label identification off the zero-source slice is by analytic continuation, (?) not stated | per torus; `k, β` through the formula |
| 7 | the marks `G θ i u Φ = e1MarkGParamG S F₁ Sol p₁ hp z T.t θ i u Φ`, `y0` | `E0CoeffFamilyG.lean:105–112` | explicit in `F₁, Sol` | explicit formula | per torus, `z` |
| 8 | `c θ C = gsumCoeff μ Lab₀ (A₀ θ) y0 G C` | `Thm31CoeffA.lean:70`; clause `hc` | formula `∫₀¹ Gsum ds` | canonical GIVEN rows 5–7; `gsumCoeff_congr_ae` shows only the a.e. class of `H` matters | per torus (`μ` = product over blocks of the torus) |
| 9 | `B`, and the families `Bτ, Gk, Gj, X₀, X₁f` | `StepTowerChainStep.lean:70`, `E0CoeffFamilyG.lean` | `∃` of constants / generating sets | NOT canonical; constants and bookkeeping sets, not labels; irrelevant to covariance | per `τ`, torus |

Conclusion of the table: in `e = dz + c`, every ingredient is either an explicit formula or a value pinned by a uniqueness
theorem on the real chart (unique small solution, unique `D` with `rawOf D = θ`, explicit polymer domains). The only genuinely
non-canonical items are row 1 (torus-free, harmless), row 9 (constants), and the analytic continuation in rows 2, 6 (needs the
identity theorem on `physV`; (?) connectedness not checked).
The failure of W1076 is therefore a statement problem, not a construction problem: `e0CoeffFamily_class_exists_tower_struct_step`
hides a family that the core theorem determines.

## (1) Explicit formula for `e`
Yes, in the following sense. `e θ T' = dz θ T' + gsumCoeff μ Lab₀ (A₀ θ) y0 (G θ) T'` with rows 3–8. Writing this in a theorem
statement without new definitions means quantifying over `F₁ Sol Lb Lab₀ A₀ …` with the big types of `E0CoeffFamilyG.lean:70–115`
(about 60 lines of binder), which is unwieldy. Recommended form: do NOT expose the formula; add CONCLUSIONS proved from it.
- Core: `e0CoeffFamily_value_fromTowerG_core` (`E0CoeffFamilyGCore.lean`) already exposes `c` and `dz`; add two conjuncts to the
  `e` clause: (a) per-label spin covariance, (b) per-label two-torus agreement. Old theorem = projection.
- Forwarders whose statements must grow by the same conjuncts (old ones become corollaries, about 10–20 statement lines + a
  5-line forward each): `…_struct_onSet`, `…_struct`, `…_struct_step` (`StepTowerChainStep.lean`), `_step_decoupled`,
  `_struct_onSet_dec_agree_collar`, `_struct_step_dec_agree_collar`, `_collar_uniform`, `_collar_classEps`, and the three `_step`
  domain variants in `StepTowerChainStepDom.lean` and `StepTowerChainStepPair.lean`: about 10 statements, 150–250 lines.
- Alternative of exposing the formula: same forwarding cost plus about 60 binder lines per statement, and every consumer must
  then rebuild covariance itself. Worse.

## (2) Per-label rotation covariance and two-torus agreement from landed lemmas
Rotation (`hTlrot`, shape: `Tl (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = Tl p`, `LocalClassDensityLevel.lean:347`).
- Landed, enough for row 3: `detActivityBg_rot`, `rootTraceBg_rot`, `barField_rot`, `decCov_rot`, `decLog_rot`
  (`DetRotation.lean:367–409`), `exists_detExpansionLocC_rot` (`:442`). Row 3 per label: covered up to bookkeeping (about 80 lines).
- Landed ingredients for rows 5–7: `composeData_rot`, `d1Triple_rot`, `F₁_rot_cover`, `fanLC_rot_cover`, `eTermFun_rot_cover`,
  `localHat_integral_rot_cover`, `clipRaw_rot`, `localB_{eTermHat,mTermHat,freshTermHat}_evTerm_rot`
  (`LocalClassRot.lean`, `LocalClassMRot.lean`), `fresh_amp_rot_pair`. These are for the COVER/local versions with the local
  centred terms, not for `F₁, Sol` of the tower nor for `e1MarkGParamG`.
- Missing (new): (i) covariance of `F₁, Sol` themselves (needs `F₁ ∘ rot = rot ∘ F₁` on the domain: from uniqueness of the small
  solution plus `composeData_rot`; (?) the tower's `Fk` is only characterised on the union domain, which is rotation invariant if
  `xiDom_act_iff` has a spin analogue (only the lattice version `xiDom_act_iff` is landed in `StepTowerNewLevelSymMain.lean:46`));
  (ii) covariance of `H(Y;·)` for the direct terms (rows 6), from the `evTerm_rot` lemmas plus (i); (iii) invariance of the block
  product measure `μ` under `Φ ↦ rot Φ` (landed only as `measurableEmbedding_hatRot`, `decCovSqrt_rot`, for the whole hat variable,
  not for `blockSplit`); (iv) `gsumCoeff` equivariance (`Gsum` integrand), about 100 lines; (v) identification of `A₀ θ` for complex
  `θ` with the explicit formula (identity theorem on `physV`; needs the real slice to be determining, a connectedness fact
  that is not in the notes). Estimate 400–700 lines, the bulk in (i)–(iv). No new mathematics beyond P3 p. 78, but (v) is a real
  gap until checked.
- Domain subtlety: `e` lives on `physV` (a neighbourhood of the axis datum). `hTlrot` quantifies over all `Q ∈ O(N)` with the point
  `p` in the field domain, and uses `Tl` on rotated points. The identity can only be proved for `Q` with `Qθ ∈ physV` unless `Tl`
  is extended off the chart; consumers (`LocalClassDensityLevel.lean:612`, `LocalClassCentre.lean:734`) must be checked to see
  which version they need (not checked). This is independent of how `e` is built.

Two-torus agreement of each label.
- Everything torus-independent (row 1) is chosen before `N₁`. Rows 2–8 are canonical per torus, so agreement of `e(ℓ)` and
  `e(ℓ')` is a statement about locality and transport of an explicit formula, not about coherent choices. The `∃ Jr` per `S` does
  not matter once covariance/agreement conjuncts are proved inside the core, where the formula is visible.
- Model for the proof: `gsumCoeff_transport`, `gsumCoeff_blockSplit_twoTorus`, `gsumCoeff_e1_twoTorus_of_domainLabels`
  (`Polymer/TwoTorusE1Coef.lean:961,1063,1348`), `gsumCoeff_e1_twoTorus_fromTowerG` (`TwoTorusDirectTermsTower.lean:301`),
  `gsumCoeff_param_congr_of_local` (`ParamCarrierLocal.lean:116`). These are for the E1 coefficient; row 3 (`dz`) has no
  two-torus lemma in these files (not found by grep of the TwoTorus files; may exist under another name).
- Root-F (`LogPartitionMultiscale.lean:48–71`) needs ONE `T ℓ` per `ℓ` and the pairwise clause for all `ℓ, ℓ'`. Defining
  `T ℓ` from `e` at `N₁ = ℓ` by a single `choose` per `ℓ` is legitimate if the agreement conjunct holds for every pair with the
  SAME `e`. A pairwise statement for two tori with possibly different `e` (as in the current chain theorem, one existential
  per `N₁` after `β₀`) gives nothing. The `can`/finite-family dependence of W1041 (3) arises in `Tn`, the tower terms of
  `TwoTorusGapTower*`, not in `e`; it is a separate item.

## (3) Symmetrizing
- Haar average over `O(N)`: `N = 2` throughout, so `O(2)` is explicit, but `e` is defined only on `physV` around the axis datum
  (see the domain subtlety), so there is no way to average over a non-small subset of `O(2)`. Averaging over the small stabilizing
  rotations does not produce invariance. Not a route.
- Reduction to the axis (`trickFnA`, `avgFamilyA` in `SmallField/RenormClassFamily.lean:140`): defines a covariant extension
  `ẽ θ := e(R_θ θ)` by a complex-orthogonal normalising rotation (those lemmas are for `TermFamily`, i.e. class terms near the vacuum
  field, not for `e`). For `N = 2`, `R_θ` is the rotation by minus the angle of `Ψ(root)`; `Σ ẽ = densE0` follows from the landed
  invariance of `densE0` and analyticity, locality (root in `T'` by the support clause), support and bound are preserved
  except for a radius loss because `R_θ θ` is a sup-norm perturbation of the same size (room: the same `C ≤ 1.7` obstacle as W1075).
  Plus a 2-element average for the reflection stabilizer. This gives `hTlrot` without exposing the construction, at the price of
  a radius loss that W1069 has no room for. Uncertain; not recommended before the room is checked.
- Root-F's single family: symmetrization commutes with restriction and cannot create agreement between tori. It does not help.
  Lattice covariance (translations permute labels and roots) cannot be obtained by averaging either: averaging over translations
  moves the root `z`.

## Recommendation
1. Do not expose the formula and do not symmetrize. Strengthen `e0CoeffFamily_value_fromTowerG_core` with two conjuncts on `e`
   (per-label spin covariance on `physV`, and per-label two-torus agreement of the same `e` for every pair `ℓ, ℓ'`), prove them
   where `e = dz + c` is visible, and forward through the chain theorems (about 10 statements, 150–250 lines of forwarding).
2. Proof cost 400–700 lines: covariance of `F₁, Sol` and `H(Y;·)` via the landed `*_rot` lemmas, block-measure invariance,
   `gsumCoeff` equivariance, plus the identity-theorem step for `A₀` off the zero-source slice (the single real gap; check
   connectedness of `physV` first).
3. Check first which `Q`/domain `hTlrot` is consumed with; if only `Q` keeping `Qθ ∈ physV` is needed, covariance is a local
   statement and the cost drops by the extension issue.
4. Root-F: ask for the agreement conjunct for ALL pairs from one `e`, not per finite family.
