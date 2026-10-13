# SRCRHO — fixed physical source radius in the coordinate-vector tower

**PROVED (source audit).** Read-only inspection of `/home/scott/Balaban/Balaban` at commit `e17670e`, 13 October 2026. The only output here is a dependency-ordered Lean work list. **OPEN:** no radius-$\rho$ Lean theorem has been proved by this note. The frozen Root-F statement in `Frozen/Roots/LogPartitionMultiscale.lean:42–72` remains unchanged. Set $\rho>0$ **before** choosing $\beta_0$; the route needs $\rho=\sqrt N$ and the coefficient target $c_9/\sqrt N$ before using `partitionFunction_rot`.

## T1. Exact carriers and bridge lemmas

Use the existing arguments and type aliases from the named files. These are proposed declarations, **OPEN** until compiled:
```lean
def l1BallRho (d L N₁ m₁ K N : ℕ) [NeZero N₁] [NeZero L] (ρ : ℝ) :
    Set (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  {g | ∑ x, ∑ i, ‖g x i‖ < ρ}
def physSΛRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ : ℝ) :
    Set (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :=
  XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
    l1BallRho d L N₁ m₁ (k + 1) N ρ
def physVRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ : ℝ) :
    Set (physParam N S) := physIncl N S ⁻¹' physSΛRho S a₁ ν eps ρ
def physVqRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ q : ℝ) :
    Set (physParam N S) :=
  {e | e ∈ physVRho S a₁ ν eps ρ ∧ ∑ x, ∑ i, ‖e.2 x i‖ < q}
def physFibreRho (S : StepSetting d L N₁ m₁ k N ϱ) (a₁ ν eps ρ : ℝ) :
    Set (physParam N S) :=
  {e | e ∈ physVRho S a₁ ν eps ρ ∧
    ∀ y i, (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 y i = (S.h₀ i : ℂ)}
```
**PROVED (definitional reduction of the displayed and landed bodies); OPEN in Lean until compiled.** `l1BallRho … 1 = l1Ball …`, `physSΛRho … 1 = physSΛ …`, `physVRho … 1 = physV …`, `physVqRho … 1 q = physVq … q`, and `physFibreRho … 1 = physFibre …` are proposed one-line `rfl` equalities after elaboration of the same implicit parameters. Keep their landed names and statements textually fixed; make each old proof a specialization at $\rho=1$. Also prove `physVqRho … ρ ρ = physVRho … ρ` by extensionality and the source clause.

**PROVED (mathematical lemmas), OPEN in Lean.** The finite sum $s(g)=\sum_{x,i}|g(x,i)|$ is continuous and convex. Hence $B_\rho=\{s<\rho\}$ is open and convex; for $\rho>0$, $0\in B_\rho$ and $t g\in B_\rho$ for $0\le t\le1$. `physVRho` and `physVqRho` are open under the same `BgHyp` as `isOpen_physV`, by the raw-chart preimage theorem and product/intersection openness. No landed source proof uses convexity of the whole raw chart, so do not claim it. A component bound from $g\in B_\rho$ is $|g_i(y)|\le\rho$; any unscaled `fsite_locInt` route must carry this $\rho$ into its amplitude.

**PROVED (scaled inclusion), OPEN in Lean.** If $s(g)<q\le\rho$, $\beta\ge\max(1,\rho)$ and $\rho>0$, then $\beta>0$, $s(g/\beta)=s(g)/\beta<q/\beta\le1$, and $s(g/\beta)\le q/\beta$. Thus `g/β ∈ l1BallEta … (q/β)`; taking $q=\rho$ gives the requested physical-ball inclusion, and taking $\rho=q=1$ recovers `sourceSlice_mem_restricted`. The first inequality is strict even when $q/\beta=1$. Use this lemma also for `physInclScaled_image_subset`. **PROVED:** `l1BallEta η` (`InteractionHatEta.lean:80`) and `physSΛEta` (`SharpAssemblyEta.lean:836`) are *normalized* carriers of $g/\beta$ and need no change. They continue to require $q/\beta\le1$; renaming them as physical $B_\rho$ would be false.

## T2. Typed-use census and upgrade contract

**PROVED (rg census).** A declaration scan of the 26 listed source/chart files in `Fluctuation/` and `Inhabited/`, searching declaration signatures or definition bodies for `l1Ball`, `physVq`, `physV `, `physSΛ `, or `q ≤ 1`, finds **75 carrier hits**. The table gives one row per hit and states whether the pin lies in its type or definition. It also adds the hidden `physFibre` and `sourceExponentFamily_fromTower` dependencies and the SRCBALL-cited scalar/observable declarations with no literal hit. The same scan across all files in `Fluctuation/` and `Inhabited/` has 140 candidate hits, including earlier unscaled interaction and separate mark/determinant branches; this is the bounded direct-terms-to-output source/chart slice, not a claim that all 140 need a new theorem. File codes: F = `Fluctuation/`, I = `Inhabited/`; all names below exist at the audited commit. In the table, `P` means physical $B_1$ or `physV`, `Q` means $q\le1$, `N` means normalized $B_1$ (`l1BallEta`), `W` means witness output; `Pρ` replaces physical carriers by the displayed $\rho$ carriers, `Qρ` changes the binder to $0<q\le\rho$, and `N=` keeps normalized types unchanged. Sizes are estimated new Lean lines, not verified line counts. **OPEN:** every proposed $\rho$-version.

| Landed declaration (file:line) | Type pin | Proof pin | $\rho$-version statement | Size |
|---|---|---|---|---|
| F `InteractionFPart.lean:128:l1Ball` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `InteractionFPart.lean:130:norm_le_of_mem_l1Ball` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `InteractionFPart.lean:156:fsite_locInt` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `InteractionFPart.lean:214:fsites_locInt` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `PhysicalTerms.lean:52:physSΛ` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `PhysicalTerms.lean:335:physicalHatTerms` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `PhysicalTerms.lean:380:physical_hatTerms` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `PhysicalTerms.lean:427:physicalDirectTerms_of_sharpLoc` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `InteractionHatEta.lean:80:l1BallEta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `InteractionHatEta.lean:83:l1BallEta_subset` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `InteractionHatEta.lean:86:l1BallEta_one` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `InteractionHatEta.lean:127:hat_fparts_bound_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `InteractionHatEta.lean:226:hat_mparts_bound_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `InteractionHatEta.lean:358:interaction_expansion_hat_bound_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:67:hat_fparts_bound_dm_dir_eta_ray` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:179:hat_fparts_bound_dm_dir_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:227:hat_mparts_bound_dm_dir_eta_ray` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:378:hat_mparts_bound_dm_dir_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:434:interaction_expansion_hat_bound_dm_dir_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:625:interaction_expansion_hat_dm_core_dir_eta` | N | normalized-coordinate bound | N=; no new theorem | 0 |
| F `SharpAssemblyEta.lean:841:physSΛEta_subset` | N, P | inclusion in physical B1 | N=; add inclusion in Bρ when η≤ρ | 10–20 |
| F `ParamActivitySubspace.lean:252:physV` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:256:isOpen_physV` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:263:physIncl_image_physV` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:274:physical_directTermsFamilyOn` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:294:paramMarkFamily_physical_subspace` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:313:physical_labelActFamilyOn_local` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:336:physical_paramMarked_analytic_local_bound` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `ParamActivitySubspace.lean:528:physical_paramMarkFamily_exists` | P | physical membership/coordinate bound | Pρ; retain B1 corollary | 15–100 |
| F `SourceFamilyRelative.lean:78:physVq` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:82:physVq_one` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:85:physVq_subset` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:88:isOpen_physVq` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:96:physInclScaled_image_subset` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:120:directTermsFamilyOn_scaled` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:156:sourceFamilyRelative_scale` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceFamilyRelative.lean:247:sourceFamilyRelative_instance` | P,Q | scaled image; raw datum membership | Pρ,Qρ; N= target | 15–100 |
| F `SourceSliceScaled.lean:60:sourceSlice_mem_restricted` | Q | q/β≤1 | Qρ; N= output | 15–30 |
| F `SourceSliceScaled.lean:77:sourceSlice_mem` | P | q/β≤1 | Qρ; N= output | 15–30 |
| F `SourceDirectTermsScale.lean:375:stepActivityBound_zeroClass_source_scaled` | Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| F `SourceDirectTermsScale.lean:436:sourceDirectTerms_scale` | Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| F `SourceAmpNonneg.lean:121:sourceFamilyRelative_scale_nonneg` | P,Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| F `SourceAmpNonneg.lean:351:sourceFamilyRelative_nonneg_instance` | P,Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| F `ObsRayActivity.lean:451:obsRayActivity_fromTower` | P | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `UniformChartRelative.lean:74:hatStepK_physV` | P | raw datum plus source norm<1 | raw datum in Vρ | 10–30 |
| I `SourceActivityScale.lean:87:stepActivityBound_zeroClass_source_scale_cutoff` | Q | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceActivityScale.lean:272:stepActivityBound_zeroClass_source_scale` | P | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceActivityScale.lean:309:sourceActivityC_scale` | P | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceActivityScale.lean:345:stepNonvanishingC_zeroClass_source_scale` | P | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceActivityScale.lean:363:stepActivityBound_zeroClass_source_scale_restricted` | Q | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceActivityScale.lean:390:sourceActivityC_scale_restricted` | Q | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceActivityScale.lean:430:sourceActivityC_scale_instance` | P | direct terms plus hDA smallness | Qρ/Pρ; CE+q CF | 20–100 |
| I `SourceAmpScale.lean:180:sourceAmp_doubled_hDA` | Q | absorbs q·CF using q≤1 | Qρ; threshold uses CE+ρ CF | 25–45 |
| I `SourceActivityFromTower.lean:305:sourceActivityC_scale_fromTower` | P | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `SourceDirectTermsFromTower.lean:102:sourceDirectTerms_scale_fromTower_ray` | Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `SourceDirectTermsFromTower.lean:232:sourceDirectTerms_scale_fromTower` | Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `SourceFamilyRelativeFromTower.lean:38:sourceFamilyRelative_scale_fromTower` | P,Q | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `SourceWitnessJoint.lean:44:sourceWitness_fromTower` | W,P | shared labels at q=1 | one shared witness on Bρ | 70–130 |
| I `SourceWitnessJoint.lean:422:sourceActivityC_scale_fromTower_of_witness` | W,P | shared labels at q=1 | one shared witness on Bρ | 70–130 |
| I `SourceWitnessJoint.lean:459:obsRayActivity_fromTower_of_witness` | W,P | shared labels at q=1 | one shared witness on Bρ | 70–130 |
| I `SourceExponentFamily.lean:67:physFibre_subset` | P | fibre uses V | fibreρ | 5–20 |
| I `ObsMarksFromTower.lean:258:obsMarks_zeroClass_family_of_ray` | P | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `ObsUnconditional.lean:35:sourceDirectTerms_scale_fromTower_ray_full` | Q | ray witness/activity at q=1 | Qρ/Pρ; bound at Bρ | 30–100 |
| I `ObsUnconditional.lean:215:obsMarks_zeroClass_family` | P | ray witness/activity at q=1 | Qρ/Pρ; bound at Bρ | 30–100 |
| I `ObsUnconditional.lean:279:thm31b_zeroClass_fromTower` | P | ray witness/activity at q=1 | Qρ/Pρ; bound at Bρ | 30–100 |
| I `ObsUnconditional.lean:301:thm31b_zeroClass_fromTower_small` | P | ray witness/activity at q=1 | Qρ/Pρ; bound at Bρ | 30–100 |
| I `Thm31bFromTower.lean:63:thm31b_zeroClass_fromTower_of_ray` | P | source slice/family or witness | Pρ,Qρ as applicable; N= target | 20–100 |
| I `StepPiecesJoint.lean:49:stepPieces_joint` | W,P,Q | aggregates source and chart clauses | Pρ,Qρ; keep other conjuncts | 80–150 |
| I `StepPiecesRenSol.lean:82:stepPieces_fromTowerRenSol` | W,P,Q | aggregates source and chart clauses | Pρ,Qρ; keep other conjuncts | 80–150 |
| I `ActivityFamilyAnalytic.lean:281:fst_zero_mem_physVq` | P,Q | zero-source lift and chart openness | Pρ,Qρ; zero family on Vρ | 30–120 |
| I `ActivityFamilyAnalytic.lean:290:physFibre_subset_physVq_one` | P,Q | zero-source lift and chart openness | Pρ,Qρ; zero family on Vρ | 30–120 |
| I `ActivityFamilyAnalytic.lean:357:activityFamilyAnalytic_fromTower` | P,Q | zero-source lift and chart openness | Pρ,Qρ; zero family on Vρ | 30–120 |
| I `ZeroSourceActivityCommon.lean:173:zeroSourceActivity_common_fromTower` | P,Q | zero-source lift and chart openness | Pρ,Qρ; zero family on Vρ | 30–120 |
| I `ChartDetJointFromTower.lean:54:scale_chart_det_joint_fromTower` | W,P,Q | aggregates source and chart clauses | Pρ,Qρ; keep other conjuncts | 80–150 |
| I `ChartDetJointFromTower.lean:215:stepPieces_fromTower` | W,P,Q | aggregates source and chart clauses | Pρ,Qρ; keep other conjuncts | 80–150 |

**OPEN (hidden dependencies and SRCBALL declarations).** The literal-type census omits the following, so they are separate rows:
| Landed declaration (file:line) | Type pin | Proof pin | $\rho$-version statement | Size |
|---|---|---|---|---|
| I `SourceExponentFamily.lean:63:physFibre` | alias P | definition uses `physV` | `physFibreRho`, old by $\rho=1$ | 5–15 |
| I `SourceExponentFamily.lean:124:sourceExponentFamily_fromTower` | fibre, $s(g)<1$ | calls direct terms at $q=1$; uses `physVq` | $s(g)<\rho$, fibreρ, $\eta=\rho/\beta$ | 80–140 |
| I `ObsUnconditional.lean:159:obsRay_hray_fromTower` | ray data | chooses $q=1$ direct terms | ray data at $q=\rho$ | 25–60 |
| I `SourceAmpScale.lean:86:sourceAmp_scale` | scalar $q$ | source factor linear in $q$ | already valid at $q=\rho$ | 0 |
| I `SourceAmpScale.lean:157:sourceAmp_scale_four` | scalar $q$ | linear source bound | already valid at $q=\rho$ | 0 |
| F `SourceSliceScaled.lean:90:sourceEta_scaled_identity` | scalar $q$ | algebraic identity | already valid at $q=\rho$ | 0 |
| F `InteractionHatEta.lean:90:prop33EpsEta` | normalized $\eta$ | source term linear in $\eta$ | already valid at $\eta=\rho/\beta$ | 0 |
| F `SharpAssemblyScaled.lean:57:prop33EpsEtaScaled` | normalized $\eta$ | scaled source term linear in $\eta$ | already valid at $\eta=\rho/\beta$ | 0 |
| F `StepComplexSource.lean:285:prop26C_zeroClass_of_activity` | activity input | algebraic step | same theorem; feed $B_\rho$ activity | 0 |
| F `StepComplexProp26.lean:491:prop26C_step` | regularity input | algebraic step | same theorem; feed $B_\rho$ input | 0 |

**REFUTED:** merely replace $q=1$ by $q=\rho$ in `physVq` or reuse `hatStepK_physV`: both still require the physical unit ball. **PROVED:** `sourceAmp_doubled_hDA` (I `SourceAmpScale.lean:180`) is a real numerical obstruction: its proof uses $q\le1$ to bound $qC_F$ by $C_F$. The generalized proof replaces its threshold argument $(C_E+C_F)/4$ by $(C_E+\rho C_F)/4$ for $q\le\rho$; `sourceAmp_scale` itself is valid for arbitrary nonnegative $q$.

## T3. Dependency order and build gates

All targets are **OPEN**; each means add a generalized theorem and reprove the landed statement as its $\rho=1$ case. Do not rename, weaken, or delete landed declarations. Compile the touched module and then the project tree after each target. Each proposed worker task is at most 300 new lines; split if implementation exceeds that bound.

1. **START NOW — carrier and slice (≤220 lines, Sonnet for the finite-sum algebra):** add `l1BallRho`, `physSΛRho`, `physVRho`, `physVqRho`, `physFibreRho`, their radius-one equalities, openness, $B_\rho$ convexity/star lemma and `sourceSlice_mem_restricted_rho`. Build the defining modules. Preserve normalized `l1BallEta` and `physSΛEta`.
2. **START NOW — scalar activity threshold (≤120 lines, Sonnet):** generalize `sourceAmp_doubled_hDA` to $q\le\rho$ and $(C_E+\rho C_F)/4$, then recover its old statement at $\rho=1$. It depends only on existing scalar lemmas and can proceed independently of target 1. Build `SourceAmpScale`.
3. **Direct terms (≤250 lines each, Sonnet):** generalized `stepActivityBound_zeroClass_source_scaled`, `sourceDirectTerms_scale`, then `sourceDirectTerms_scale_fromTower_ray`, `sourceDirectTerms_scale_fromTower`, and the full ray wrapper. Keep their `physSΛEta(q/β)` target; replace $q\le1$ by $q\le\rho$, require $\beta\ge\max(1,\rho)$. Build after each module.
4. **Relative chart (≤250 lines each):** upgrade `hatStepK_physV`, `physInclScaled_image_subset`, `directTermsFamilyOn_scaled`, `sourceFamilyRelative_scale` and nonnegative/tower wrappers to `physVqRho`; prove point membership with the new physical chart. Build after the base and tower layers. The legacy unscaled physical expansion and mark interfaces in the census are separate generalization targets only if a consumer actually needs unscaled $B_\rho$; any such target must retain its radius-one corollary.
5. **Activity and common labels (≤280 lines each):** re-run `stepActivityBound_zeroClass_source_scale_cutoff` and `sourceActivityC_scale_fromTower` with $q\le\rho$, scalar threshold from target 2, and one $\mathcal Y$ for the whole physical ball. Upgrade restricted and nonvanishing wrappers, then `sourceExponentFamily_fromTower` on `physFibreRho` and `sourceWitness_fromTower`; preserve the shared `val,\mathcal Y,T_t` quantifier order. Build after each file. Use more than one worker target if any output grows past 300 lines.
6. **Observable and analytic outputs (≤280 lines each):** generalize `obsRay_hray_fromTower`, `obsMarks_zeroClass_family_of_ray`, `obsMarks_zeroClass_family`, `thm31b_zeroClass_fromTower_of_ray` and unconditional/small wrappers; then `activityFamilyAnalytic_fromTower` and `zeroSourceActivity_common_fromTower` with open `physVqRho` and `physVRho`. The zero-source lift uses $0\in B_\rho$ and source independence, not a unit-source restriction. Build each module.
7. **Joint outputs (≤280 lines each):** generalize `scale_chart_det_joint_fromTower`, `stepPieces_fromTower`, `stepPieces_joint`, `stepPieces_fromTowerRenSol`. Review every `physV` conjunct: mark/determinant functions that ignore $g$ can be pulled back through the datum projection; source-bearing clauses need target 6. Build after each theorem/module. Specialize $\rho=1$ for the old statements.
8. **Coordinate-to-general-field assembly (separate later campaign):** at $\rho=\sqrt N$ prove coordinate analytic identity on $B_\rho$, coefficient bound on the closed $B_{\rho/2}$ with $c_9/\sqrt N$, then rotate using `Model/SymmetryPartition.lean:partitionFunction_rot`, `sum_norm_rotSource_le`, `rotFamily_analytic`, and `norm_rotFamily_le`. **OPEN:** current tower is fixed at $d=L=3,N=2$; this target does not by itself prove frozen Root-F for general $d,N$.

## T4. Radius pins outside the source lane

| Input | Consequence at $\rho=\sqrt N$ |
|---|---|
| Old $\mathcal M^{(j)}$ terms, P4 H7 (printed p. 679) | **PROVED:** H7 prints $\|g\|_{\ell^1}<1$ for the inherited analytic observable; P7 printed p. 533, (4.15)–(4.17), invokes H7. **OPEN:** an H7 successor on $B_{\sqrt N}$, including uniform bounds and nonvanishing where needed. A larger $\beta_0$ alone cannot enlarge an assumed analytic domain; recursively produced old terms must be carried on the new radius. |
| Final integral and large-field correction, P7 (4.15)–(4.17), P9 printed p. 516 (4.4)–(4.7) | **OPEN:** prove complex analyticity, zero-free logarithm and the final polymer coefficient bounds on $B_{\sqrt N}$, with the $c_9/\sqrt N$ budget. These cited formulas do not state the larger source domain. Source dependence of the large-field regulator may add constants or a new estimate; it cannot be certified here as only a $\beta_0$ change. |
| Root-C derivatives at $g=0$, `Frozen/Roots/LowTemperatureCorrelations.lean` | **PROVED (local calculus):** any positive analytic radius contains an open neighbourhood of $0$, so taking first and second source derivatives at $0$ imposes no extra *domain* enlargement once the $B_{\sqrt N}$ partition identity exists. Quantitative Cauchy constants may depend on chosen interior radius, $N$, and the rotated norm; the full correlation asymptotics and limiting arguments remain **OPEN**. |

**OPEN closeout condition.** Only after targets 1–8 and the inherited/final source-domain estimates hold with one fixed $\rho=\sqrt N$ can the frozen general-field unit ball follow by rotation. The radius-one tower and all existing Lean statements remain available throughout.
