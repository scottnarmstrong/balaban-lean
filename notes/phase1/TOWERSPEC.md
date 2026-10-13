# TOWERSPEC — shared numerical tower and scale interface

**Scope.** This is a Lean design, not a landed declaration. Paths below are relative to the read-only `Balaban/` source tree. **PROVED** refers only to named declarations there; **OPEN** refers to the proposed shared interfaces. The physical specialization is $d=L=3,N=2$, `zeroClass`, and the central unit datum. It does not assert a general class or chart-wide activity theorem.

## 1. Exact landed tower

**PROVED** (`Inhabited/StepActivityDirectPhysicalRates.lean:55`): `tower_core_rates (N : ℕ) {κ0 κdec : ℝ} (hκ0 : aEnt 3 3 + 1 ≤ κ0) (hκdec : 3 * κ0 + c1 3 3 + 5 ≤ κdec)` returns `∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ)` and, in this exact order, the following conjunction:

```lean
4 ≤ m₁ ∧ 0 < t ∧
Nonempty (FlCore N (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁))
  1 nuW c BG κ t (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t) ∧
0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ ∧
1 ≤ (κ / 2 - 1) / 2 ∧
Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
c7 3 3 N BG κ ≤ thm73C3 3 3 N ∧
cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
decDomMargin 3 3 N BG κ (xiC1 3 * t) < δc ∧
K4 3 3 N BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
2 * t ≤ deltaStar 3 3 N ∧
cK2 3 3 N * (2 * t) < bgC0 3 3 N / 2 ∧
cK2 3 3 N * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
cK2' 3 3 N (famConst 3 3 BG₂ κ) * t ≤
  c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 N ∧
aEnt 3 3 + 1 ≤ κ0 ∧
0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
0 ≤ famConst 3 3 BG₂ κ
```

**PROVED consumer map.** `SourceActivityScale.stepActivityBound_zeroClass_source_scale_cutoff`, `DetStepScale.stepActivityBound_detExpansionLocC_scale`, `ScaleActivityFinal.stepActivityBound_zeroClass_direct_physical_scale_cutoff`, `SourceDirectTermsScale.sourceDirectTerms_scale`, `SourceAmpNonneg.sourceFamilyRelative_scale_nonneg`, and `ExpSourceChart.expSourceChart_scale` each obtain the 8 witnesses and 21 fields, then use `hMX` to derive `hbig : cstarX 3 3 ≤ (3 : ℝ)^m₁`, `scale_C_items` for one threshold/ray, `flCore_level_transfer` for the scale pair, and `LocalCover.levelLocalCover` after `3 ∣ N₁`. Source/direct consumers also use `famConst ≥ 0`, `rho4 ≥ 0`, the `cK2'` bound, the five small-radius bounds, `κ0`, `κdec`, and the rate relation. `DetOutputTermsWitness.detExpansionLocC_scale_of_tower` uses precisely `h4,ht,hC,hMX,hdm,hα,hsmX,hz`; its public `detExpansionLocC_scale` independently calls the tower. `UniformChartMargins.scale_markedDisc_mem_flBallLC` uses `hC,hMX,hdm,hα,hsmX`; `scale_chart_det_joint` wraps the determinant theorem. `StepRegWitness.exists_witness_params` independently supplies `δ,δ'` and their six radius inequalities; its own `m₁` is discarded. The physical callers set `κ0=aEnt 3 3+1`, `κdec=100*(κ0+c1 3 3+10)`, `κ'=3/2*κdec+κ0+1` (`StepRatesDirect.stepRates_direct_witness`).

## 2. Proposed fixed record (**OPEN**)

Use `N=2` in this record: the `δ'` bounds of `exists_witness_params` are specialized to 2. Place it in the `Balaban.Inhabited` namespace with the same opens as `StepActivityDirectPhysicalRates`; `κmin` is an input, not a rate chosen after the scale. The following is the field-by-field declaration, with shortened numerals only where definitionally equal to the landed form.

```lean
structure StepTower (κmin : ℝ) where
  κ0 κdec κ' : ℝ
  κ0_eq : κ0 = aEnt 3 3 + 1
  κdec_eq : κdec = 100 * (κ0 + c1 3 3 + 10)
  κ'_eq : κ' = 3 / 2 * κdec + κ0 + 1
  m₁ : ℕ
  c BG κ t c₂ BG₂ δc δ δ' : ℝ
  m₁_four : 4 ≤ m₁
  t_pos : 0 < t
  core : Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁))
    1 nuW c BG κ t (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t)
  κ0_nonneg : 0 ≤ κ0
  κdec_lower : 3 * κ0 + 3 ≤ κdec
  κ_lower : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ
  κ_one : 1 ≤ (κ / 2 - 1) / 2
  κ_log : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) *
    (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2
  c7_cap : c7 3 3 2 BG κ ≤ thm73C3 3 3 2
  large_block : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁
  dom_margin : decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc
  coer_margin : K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2
  δc_small : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4
  t_cap : 2 * t ≤ deltaStar 3 3 2
  bg0_cap : cK2 3 3 2 * (2 * t) < bgC0 3 3 2 / 2
  cK2_cap : cK2 3 3 2 * t ≤
    c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)
  cK2'_cap : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t ≤
    c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)
  bg1_cap : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * t))) +
    5 * (2 * t) ≤ bgC1 3 3 2
  κ0_ent : aEnt 3 3 + 1 ≤ κ0
  rate_rel : 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1
  fam_nonneg : 0 ≤ famConst 3 3 BG₂ κ
  κmin_le : κmin ≤ κ
  δ_pos : 0 < δ
  δ_small : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4
  δ'_pos : 0 < δ'
  δ'_cap : δ' ≤ thm73C3 3 3 2 / 2
  δ'_step : bgK1 3 3 2 * δ' ≤ δ / 4
  δ'_coer : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4
  block_base : cstarX 3 3 ≤ (3 : ℝ) ^ m₁
  xi_small : xiC1 3 * t ≤ 1
  rho_nonneg : 0 ≤ rho4 3 3 2 BG κ
  det_z : ((detDeg 3 3 + 1 : ℕ) : ℝ)^2 * (2 / Real.exp κ) < 1
  det_rate : κ' ≤ (κ - Real.log 2 -
    2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18
```

**Proof sources.** The 21 numerical/core fields from `m₁_four` through `fam_nonneg` are `tower_core_rates 2`; the three equations use the displayed physical choices, `κmin_le` uses the strengthened construction below. The six `δ,δ'` fields are from `exists_witness_params (fun _ => 0)`, ignoring its block-size witness. `block_base` follows `large_block`, `κ_lower`, positivity of `cstarX` and `Real.one_le_exp`; `xi_small` follows `core.c7le`, `c7_le_bgC1`, `bgC1_le_small`; `rho_nonneg` follows `core.hS.fam`, `famConst_ge_one`, `c6'_pos`. `det_z` follows `detDeg_three_rate` at `κ≥57`; `det_rate` uses `log_detDeg_three_lt`, `κ_lower`, the physical rate equations and arithmetic, as in `DetOutputTermsWitness.detExpansionLocC_scale`. These derived proofs belong next to the record and run once.

**OPEN theorem signatures:** `tower_core_rates_at_least (N : ℕ) {κ0 κdec κmin : ℝ} (hκ0 : aEnt 3 3 + 1 ≤ κ0) (hκdec : 3*κ0+c1 3 3+5 ≤ κdec)` has exactly the existential witnesses and 21-conjunct conclusion of §1, followed by `∧ κmin ≤ κ`; `exists_stepTower (κmin : ℝ) : Nonempty (StepTower κmin)` specializes it to `N=2` and adds the separate radii. Re-run `tower_core_rates`, replacing its assignment `κ := 4116*κdec + 40000 + 1/thm73C3 3 3 N` by `κ := max (4116*κdec + 40000 + 1/thm73C3 3 3 N) κmin`. Its `hκ1,hκ2,hκ3` still follow by `le_max_left`; `κmin_le` is `le_max_right`. Re-choose `m₁` by `exists_m₁` for `max(max(c exp(N0κ),c₂ exp(N0κ)),cstarX exp(N0κ))`; then `flCore_level_eventually` and the seven eventual inequalities select a new `t>0`, and `δc=1/[2(smallConstX(κ)+1)]`. No upper bound on κ is used. The determinant rate argument uses only the resulting lower bound; a large `κmin` can be the hull threshold of `CONSTS.md`.

## 3. Proposed per-scale package (**OPEN**)

Keep `hk`, `[NeZero N₁]`, `h3N`, `hN`, mass and cutoff proofs as theorem arguments, not record fields with unresolved instances. For each `T : StepTower κmin`, `hA : 0<A₁`, `p`, first obtain `∃ βray≥2` from landed `LevelRayTower.scale_C_items T.m₁_four T.block_base T.κ T.t_pos T.δ_pos T.δ_small T.δ'_pos T.δ'_cap T.δ'_step T.δ'_coer`; choose any later common `β₀≥βray`. Set `S := hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ` and `b := β*3^k`. Define `StepScaleData T k hk N₁ ν β p₁` with fields `S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)`, `S_eq : S = hatStepK ...`, `core : FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t`, `xi : XiCData S.G' (compWeight 3 1) ν (k+1) 1 T.t S.D'`, `ray : S.RayData (2*p₁)`, `cψ_pos : 0<lvCpsi T.κ T.t b`, `r_pos : 0<lvR T.κ T.t b p₁`, `fl_radius :` the strict square-root/covariance inequality from `scale_C_items`, `ray_margin : (4+lvR T.κ T.t b p₁)*p₁<lvCpsi T.κ T.t b`, `p_lt : p₁<2*p₁`, and `covers :` the exact conjunction returned by `LocalCover.levelLocalCover` with `Hm=lvLow`, `Gp=lvTop`, `m₀=1`. The `covers` field should be implemented via a named abbreviation for that full dependent conjunction; it must retain both block and source-site covers. The `S_eq` transport is needed because `FlCore` and covers are stated on `lvTop/lvLow`, while `xi/ray` refer to `S`.

**OPEN theorem signature:** `theorem StepTower.scale (T : StepTower κmin) (hA : 0 < A₁) (p : ℕ) : ∃ βray : ℝ, 2 ≤ βray ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ → ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2*(k+1)) ≤ 1 → ∀ β : ℝ, βray ≤ β → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β*3^k) → Nonempty (StepScaleData T k hk N₁ ν β p₁)`. Proof: `flCore_level_transfer`, `hatStepK_xiCData`, `scale_C_items`, and `levelLocalCover`; the activity consumers separately require `0<ν` for `hBh_of_xi`.

## 4. From-tower endpoints (**OPEN**)

Each signature begins `(T : StepTower κmin) (hA : 0 < A₁) (p : ℕ)` and has `∃ β₀ : ℝ, 2 ≤ β₀ ∧ ...` **after** `T`; later binders are `k hk N₁ [NeZero N₁] h3N hN ν hνpos hν β hβ p₁ hp₁ hpLog` in the landed order. `D : StepScaleData T k hk N₁ ν β p₁` is passed after those binders. A common maximum of endpoint thresholds is permitted; no endpoint chooses a new tower.

The `∀ ... (D : StepScaleData ...)` used in items 1–5 abbreviates exactly `∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ → ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2*(k+1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β*3^k) → ∀ D : StepScaleData T k hk N₁ ν β p₁, ...`. Thus each endpoint's conclusion below is a predicate at this fully bound scale; `b` means `β*3^k`. The determinant endpoint alone may weaken `0<ν` to `0≤ν` and omit the β/cutoff threshold, as `detExpansionLocC_scale_of_tower` does.

1. `sourceActivityC_scale_fromTower`: `∃ β₀ CE CF, 2≤β₀ ∧ 0<CE ∧ 0<CF ∧ ∀ ... (D : StepScaleData ...), ∀ g ∈ l1Ball ..., ∃ BR : StepActivityBound D.S (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g, ∃ BC : StepActivityBoundC D.S (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g`, with `BR.κH=BC.κH=2*T.κdec-1`, `BR.κ0=BC.κ0=T.κ0`, `BR.κ'=BC.κ'=T.κ'`, `BR.Kc=BC.Kc=2*(K0 3 3 T.κ0+1)`, `BR.εH=BC.εH≤CE*(log b)^(3*p)/sqrt b+CF*(log b)^p/sqrt b`. Add a **common label witness before `∀ g`**: a fixed finite `Lb`, `Lab : CubeLabels ... Lb`, and `BS : BlockSplit D.S 1`, with both records' `Lb=Lb`, `HEq Lab` fields, and `BS=BS` for every source. This fixed-label clause is a further **OPEN** strengthening; the current public theorem does not imply it. Extract the common `𝒴,T` of `sourceDirectTerms_scale` once, then factor the source assembler and `stepActivityBoundC_of_activityBound`; the latter preserves all numerical fields and labels by `I.toC_of_ae`. Re-run, not a wrapper around `sourceActivityC_scale`.
2. `detExpansionLocC_scale_fromTower`: for all scale data and roots `z`, return `E : DetExpansionLocC D.S 1 z T.t ((T.κ-log 2-2*log(detDeg 3 3+1))/18) (27*covBLogMax 3 3 T.κ/(1-zκ))`, with `zκ=((detDeg 3 3+1)^2)*2/exp T.κ`, and the exact `E.term D₀ U = ∑ y ∈ D.S.blockU z, detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D₀ y U`; also expose `T.det_z,T.det_rate`. **Thin wrapper:** `detExpansionLocC_scale_of_tower` with `Classical.choice T.core` and the seven named tower premises; its conclusion already supplies `xi` and this `E`.
3. `scale_chart_det_joint_fromTower`: for all scale data, return the landed `hatStepK_chartBall` radius `r>0` and both raw/source-ball inclusions, the four bounds of `scale_markedDisc_margin` (in particular `81*T.t/128<T.t`), the zero-source activity at rate `2*T.κdec-1`, `D.xi`, and the preceding determinant `E`. **Re-run** `scale_chart_det_joint`'s short final proof from the from-tower activity/determinant endpoints; invoking its public existential would lose `T`. The marked-disc lemma must likewise be factored using `D.core` rather than its separate tower call.
4. `sourceFamilyRelative_scale_fromTower`: the full conclusion of landed `sourceFamilyRelative_scale_nonneg`, with its existential `val,𝒴,Tterms,I,hF`, analytic family on `physVq × ball 0 2`, source-point identity, and nonnegative amplitude estimate, substituting `T.m₁,T.t,T.δ,T.BG,T.BG₂,T.κ` and `T.κ0`. The fixed `𝒴,Tterms` are quantified before sources. **Re-run** its proof after replacing the initial tower/ray block with `T,D`; its public existential cannot fix those values.
5. `expSourceChart_scale_fromTower`: the full landed `expSourceChart_scale` conclusion for each `D.S`, with `Jr : D.S.JointRep T.t (2*p₁)`, the displayed `val` using `T.BG₂,T.κ`, and its `W2` source difference identity for all `g,x,τ`. **Re-run** after removing its tower and `scale_C_items` calls; use `D.core,D.xi,D.ray` and radius fields. No activity or label conclusion is implied by this endpoint.

**Order and risks.** First land `tower_core_rates_at_least` (about 180 lines), then `StepTower` and `exists_stepTower` (under 250 lines), then the scale package (under 250 lines), then one endpoint per file (each under 300 lines; factor source leaf if needed). Check `NeZero N₁` is introduced before forming `StepScaleData` or `hatStepK`; avoid an instance field in the record. Normalize `S_eq` by `subst S` or `change` at dependent `XiCData`, `RayData`, and covers. `δ` comes from the separate radius lemma; do not identify it with `δc`. The common-label field is stronger than any public theorem and may require a separate `LabelAct` family constructor. If the dependent record causes elaboration trouble, replace it with a single theorem returning a nested `∃ S, S=hatStepK ... ∧ FlCore ... ∧ XiCData ... ∧ Nonempty (S.RayData ...) ∧ covers ...`, and retain the same fixed `T` in every endpoint. **OPEN:** this design has not been compiled; **PROVED:** the cited source ingredients and their restricted conclusions are landed.
