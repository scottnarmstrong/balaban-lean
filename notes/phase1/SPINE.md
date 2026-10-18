# SPINE — Root-F from a finite list of source-level inputs (W1094; corrected by W1098 after SPINE-AUDIT, SPINE-AUDIT-2)

**PROVED.** `Balaban.RootFSpine.rootF_of_spine` (`Balaban/Spine/RootF.lean`) has as conclusion the body of the frozen
`Balaban.logPartition_multiscale`, copied verbatim. Its hypotheses are the seven `def … : Prop` of `Spine/RootFInputs.lean`, at
constants that the provider chooses as functions of `(κ, c₉)`: `δ`, `Ty` (typing), `P6` (Def-6), `C7`, `PB` (budget), `cs₀`
(non-running operator constants), `M1, c` (geometry), `rH, ϱ`. No `sorry`; axioms `propext, Classical.choice, Quot.sound`. The
scratch check `type_of% (logPartition_multiscale d N hd hN)` accepts the conclusion (definitional match; the elaborated
`NormedSpace ℂ` instance path differs, as for the landed copy `RootFStatement`). The provider closes Root-F by
`exact rootF_of_spine d N hd hN δ hδ Ty P6 C7 PB cs₀ M1 c rH ϱ hA1 hA3 hA4 hA4t hA4f hA6 hA7`.

**Proved inside (not inputs):** the order of the constants (`δ`; `L = Ty.L`, `M = Ty.M`, with `2 ≤ L`, `1 ≤ M` from the prefix,
`prefix_ranges`; one `β₀` = max of the inputs' thresholds and 2; `kf = k̂_f`, `exists_isHorizon`, `IsHorizon.scale`); `k₀ ≤ k̂_f`
(`kZero_le_of_isHorizon`); A5, the flow (`class_flow`, the transfer, `frozen_flow`, `IntegralIsZ.step`); the stop by the
horizon (`stop_of_flatClassAt`, now from (I.2) in the class); A8 and the conversion (`ratio_eq_exp`, `activityTerm` of the
increments, `rootFClauses_of_activities`); the transport to Root-F's tori (`sideOf_eq`). A0 is not used: the classes carry a
general unit field and the source ball of radius 1, so the inputs are stated at every unit `h`.

## Carriers

`RepClassAt … k ρ ν_k` is `IsRep2` (LFR Def. II.6.2 v2, containing `IsSFFamily2` as (D2) and the small-field half of (D8) as
`coherent : D8SF`) at the a priori setting `𝒮[d, T, β, a]` (`λ̂_j`, forced by `Coh.lam_eq`), `k₀ = kZero d L β ν`, horizon
`K = k̂_f + 1`; `cs, P, geo` existential with their outer fields fixed. Added clauses (W1098): `β_0 = β`, `ν_0 = ν`, `ν_k`
exposed, `RunningHypTo` ((I.2) of (A-IV.2) at the scales `≤ k`, `ε = 1/20`, `Spine/Coherence.lean`) and `LFCoherent F`, the
large-field half of (D8) as LFR D-IV.9 states it (`Spine/Coherence.lean`). For two tori `n_K = nK₁, nK₂` and a centre `c`,
`LFCoherent` asks agreement at corresponding arguments. Arguments correspond when their `ℤ^d` representatives nearest to `c`
(`liftNear`) agree inside the box `4|y − c| < min(ℓ₁, ℓ₂)`. Three kinds of datum are compared:
* the step kernels and boundary factors `K_j, b_j` of corresponding localized histories (records and `V` in the box);
* the kept sets `I''`, kept kernels and exponents `κ_j`;
* the boundary terms `ℬ^{(k)}(X, 𝔸)`, when `X`, the records of `𝔸` on `X` and the localized histories of the components meeting
  `X` correspond (the two-torus form of (D7)'s locality).

`FlatClassAt` is the same with `IsRepFlat2` (horizon `k̂ = k̂_f`). `IntegralIsZ`: `∫ρ_k dψ_k = c Z(g)`, `c > 0` per torus;
`IntegralStep`: `∫ρ' = c∫ρ`; Lebesgue integrals over the `k`-block fields. `ObservableActivities … J kf p` (W1098: increments only)
asks, on every admissible torus:
* `p_j(X;g) = p_j(X;0)` unless `1 ≤ j ≤ J` and `IsPolymer d ℓ (ML^j) X`;
* analyticity on the unit ball and locality in `g|_X`;
* `‖p_j(X;g) − p_j(X;0)‖ ≤ (c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(ML^j)^d}`;
* two-torus agreement of the increments on the quarter box.

## Corrections after the audits

* **D1 (W1096).** `LFCoherent` added to both class predicates. A3, A4 and the transfer now produce it; A6 consumes it. A6's
  agreement conclusion is LFR Thm IV.5.3 item 7 from (D8) of both halves plus the locality of the last integral, so A6 is no
  longer stronger than the source. The A11 docstring of `RootFInputs.lean` is corrected. No Def-7 field was needed.
* **D2, F4.** `F.sf.β 0 = β` and `RunningHypTo` added. The step inputs and A6 now carry (A-IV.2) in their hypotheses.
* **D5, F1–F3.** `PrefixInput` asks:
  * every constant condition a class member needs: `L ≥ 3`; `1 < a < 3/2` and `9/10 ≤ a(1−L⁻²)²` (`a_k → a(1−L⁻²)`, `a_ge`
    at every scale); `M = c M₁`, `c ≥ 14`, `M₁ ≥ 1` (`Geo`); `M = L^{m₀+m₁}`; `P6` admissible; `c₉^{flow} > 0` (strict (H.7));
    `B₀ > 0` (strict (D7)); `C_b ≥ 0` ((S0));
  * the ties to Root-F (LFR D-IV.7, rows 1, 5, 10): `δ ≤ γ − α₁`, `κ_flow ≥ 3^{d+1}L^{2d+1}(κ+1)`,
    `c₉^{flow} ≤ (c₉/2)e^{−κ_flow}`.

  The c₈ clause is dropped, since the stop now uses (I.2). This list is what the class fields require that I could identify
  (Coh, Geo, D7, D9, IsSFFamily2, StepData); a condition hidden deeper (e.g. in `OpConsts.aw`) is not excluded.
* **D6.** `ObservableActivities` constrains only the increments. The conversion uses `p(g) − p(0)`.
* **D3, D4, D7, F5, F6.** These are recorded below (items 4, 5, non-vacuity, coverage).

## The inputs (statement; source; landed pieces; open sub-inputs; size, rough)

1. **`PrefixInput` (A1)**: as above; source LFR §I.1.4. Landed: `exists_rootParams_consts_all` (`L = 7`, `c₈ = 1`, admissible
   `Consts`). Open: the provider defines the full prefix (rows 0–15, `λ_*` with (Λ0)–(Λ32)); the other inputs are true only for
   that choice. The chain's `L = 3` and A1's `L = 7` are not reconciled; LFR §I.1.1's `a = (1−L⁻²)⁻¹` violates the window at
   `L = 3` (W1096 D5: correct LFR). ~800.
   **Satisfiable (W1105, `Spine/Prefix.lean`, `prefixInput_exists`):** for every `L ≥ 3` and `0 < δ < 1/2`, with `m₀ = 1`, `m₁ = 3`,
   `M = c = L⁴`, `M₁ = 1`, `a = 5/4`, `γ = (1+2δ)/4`, `α₁ = (1−2δ)/4`, `κ_flow = 3^{d+1}L^{2d+1}(κ+1)`, `c₉^{flow} = (c₉/2)e^{−κ_flow}`.
   The clauses are jointly satisfiable at every `L ≥ 3`, so `L = 3` (the landed class chain) is possible and `exists_rootParams`'
   `L = 7` is not forced by `PrefixInput`; it is forced only by its own extra clauses (`6 ≤ L`, `Odd L`, tower `5 < q L^{m₀}…`).
   `exists_rootParams`' `δ = (d−2)/8` exceeds `1/2` for `d ≥ 6` (impossible with `γ < 1/2`); use `exists_rootParams_consts_all`' `δ`.
2. **`BaseStepInput` (A3, LF-6)**: `ρ₁ ∈ ℛ₁` (`k₀ ≥ 1`) or `ℛ♭₁` (`k₀ = 0`), `∫ρ₁ = cZ(g)`, with `β_0 = β`, `ν_0 = ν`, (I.2) and
   (D8). Source: LFR Thm II.7.10 (a), (b), (d); P4 (2.42)–(2.54). Landed (`LargeField/Base/`, general `d, L`):
   `baseFirst_partition_integral`, `baseFirstCut_integral_of_posDef`, `baseCovX_bound`, `baseSectorDatum_inDomainR_c7`,
   `baseActivity_LabelAct`, `partitionFunction_eq_sum_kf0Sector`. Open: carrier R7 (`BaseSmallFieldInput`); BASEPLAN OUT-1;
   blockers 1, 2; nothing produces `IsRep2 … 1`, `IsRepFlat2 … 1` or `IntegralIsZ`. ~5000.
3. **`ClassStepInput` (A4, LF-3 + LF-4)**: `1 ≤ k < k₀`, `ℛ_k → ℛ_{k+1}`, `∫ρ' = c∫ρ`; hypothesis and conclusion carry (A-IV.2)
   and (D8). Source: LFR Thm IV.1.1 (h), Thm III.10.8. One input, because LF-4's "rep produced by LF-3" and the small-field step's
   output relation have no Lean statement. Landed:
   * small-field, `3,3,2`, over `StepClass`/`SFTermClauses`: `e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot`,
     `e0CoeffFamily_class_fromTower_of_irrelBounds_X`, `classOldDec_expansion_cover_birth_run`, `newLabels_castInputs_of_localFamily`;
   * large-field: `lf4R_removed` (named `hrip`, `hCR0`, `hwin`, `hτ`), `hrip_of_counter`, `hcount_of_flow`,
     `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel`, `removedKernel_kerBound_of_hid_action`,
     `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du`, `keptKernel_one/two/three_kerBound`.

   Open:
   * the chain's premises (hchart type, per-label irrelevant bounds `Bτ`, analyticity along the path);
   * R8, the counterterms;
   * blockers 2–4 (R4, kept bounds, vacuum bound);
   * the bridge chain ⇒ `IsSFFamily2` at `k+1` (with `β_0 = β`, one `c₈`, `RTermsH4`), `StepTowerG`;
   * the large-field (D8) of the constructed data.

   Watch (W1096): if the scheme-A step needs the SF→LF interface (`IsRep2WithInterface`) of its input, this input is stronger
   than that step; `D2SF2` asks every Def-6 torus `N₁ ≥ 1`. ~10000.
   **Split (W1102):** `classStepInput_of_parts` (`Spine/ClassStep.lean`) from `SFStepInput`, `RInput`, `FlowRateInput`; see
   "ClassStepInput sub-inputs" below.
4. **`TransferInput` (A4, Lemma IV.2.1)**: `ℛ_{k₀} ⊂ ℛ♭_{k₀}`, same `ρ`, `ν_{k₀}`. Landed: `IsRep2.toFlat` (with `D2SF2.toFlat2`,
   `D9Coeff.toFlat`), valid only for torus horizons `K ≤ k₀ + 1`. Named sub-inputs (D3, F6):
   * (a) LF-2 (ii) for a representation with the counter history truncated at `top = k + 1`, independent of `K`. The landed
     `Rep.lf2Hyp` needs `K ≤ top`, and `Rep.budgetFlat_of_LF2` / `frozen_budget` need `K ≤ k̂`;
   * (b) `IsRep2.toFlat` for every `K` from (a);
   * (c) `BudgetSetup` from the class: its `run : RunningHyp` asks (I.2) at every scale, while the class gives `RunningHypTo` up
     to `k`. A truncated `RunningHyp`, or `P.beta` pinned beyond `k`, is needed;
   * (d) `S.Good` and (H-λ) `hH1`, `hH2` (LFR Lemma IV.3.3 (c); window `(d−2)/2 < θ ≤ (d−2) log L`) as a lemma of the prefix.

   **Proved (W1106):** (a), (b) by W1099 (`IsRep2.toFlat_of_all_horizons`); (c) `BudgetSetupTo S P c` (Lemma B and Lemma II.1.2 for
   (I.2) up to the scale `c`, `Analytic/Constants.lean`, `Budget/LemmaB.lean`; `BudgetSetup` is its every-cutoff case, `BudgetSetup.toTo`);
   (d) `exists_good_lamHat`, `hLam_window` (needs `c_H ≥ d(d-2) log L / 2`, `log β ≥ 2d`), `analyticK_at`, `kZero_le_horizon`
   (`Spine/TransferAnalysis.lean`); `flatClassAt_of_repClassAt` (one class member) and `transferInput_of_prefix`
   (`Spine/Transfer.lean`): `PrefixInput` and `TransferTyping` give `TransferInput`.
   **Finding:** `PrefixInput` does not constrain `Ty κ c₉` beyond `L, M`, nor `PB κ c₉`; `S.Good` (needs `Typing.Ok`), (H-λ) (needs
   `c_H ≥ d(d-2) log L / 2`, `θ₋ ≤ (d-2) log L ≤ θ₊`) and the budget setup (`H₀ > 0`, `c₁ ≥ 0`, `L ≤ M`, `c_v ≥ M^d (H₀+c₁+3)`) need them.
   They are collected in `TransferTyping` (inhabited, `transferTyping_exists`). The orchestrator may add these clauses to `PrefixInput`.
5. **`FrozenStepInput` (A4, LF-5)**: `max(k₀,1) ≤ k < k̂_f`, `ν_k ≤ 7/8 L⁻²`, `ℛ♭_k → ℛ♭_{k+1}`, `∫ρ' = c∫ρ`; LFR Thm IV.2.2,
   switch FLUCTUATION Lemma 2.9. Landed: the small-field pieces of item 3. `Rep.budgetFlat_of_LF2` does not apply at
   `K = k̂_f + 1` (D3). Named sub-inputs: 4 (a), (c), (d) for (H6♭) at `k + 1`; the step theorem; blocker 2; R5′; blocker 6.
   ~3000 beyond item 3.
6. **`LastIntegralInput` (A6, LF-8 (a), observable form)**: at the stopping scale, `∫ρ = exp(E + ⟨g,h⟩ + Σ_{j≤k+1} Σ_X p_j)`,
   `ObservableActivities … (k+1)`. For `j ≤ k`, `p_j = Σ_{x∈X}⟨g(x), ℳ^{(j)}(x,X;h,h,g)⟩`; for `j = k+1`, `ℳ_0`, `ℛ_n` and `𝒫` are
   regrouped by `Ȳ`. Source: LFR Thm IV.4.1, Def. IV.5.2, Thm IV.5.3 items 2, 3, 5, 7. True for constants satisfying `PrefixInput`
   (the ties). Landed (`Green/`, general `3 ≤ d'`, `3 ≤ L`, `N`):
   * `cutoffInteraction_final_class_polydisc_local`, `norm_coef_cutoff_class_le_levels_of_large`, `final_tail_gas_bound`,
     `FinalLarge*`;
   * A9: `rootRate_of_sizeJ`, `rootBound_of_perTerm`, `betaK_inv_sq_le`, `mObs_rootF_of_obsBound`;
   * A10: `sitesOf_isPolymer`, `rootF_sites_of_cellClause`, `obsCubeFamily_sourceBall_fromTowerG_rho`.

   **A11 coverage (D7):** `finalCoef_close_quarterBox_weighted`, `fibre_hcoef_of_quarterBox_weighted` and
   `resum_lastScale_rootF_weighted_of_block_large` give closeness between tori, not the exact agreement asked (W1088).
   `e0CoeffFamily_value_fromTowerG_core_twoTorus` is exact only for the core family (W1090). Exact agreement needs a complete
   localization of the last integral (P6 p. 3), with the wrapped remainder put on winding polymers (SPINE-AUDIT-2 (d)).

   Open: blocker 5 (identification of `F`, gap L4, linked gas P7 (4.11), joins, `det-ratio × J`); cells-to-sites reindexing
   (ROOTFFAM 4); the rate/amplitude conversion (item 5); blocker 7 (item 24, W1090, `hFclose`, TORUSCOH2). Nothing is over
   `IsRepFlat2`. ~6000.
7. **`KfZeroInput` (A7, LF-8 (b))**: `7/8 L⁻² < ν ≤ 1`, `Z(g) = exp(E_ℓ + ⟨g,h⟩ + Σ_X p_1)`, `ObservableActivities … 1`; LFR
   Prop. IV.4.3 / LF-BASE-KF0; no paper. Landed: shape of the hypothesis of `rootF_kf0_partial_of_oneScaleInput`; `KF0AllGoodGas`,
   `KF0AllPlusGas`, `Green/KF0CovarianceAtoms`. Open: reversed-spin sector (blocker 1), `CompleteHeavyLocality`. ~2500.

## ClassStepInput sub-inputs (W1102)

**PROVED** (`Balaban/Spine/ClassStep.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`):
```
theorem classStepInput_of_parts (hSF : SFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hR : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ) (hQ : FlowRateInput T P6) :
    ClassStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ
```
It follows LFR Thm IV.3.2: LF-3 at `k`, then (I.2) at `k + 1`, then LF-4 at the scale `k + 1 ≤ k₀`; the threshold is the larger one.
New carrier: `PreClassAt … kf k r ρ νk`, the pre-`R` class `ℛ^pre_k`. It is `RepClassAt` with `IsRepPre2` in place of `IsRep2` and
(I.2) up to the scale `r`. Proved inside:
* the coefficient step `runningHypTo_succ_of_coeffBounds`: (H.6) at `k + 1` (`CoeffBounds`, the flow `ξ`), `β_0 = β`, `ν_0 = ν`,
  (I.2) up to `k` and `c₈ q ≤ ε(1 − q)` give (I.2) up to `k + 1`; positivity uses `|ξ| ≤ 1/4` and `ν_{k+1} > 0`, the bounds use
  `Flow.norm_gammaSeq_le`. `PreClassAt.succ` applies it to `IsRepPre2.sfData`;
* the integral assembly `IntegralStep.trans_eq`.

Rule 10: `preClassAt_witness` (`wIsRepPre2`; `d = L = 3`, `N = 2`, `kf = 0`, `k = 1`, `r ≤ 1`) and `flowRateInput_of_lower` (any
admissible constants with `L ≥ 2`, after lowering `c₈`). `SFStepInput` and `RInput` need the exemption of the seven inputs: their
truth is the open work.

**Coherence is not a separate sub-input.** (D8) at `k + 1` (`LFCoherent`, D-IV.9) is a property of the representation that the
step builds (LF-3 (h); proof of Thm III.10.8, (D8)). No landed operator says which representation that is. A statement "(D8) at
`k + 1` from (D8) at `k`" over all members of `ℛ^pre_{k+1}` would be false: a family of densities on different tori need not be
coherent (audit D1). So `LFCoherent` is a conjunct of the outputs of `SFStepInput` and `RInput`, and (D8) at the input scale is
in their hypotheses. Splitting it into "old data inherited" plus "new data coherent" needs a core of `LFCoherent`; that means
editing `Spine/Coherence.lean`, which this task may not do.

**A landed definition must change (ruling R6, approved 2026-10-17, not yet applied to Def-7):** `Balaban.LargeField.Def7v2.sfDom`
(`Def7v2Class.lean:59`). It is read by `D2SF2.sfClass` and `SFFlat2.torus`, hence by `IsRep2`, `IsRepPre2` and `IsRepFlat2`.
At every level `j` it is the current-mass domain `xiFieldDom (aIdeal L k (a k)) (sfBgMass k) (P6.eps)`, equal to `completeXiDom`.
The output of `SFStepInput` must give the inherited levels `j ≤ k` the clauses of `IsSFFamily2` at `k + 1`. That needs
`Ξ^c_j(a_{k+1}, μ_{k+1}, ε_j) ⊆ Ξ^c_j(a_k, μ_k, ε_j)`, which is false at admissible constants (`astra/SFFAM.md` §3.2). R6
replaces it by the birth-mass family `birthXiDom P6 ⟨k₀, sf.ν⟩ sf.a` (`Def6v2Birth.lean:31`). Until then `SFStepInput` (and
`ClassStepInput`, `FrozenStepInput`) have no source argument for the inherited levels. `Spine/ClassStep.lean` does not read the
domain, so its proofs survive the change.

1. **`SFStepInput` (LF-3; LFR Thm IV.1.1 (a)–(e), (h); P5 Thm 1, P6 Thm 1; P4 Thm 1 for the small-field data).** For
   `1 ≤ k < k₀`, `ρ ∈ RepClassAt k` (with (I.2) up to `k`, (D8)) gives `ρ' ∈ PreClassAt (k+1) k`: `IsRepPre2` at `k + 1`,
   `β_0 = β`, `ν_0 = ν`, (I.2) up to `k`, `LFCoherent`, and `IntegralStep ρ ρ'`.
   * Landed, small-field half. On one Def-6 torus, `d = L = 3`, `N = 2`, carrier `StepClass`/`SFTermClauses`, `StepTower`:
     * the chain `e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot` (`3 ∣ N₁`, `5 < N₁`, `3^{m₀} ∣ N₁`,
       `m₀ ≥ 7`, `ν 3^{2(k+1)} ≤ 1`, one `β₀`, `t_k = λε_{k+1}`, collar 327). It gives the new-level coefficients `e` with
       analyticity on `physV`, locality, bound, support, `Σ e = E0locJ = densE0` and per-label spin covariance;
     * class activities and marks: `e0CoeffFamily_class_fromTower_of_irrelBounds_X`, `classE1_M1_of_family`,
       `classMarks_M2_of_family`;
     * old terms on birth domains: `classOldDec_expansion_cover_birth_run`;
     * new level: `newLabels_stepChart_of_rootFamily_thick`, `localClass_newLevel_of_expansion_cast`,
       `newLabels_castInputs_of_localFamily`, `tower_E0_closure_agree`, `newLabels_hsum_closure`, `not_newLevel_cover_and_room`;
     * core family on two tori: `e0CoeffFamily_value_fromTowerG_core_twoTorus`, `coreE0_unique`;
     * counterterms: `renLocC1_scale_of_tower`, `renLoc_fields_scale_of_tower_at`.

     General `d, L, N`:
     * inherited levels (R6): `oldTorusEquiv`, `liftOldTerms`, `liftOldTermsFam`, `sfTermClauses_splice_birth`,
       `torusIndep_splice`, `gsStrong_splice`, `renorm_splice_birth`, all on `birthXiDom`;
     * local sets (W1084): `zeroSourceTerm_localB_hat`, `detActivityBg_cross`, `flCore_castG_localB`;
     * the step `ξ^{(k)}`: `rg_step_infty`; the Gaussian identity behind `∫ T ρ = ∫ ρ`: `integral_blockSpin`.
   * Landed, large-field half (general `Setting`):
     * quiet steps: `quietKernel`, `quietStepData'`;
     * the vacuum term (R5′): `stepVacuumTerm`, `stepVacuumVolume`;
     * (H6′)^pre by LF-2 (i): `Rep.budgetPre_of_LF2`. Its `BudgetSetup.run` asks (I.2) at every scale (item 4 (c));
     * a non-quiet kernel exists only at `k = 0` (R7 `Kphys`).
   * Open:
     * (a) R8: the generic `decMarkG`, `decMarkCorr(Term)`, `e1MarkGParamG`, `DetExpansionLocC`, `DirectTerms`, `physParam`/`physV`
       with an explicit background generating set (not started). With them, (A1)–(A5) of `newLabels_castInputs_of_localFamily`:
       the new level's terms on the local charts of `𝔹_{k+1}(Y⁺(T′))`.
     * (b) The castG gap. W1084's local pieces live on the literal `localB` at `minSep` on the step torus, while the cast theorem
       reads `castG hc (localB …)` on `(N₁′, m₁ + 4)`. Missing: castG versions of `LocalPairDepth`, `LocalPairLevelInner`,
       `localHatLift_eq_hatPsiF_localB`, `localB_collar_margin`, `localB_tauExt_*`.
     * (c) The inherited terms on two tori. For a general class the chain's `e` is not a core family (W1090). `D8SF.M_eq` at
       `k + 1` and `hFclose` need two-torus agreement of the old-term pieces `AC`, `G₁`.
     * (d) The chain's named premises:
       * the per-label bounds `hEbd`/`Bτ` of `irrelTorus` at the composed step data (P1 (3.128)), with the decay
         `CI E₀ 3^{-(k-j)(3+α₃)}`;
       * `hchart` (the composed data lie in the term domain);
       * the analyticity of the old densities along the path;
       * the smallness `hεnum`.
     * (e) The counterterm assembly `D_E = ℰ''₀(θ_ξ) + oldE + C₁ + C₂ −` vacuum (P4 (4.14)–(4.22)). Missing: `oldE` of a general
       class, the physical `locC2`/`locDφ`, `renE0_fibre`. The observable terms `D_M`, `T_M` (P4 (4.18), Prop. 4.2) exist for the
       zero class only.
     * (f) Generality. The chain is at `StepTower`, but `StepTowerG d L N` is needed at the prefix's `L` (A1 picks `L = 7`).
       It also needs `3 ∣ N₁`, `5 < N₁`, `3^{m₀} ∣ N₁`, while `D2SF2` asks every `N₁ ≥ 1`.
     * (g) Large field:
       * the non-quiet kernels P5 (2.47)·P6 (3.2) for `k ≥ 1` with local backgrounds, (S1)–(S5) (Lemmas IV.1.3, IV.1.4, IV.1.6);
       * `ℬ^{(k+1)}` with `B_st` (Lemma IV.1.5; blocker 3 for old terms across a new hole);
       * `D1PreForm2` for `ρ' = z^{N|T|}(Tρ)(z·)`, the operator bound `D5Bound`;
       * `D6Pre` with (I.2) only up to `k + 1`, and `∫ ρ' = ∫ ρ` for the Def-7 densities;
       * blocker 2 (R2 landed, leaf 5 open).
     * (h) (D8) of the new step kernels and of `ℬ^{(k+1)}`. Even the quiet kernel has no cross-torus theorem for `bgLocPiece`
       (W1103).
     * (i) The SF→LF interface watch item (item 3).
   * **The bridge, exactly (not landed; no theorem concludes `IsSFFamily2 … (k+1)` or `D2SF2 … (k+1)` except the witnesses).**
     Proposed: `d2SF2_succ_of_chain`, the small-field half of `SFStepInput`. Let `(F, ρ)` be a member of `RepClassAt k`,
     `1 ≤ k < k₀`. For every Def-6 torus `N₂ ≥ 1` of scale `k + 1`:
     * let `C(N₂)` be the `StepClass` with `m₀ = P6.m₀`, terms `liftOldTerms (F.sf.Tm (L N₂))` (levels `≤ k`, along
       `oldTorusEquiv`) and vacuum constant `F.sf.E (L N₂)`;
     * let `S(N₂)` be the step setting of `F.sf` at scale `k` (`a₁ = a_k`, mass `sfBgMass k`, `β_k`, `p₁`, `δ_k`);
     * let `ξ = ξ^{(k)}` be the solution of the conditions (H.5) at `k + 1` (`rg_step_infty`).

     Define `sf' : SFData d L m₁ (k+1) N ϱ`:
     * at `j ≤ k`, `β′, ν′, a′, z′, E′` equal those of `F.sf`;
     * `β′_{k+1} = β_k L^{d−2}/(1+ξ₃)`, `ν′_{k+1} = ν_k L²(1+ξ₃)/(1+ξ₂)`, `a′_{k+1} = compWeight L a (k+1)`;
     * `Tm′(N₂)` is the splice of `liftOldTerms (F.sf.Tm (L N₂))` (levels `≤ k`) with the new level `k + 1`. The new level is
       the chain's labels on `C(N₂)`, recomputed on `𝔹_{k+1}(Y⁺(T′))` and regrouped on `𝒟^{(m₀)}_{k+1}`, plus `D_E` and the
       observable terms `D_M`;
     * `Rt′` holds the `ℛ^{(k+1)}_n` of P5 Props. 3.1–3.4.

     Conclusion:
     * `IsSFFamily2 P6 ⟨k₀, sf'.ν⟩ sf'.β sf'.a (sfDom P6 k₀ sf') sf'.Tm ρsf' sf'.E` at `k + 1`, with `sfDom` replaced by
       `birthXiDom` per R6, and `ρsf'(N₂) = z^{N|T|}·T^{(k)} ρsf(L N₂)` (the density clause of `IsSF2`). This includes
       `CoeffBounds` at `k + 1` with the same `c₈`;
     * `RTermsH4` with `preFac`, `D8SF P6.m₀ sf'`, `D9Coeff P6 k₀ sf'`, and the `Coh` tables (`sf'.a j = compWeight L a j`).

     Landed parts: the inherited half (`sfTermClauses_splice_birth`, `torusIndep_splice`, `gsStrong_splice`,
     `renorm_splice_birth`), the new-level clauses from label inputs (`localClass_newLevel_of_expansion_cast`), and the label
     inputs from (A1)–(A5) (`newLabels_castInputs_of_localFamily`). The large-field half of `SFStepInput` then assembles
     `IsRepPre2 … (k+1)` around `sf'`.
2. **`RInput` (LF-4; LFR Thm III.10.8, Lemma III.8.4; P7 Thm 2, (1.3)–(1.7); ruling R4).** For `1 ≤ k ≤ k₀`,
   `ρ ∈ PreClassAt k k` (with (I.2) up to `k`, (D8)) gives `ρ' ∈ RepClassAt k` with the same `ν_k` and `∫ ρ' = ∫ ρ`. General
   `Setting`.
   * Landed:
     * `lf4R_removed` (named `hrip`, `hCR0`, `hwin`, `hτ`; W968 refuted `hτ` as the form of R's output, replaced by (3.10″)),
       `hrip_of_counter`, `hcount_of_flow`, `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel`;
     * the window: `removedKernel_kerBound_of_hid_action`, `removedKernel_kerBound_of_hid_action_cl` (`hnamedCU`),
       `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du`, `genSet_stability_core`;
     * kept outcomes: `keptKernel_one_kerBound`, `keptKernel_two_kerBound`, `keptKernel_three_kerBound`;
     * R4: `RopC`, `rhoSigma`, `Rop_integral_coupling`, `gasDecor_eq`, `gasR4Decor_eq`, `gasR4DecorOp_eq`,
       `r4Fresh_aggregate_of_localization`, `r4HeavyActivity_bound`, `gasOp_pe_hole`;
     * the normalization: `R_normalization_of_indep`, `R_normalization_sum_of_indep`, `R_normalizationPhysical`
       (named integrability hypotheses);
     * the class: `isRep2_of_isRepPre2_of_fields`, `isRep2_of_isRepPre2_of_enum_of_pin`, `sfData_of_remainder_added`,
       `d7Post_bound_of_avoid_of_gas`, `isComplete_succ_of_enum`.
   * Open:
     * (a) `hnamedC.1` of the window chain: the conclusion of `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` under its ~60
       numeric side conditions (P7 Step 1). Also the P7 Q-part of `hnamedC.2` at the physical collar (COLLAR-FIX 1.2).
     * (b) (3.10″) for the actual removed operators, and (H-op): hole closure, the two PE inequalities, the product measure.
     * (c) `ℬ′` (P7 (3.22)–(3.25)): the physical extension that `r4Fresh` needs.
     * (d) The seven obligations of `isRep2_of_isRepPre2_of_fields`: OPEN-R-HISTORY-ENUM, OPEN-R-TOP-PIN, OPEN-R-D7-PHYSICAL,
       `form`, `opBound`, `budget` (LF-2's R-step, (Rg) from LF-4R), OPEN-R-RM-H4. Its premise `F'.sf = F.sf` fails once
       `ℛ''_m` is added, so the assembly must be restated for `sf' = sf + ℛ''`.
     * (e) The kept bounds `ϰ₄`, `ϰ₅` (`hquot`), and the vacuum bound (W965 normalization).
     * (f) (D8): `LFCoherent` of the output, and `D8SF.R_eq` of `ℛ''_m`, which comes from the input `LFCoherent` (audit D1).
3. **`FlowRateInput` (the coefficient step; LFR Thm IV.3.2 (d), prefix row 10).** `c₈ q ≤ (1 − q)/20` with `q = L^{−2γ}` for
   every `κ, c₉`. (H.6) at `k + 1` is part of the output of `SFStepInput`, and (I.2) at `k + 1` is proved from it. The landed
   `exists_rootParams_consts_all` (`c₈ = 1`, `L = 7`, `γ < 1/2`) violates it, since then `q > 1/7`. `flowRateInput_of_lower`
   lowers `c₈`; the flow bound then costs `β ≥ c_ξ/c₈` (LF-7 (d)).

## LastIntegralInput sub-inputs (W1108)

**PROVED** (`Balaban/Spine/LastIntegral.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`):
```
theorem lastIntegralInput_of_parts (hB : InheritedBoundInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ)
    (hA : InheritedAgreeInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hS : FinalSmallFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ)
    (hL : FinalLargeFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ) :
    LastIntegralInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ
```
It follows LFR Thm IV.4.1 with Def. IV.5.2 and Thm IV.5.3. For a member `ρ` of `ℛ♭_k` at the stopping scale with a
representation `F`, the activities are `p = q + 1_{j=k+1}(a + b)`; `E` is the vacuum term of A6-3; the threshold is the largest of
the four. The three families:
* `q = inhObs F.sf P6.m₀ h` (a definition). For `1 ≤ j ≤ k` and `X ∈ 𝒟_j` (`IsPolyDom`),
  `q_j(X; g) = Σ_{x∈X} ⟨g(x), ℳ^{(j)}(x, X; h, h, g)⟩`, and `0` otherwise. These are the (H.7) terms of the class at the
  constant configuration (LFR Def. IV.5.2, first item; P7 (4.17)).
  They are read on the Def-6 torus `N₁ = ℓ/(L^{m₁}L^k)`, which is the torus `sfIdx` of `RepFam.ctx` (`sideDiv_eq_sfIdx`).
* `a`: the scale-`(k+1)` activities of the small-field part. That part is `Ξ^sf = sfIntegral F hM6 hkK vc h nK g :=
  ∫ sfFactor2 (F.ctx hM6 hkK nK) vc univ ψ h g dψ`, the integral of the small-field factor of (D1) on the whole torus, i.e. the term
  of P7 (4.1) with no large-field region.
* `b`: the scale-`(k+1)` activities of the large-field part `∫ρ/Ξ^sf`.

Proved inside:
* the locality of `q` in `g|_X`, from `localM` on every Def-6 torus (`inhObs_actLocal`, through `SFFlat2.torus`);
* `inhObs_of_lt` (`q = 0` above `k`) and `inhObs_zero` (`q = 0` at `g = 0`);
* the amplitude budget: `q` is at most `c₉/2` at `j ≤ k`, and `a`, `b` at most `c₉/4` each at `j = k + 1`
  (`ActBoundAt.add`, `ActBoundAt.add_actAt_succ`);
* the exponential identity (`sum_actAdd_actAt`).

Pieces of `Spine/RootFInputs.lean` (one copy each; the two definitions built from them are definitionally the old ones):
* `FlatRep … hM6 hkK R geo cs P F St vc ρ νk`, the body of `FlatClassAt` for given witnesses; `FlatClassAt` is now
  `∃ hM6 hkK R geo cs P F St vc, FlatRep …`, so the sub-inputs can read `F`;
* `ActSupportAt`, `ActAnalyticAt`, `ActLocalAt`, `ActBoundAt` (the clauses on one torus `𝕋_ℓ`) and `ActAgree`;
  `ObservableActivities` is now `(∀ admissible ℓ, ActSupportAt ∧ ActAnalyticAt ∧ ActLocalAt ∧ ActBoundAt) ∧ ActAgree`.
  The literal conjunction of five tori-quantified clauses would not be definitionally the old body (the `∀ ℓ` would be split),
  so the four torus clauses are stated on one torus.
The lemmas `.add`, `.mono`, `.actAt` of these clauses are in `Spine/LastIntegral.lean`. Rule 10: the clause predicates are inhabited
by `observableActivities_zero` and `FlatRep` by `flatClassAt_witness` (the same unused configuration `kf = 0`). The four sub-inputs
need the exemption of the seven inputs, as `SFStepInput` and `RInput` do (ledger, 2026-10-18). Their hypothesis is `FlatRep` at
`K = k̂_f + 1`, whose non-vacuity at used configurations is item D4. All four are stated at general `d, N` and general constants.

**A6-1 and A6-2 need no source input** beyond the class, its (D8) and the ties of `PrefixInput`: they are bounded proof tasks (sketches
below). A6-3 and A6-4 are the last integral proper (blocker 5).

1. **`InheritedBoundInput` (A6-1, the conversion of the observable terms; LFR Thm IV.5.3 items 2, 4, 5 for `j ≤ k_f`; P4 (H.7)).**
   On every admissible torus, `ActSupportAt … k`, `ActAnalyticAt` and `ActBoundAt … c₉ … k` of `inhObs F.sf P6.m₀ h`.
   * Landed (general `d, L, N, m₀, m₁`):
     * the class clauses `SFTermClauses.boundM` and `.analyticM` (on `sfDom`, with `Def6.l1 g < 1`), on every Def-6 torus
       (`IsSF2.terms`, `SFFlat2.torus`);
     * `G1_card` (`|X| ≤ c1 d L · cellSide^d (1 + d_j(X))`, general `m₀`, `L^{m₀} ∣ N₁`);
     * `rootRate_of_sizeJ`, `rootRate_of_dExt` and `sitesOf_isPolymer` (`m₀ = 1`);
     * `prefixInput_exists`; the tower's analogue `mObs_rootF_of_obsBound`.
   * Open:
     * (a) the constant configuration `(constFld h, constFld h)` lies in `sfDom`. Since R6 (W1107) this is `birthXiDom`:
       `XiDom (Tm.gs j X) (aIdeal L k (a k)) (physMass L j ν_j) j ε_j`. It needs `XiAt` of the constant real datum,
       `InUnionDomainC` and `XiCBounds` with zero complex parts;
     * (b) `IsPolyDom m₀ j` ⇒ `IsPolymer d ℓ (M L^j)` for general `m₀`. The boxes of `ChosenOne` have side `L·M L^j` and are aligned
       at `cellSide = M L^j`, so this generalizes `sitesOf_isPolymer`;
     * (c) the arithmetic:
       * `|Σ_i g_i ℳ_i| ≤ (Σ_i |g_i|) vn ℳ`, and Root-F's ball lies in `{Def6.l1 < 1}`;
       * `(L^j)^{-((d-2)/2+γ-α₁)} ≤ L^{-j((d-2)/2+δ)}` from `δ ≤ γ - α₁`;
       * `c1 d L = (3(2L-1))^d ≤ 3^{d+1}L^{2d+1}`;
       * `c₉^{flow} e^{-κ_flow d_j(X)} ≤ (c₉/2) e^{-κ|X|/(ML^j)^d}`, from `G1_card` and `c₉^{flow} ≤ (c₉/2)e^{-κ_flow}`.

     Then A6-1 becomes a theorem with `PrefixInput` as a premise. ~300–500 lines.
     W1111 (`Spine/InheritedBound.lean`): (a), (b), (c) proved; `inheritedBoundInput_of_massCap` needs `3 ≤ d`, `bgR0 d L ≤ ϱ` and `InheritedMassCap`
     (the `BgHyp` mass cap `ν_j L^{2(k-j)} ≤ 1` at `k = k̂_f`, j < k: (I.2) and `ν_k ≤ 1` give only `e^{1/10}`; a bound `ν_k ≤ 9/10` in `D9Flat` would close it).
2. **`InheritedAgreeInput` (A6-2, exact agreement of the inherited terms; LFR Thm IV.5.3 item 7 for `j ≤ k_f`; P4 (H.4); (D8)).**
   `ActAgree` of `inhObs F.sf P6.m₀ h`. It follows from `D8SF.M_eq`, a clause (`coherent`) of `IsRepFlat2`.
   * Landed:
     * `D8SF.M_eq`;
     * the transport lemmas `Ypoly_eq_image`, `image_unlift_Ypoly`, `Ypoly_boxMap_of_small`, `fineLift_toTorus`, `toTorus_fineLift`,
       `mem_Ypoly_iff`;
     * here: `inhObs_zero` (the increment is the value) and `inhObs_local`.
   * Open:
     * (a) for `A` in the common quarter box, the preimage of the image of `A` is `Ypoly j X'` with `NonWind` on both Def-6 tori, and
       `IsPolyDom` holds on one torus iff it holds on the other (the `ChosenOne` boxes and `Nbr` paths do not wind);
     * (b) on the polymer, `pullFld j g = g ∘ valMinAbs` (the block-centred lift is the centred representative in the quarter box),
       and `pullFld j (const h) = constFld h`;
     * (c) the reindexing of `Σ_{x∈X}` by `A`.

     ~400–700 lines.
   * The exactness itself comes from the flow: (D8SF) at the stopping scale is produced by `ClassStepInput` and `FrozenStepInput`
     (item 3 (c) of `SFStepInput`: the inherited terms on two tori). W1089 (`e0CoeffFamily_value_fromTowerG_core_twoTorus`) is exact
     for the core family only. W1088 shows that closeness is not enough: the canonical-torus resummation
     `towerGapScale_resum_fromTowerG`
     needs bounded `K` (`K_bounded_of_can`). So the resummation of the gap scales into Root-F's polymer form belongs to the class
     steps; at `j ≤ k` A6 needs none, since `inhObs` is already per polymer on every torus.
3. **`FinalSmallFieldInput` (A6-3, the small-field last integral; P4 §6 (6.1)–(6.7), P7 (4.1)–(4.9) with `Z = ∅` and (4.15)–(4.17);
   LFR Thm IV.4.1; blocker 5, small-field half).** There are `a, E` with `ObservableActivities … κ (c₉/2) δ (k+1) kf a` and, on every
   torus of the family and the unit ball, `Ξ^sf = exp(E + ⟨g,h⟩ + Σ_{j≤k} Σ_X q_j + Σ_X a_{k+1})`.
   * Landed (`Green/`, general `3 ≤ d′`, `3 ≤ L`, `N` components):
     * the cut interaction: `cutoffInteraction_final_class_polydisc_local`, `cutoffInteraction_final_class_epsSeq`,
       `cutoffInteraction_final_comp`, `norm_coef_cutoff_class_le_levels_of_large`;
     * the class energy: `edensSum_analyticOnNhd_of_dom`, `norm_edensSum_le_of_dom`;
     * the expansion: `abstract_expansion_taggedCfin_final`, `localityAE_taggedCfinU`;
     * the datum: `finalSelectedDatum`, `finalSelectedDatum_inDomainR` (`k ≤ k₀` only);
     * the odd part of the linear term: `Green/FinalCrossTerm`; the Hessian: `Green/FinalHessian`;
     * amplitudes: `betaK_inv_sq_le`, `norm_kf0Deriv_le_two`;
     * on two tori, closeness only: `finalCoef_close_quarterBox_weighted`, `fibre_hcoef_of_quarterBox_weighted`,
       `resum_lastScale_rootF_weighted_of_block_large`; the limits `resum_lastScale_limit`, `rootF_hcoef_limit`.
   * Open:
     * (a) `sfIntegral` as the cut expansion. This needs:
       * the massive final variational problem (P7 p. 530, (4.3)–(4.6)) and the Gaussian change of variables at the physical point;
       * `det(U+E)/det(U)·J`;
       * `F_{k_f} = Σ_{j≤k} Edens` (FINALPHYS3 §8);
       * the block datum in the class chart with room (`hθ`);
     * (b) the source part `⟨g, φ̄_k⟩ − ⟨g, h⟩` together with the change of `ℳ^{(j)}(ψ^{(j)})` against `ℳ^{(j)}(h)`, as scale-`(k+1)`
       polymer terms (`ℳ^{(k+1)}_0`, the second-order remainder of the linear term; ROOTFFAM §3, row `⟨g, φ_k − h⟩`);
     * (c) the regrouping `Y ↦ Ȳ` and cells to fine sites (ROOTFFAM target 4);
     * (d) the exact two-torus agreement of `a`. It needs the complete localization of the last integral, with the winding remainder
       on winding polymers (SPINE-AUDIT-2 (d)); the landed results give closeness;
     * (e) the amplitude `c₉/4`: the `ℳ^{(k+1)}_0` part is `≤ (c₉/2)e^{−(κ+1)|X|_#}` by the ties, the rest is small in `β`.
4. **`FinalLargeFieldInput` (A6-4, the large-field part: final-scale representation and linked gas; P7 (4.9)–(4.14), P5 (3.18);
   LFR Lemma IV.4.2, (IV.4.1); blocker 5, item 18).** There is `b` with `ObservableActivities … κ (c₉/2) δ (k+1) kf b` and
   `∫ρ = Ξ^sf · exp(Σ_X b_{k+1})`.
   * Landed:
     * the linked gas (W990): `gasLinked_activity_bound`, `gasLinked_coverage_activity_bound`, `gasLinked_singleton_eq`;
     * the gas and the polymer expansion: `gas_eq`, `gas_activity_bound`, `pe_blockTorus`, `pe_PY_bound`, `pe_PY_analyticOnNhd`;
     * the tail: `integral_eq_sum_blocksSplit`, `norm_setIntegral_blocksSplit_le`, `final_tail_gas_bound`, `final_tail_gas_bound_nbhd`;
     * `Green/FinalLarge*`: `final_large_integral_eq_gasXi_of_factorization`, `linked_mayer_of_activated_local_terms`,
       `coverage_aggregate_coefficient_bound`, `retained_box_interaction_analytic_of_room`, `finalCrossing_eq_linked_triggers`,
       `no_single_linked_label_for_crossing`.
   * Open:
     * (a) the final-scale fluctuation representation: `𝕋'_{k+1}(Z', 𝔸')` (P7 (4.7)–(4.9), P5 (3.18)) is not defined in Lean
       (W1027), so there is no statement `∫ρ = Σ_{Z'} 𝕋'(Z')[…]` and no heavy weight `τ`;
     * (b) the completion (P7 (4.11)): the history of (D1) with no large-field region contributes `Ξ^sf`, and the other histories,
       divided by `Ξ^sf`, form the gas;
     * (c) the bounds:
       * (IV.4.1) for the weights (Lemma IV.4.2: `H^fin`, the frozen threshold);
       * the couplings `ℬ''`: L4, the cells meeting `Z` with the `Z`-dependent background (item 18 addendum);
       * the hypotheses of the linked gas;
     * (d) the end of the argument:
       * the exponentiation into `𝒫^{(k+1)}` (PE-L) and the regrouping;
       * the agreement (PE (f) with `LFCoherent` and `D8SF`);
       * the amplitude ((Λ32)).
   * The representation and the gas are one sub-input here (the brief expected two). Splitting them needs a landed `𝕋'_{k+1}`:
     the only statement that would separate them is "`∫ρ / Ξ^sf` is the linked gas of the weights `𝕋'(Z')`".

**Strength (watch).** A6-3 pins the inherited part to the class's (H.7) terms at the constant configuration. LastIntegralInput only
asks for some activities, so A6-3 is stronger than strictly needed. This is the form of the source (LFR (IV.4.2), Def. IV.5.2) and the
reading in LastIntegralInput's docstring. If the Lean class's `ℳ^{(j)}` at the constant configuration were not the source object
(open item (a) of A6-1), A6-3 would have to change with it.

## Non-vacuity (D4, F5) and rule 10

Inputs 3–6 are `∀ ρ ∈ class`. Input 2 asserts a member with `∫ρ₁ = cZ(g) ≠ 0`, inputs 3–5 propagate it, and the stop lemma
supplies the massive member that 6 needs; inputs 2 and 7 contain the physical `Z(g)`. Proved (`Spine/Witness.lean`):
* `repClassAt_witness`, `flatClassAt_witness` (`wIsRep2`, and `wIsRepFlat2_khat_zero` = `wIsRepFlat2` with `k̂ = 0`, since
  `W(2,0) = W(2,1) = 0`), at `d = L = 3`, `N = 2`, `kf = 0`, `K = k = 1`, `ν = 1/(27β)`, with all W1098 clauses (`β_0 = β`,
  `RunningHypTo` with `γ_j = δ_j = 1`, `wFam2_lfCoherent`: zero kernels and boundary terms);
* `observableActivities_zero`.

These configurations are not used: `IsHorizon 3 ν 0` fails there, and a used one has `kf ≥ 1`, `K ≥ 2`. Zero step data then fail
(`zeroStepData` needs `K ≤ 1`): an admissible history can have a quiet step `1 → 2`, whose kernel must be the quiet kernel
(`StepData.quiet`). A witness at `K ≥ 2` needs `quietStepData'` (with its side conditions `BgHyp`, `δ` bounds) from a
`QuietStepInput'` on every torus `n_K`; the landed `quietStepInput'_nonempty_pos` (`K = 2`, `k₀ = 0`) gives only `n_K = 1`, since
`quietRealized_iff_of_histImage` needs `n_j = 1` for `j ≥ K`. So non-vacuity at used configurations is open. **Ledger (rule 10):**
exempt the seven inputs (their non-emptiness is the open work) and `RepClassAt`/`FlatClassAt` at used configurations (`kf ≥ 1`).
**W1103 (K ≥ 2 witness; not built).** Beyond the quiet datum on every torus (the image history needs `n_j = 1` above `K`, so `real_euclid` needs `ImageHist` without `hsub`), the conjunct `LFCoherent` forces a cross-torus locality theorem for `quietKernel` (`StepData.quiet` pins `ker` to it at every quiet step 1 → 2, and such steps exist on every torus: `QuietHist`); its local background `bgLocPiece` is an `∃!` small solution on `Ω_1`, so the theorem is the D8 transport of that solution, and no landed lemma relates two tori (`HistCorr`, `OutCorr`, `CfgCorr` occur only in `Spine/Coherence.lean`).
Used configurations: `IsHorizon` with `ν L² ≤ 7/8` forces `kf ≥ 1`; with `β > 10` and `ν ≥ 1/81`, `kf = 1` has `k₀ = 0` (only `FlatClassAt`); `RepClassAt` needs `β ν ≤ 1`, hence `K = kf + 1` as large as `log_9(27 β)`, not 2.

**Plausibility.** The inputs follow LFR Thm IV.5.3 with the carriers above, and are true for the LFR prefix if the landed
definitions mean their sources. Carrier defects (e.g. CRotE, repaired by W1091) carry into items 2–6.

## Root-C

`rootC_of_rootFAndC1Star` needs `RootFAndC1Star`. Beyond the spine's inputs (whose prefix gives `L ≥ 3`), it adds one input:
`C1Star d N L M hN` at `(κ_*, 1)`. `C1Star` contains:
* the constants `a, γ₀, c_*, c_ξ, c', ρ₀, ρ₁, β_*`;
* per `β`: `J(ν) = k_f + 1`; (F1) the running `ξ` with bounds and continuity at `ν = 0` (LF-7 (d), (e)); (F2) `blockM = magJ + em`;
  (F3) the two-point decomposition and its limits.

Sources: LFR Thm IV.5.4, Prop. IV.4.4, OBS Thms 3.1, 5.2. `rootFAndC1Star_of_spine` and `rootC_of_spine` (`Spine/RootC.lean`)
prove them from the spine inputs and this hypothesis.
