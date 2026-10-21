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

  The rate clause `c₈ q ≤ (1 − q)/20` (`FlowRateAt`) is the last clause (W1116). This list is what the class fields require that I could identify
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
   than that step; `D2SF2` asks every Def-6 torus `N₁ ≥ 1`. ~10000. **Decided (W1136): the step does not need the interface**
   (section "LFStepInput sub-inputs"); it needs two other clauses of its input that the class does not carry (the vacuum tie of
   the step data, `z_j > 0`), asked by parts of A4-1h.
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
   (`Spine/Transfer.lean`).
   **Correction (W1112):** `S.Good` (needs `Typing.Ok`), (H-λ) (needs `c_H ≥ d(d-2) log L / 2`, `θ₋ ≤ (d-2) log L ≤ θ₊`) and the budget
   setup (`H₀ > 0`, `c₁ ≥ 0`, `L ≤ M`, `c_v ≥ M^d (H₀+c₁+3)`) are now clauses of `PrefixInput` (`TypingClauses`, with `R₀(d,L) ≤ ϱ`;
   `PrefixInput` takes `PB` and `ϱ`). `transferInput_of_prefix : PrefixInput → TransferInput`. `prefixInput_exists` produces them at every
   `d ≥ 3`, `L ≥ 3` (`prefixTyping`, `Typing.Ok` in general dimension). `TransferTyping` and `TransferWitness.lean` are removed.
   **Mass bound:** `FlatRep` (hence `FlatClassAt`) carries `ν_k ≤ 9/10`. Source: (D9♭) of LFR Thm IV.2.2, `ν_{k+1} = ν_k L² (1+ξ₃)/(1+ξ₂) ≤ 7/8 e^{c_ξ/β}`
   for `k < k_f`, which is `≤ 9/10` for `β ≥ β₀`; at the first frozen scale from the transfer, `ν_{k₀} ≤ e^{1/20}/β` (`nu_kZero_le`, proved from
   `β ν L^{k₀ d} ≤ 1`). `BaseStepInput` (`k₀ = 0`, `ν₁ = ν L² (1+ξ₃)/(1+ξ₂) ≤ 7/8 e^{c/β}`) and `FrozenStepInput` must produce it (cited input).
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
   Prop. IV.4.3 / LF-BASE-KF0; no paper. **PROVED by route FR** (W1149, `notes/phase1/KF0-FR.md`): `kfZeroInput_of_typing`
   (`Spine/KfZeroFRMain.lean`) from `1 ≤ d` and the typing condition `kf0FRs0 d N L κ ≤ M L` for every `κ, c₉ > 0` (a lower
   bound on the block side depending on `d, N, L, κ` only; compatible with `M = L^n`, `kf0FRs0_le_pow`). The sectors are never
   separated: finite-range whitening of the Gaussian chart, a block gas on the block torus, analyticity in `g`, Schwarz
   increments at source radius `c_G √β`. The split into A7-1/A7-2 (`kfZeroInput_of_parts`, below) is superseded.

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

**A landed definition changed (ruling R6, approved 2026-10-17; applied to Def-7 by W1107, `sfDom` is `birthXiDom` on main):** `Balaban.LargeField.Def7v2.sfDom`
(`Def7v2Class.lean:59`). It is read by `D2SF2.sfClass` and `SFFlat2.torus`, hence by `IsRep2`, `IsRepPre2` and `IsRepFlat2`.
At every level `j` it is the current-mass domain `xiFieldDom (aIdeal L k (a k)) (sfBgMass k) (P6.eps)`, equal to `completeXiDom`.
The output of `SFStepInput` must give the inherited levels `j ≤ k` the clauses of `IsSFFamily2` at `k + 1`. That needs
`Ξ^c_j(a_{k+1}, μ_{k+1}, ε_j) ⊆ Ξ^c_j(a_k, μ_k, ε_j)`, which is false at admissible constants (`astra/SFFAM.md` §3.2). R6
replaced it by the birth-mass family `birthXiDom P6 ⟨k₀, sf.ν⟩ sf.a` (`Def6v2Birth.lean:31`), which is `sfDom` now. The inherited
terms of `F.sf` lie in the birth domain of the output only if the output keeps `β_j, ν_j, a_j` for `j ≤ k` (the birth domains read them),
so the outputs of the step inputs tie them (`FrozenSFStepInput`, W1121; `SFStepInput`, W1115). `Spine/ClassStep.lean` does not read the
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
     * (a) R8: the generic objects are landed (W1129, W1138, W1139, `Tr.Reads` for `canon` W1141). (A1)–(A5) of
       `newLabels_castInputs_of_localFamily` (the new level's terms on the local charts of `𝔹_{k+1}(Y⁺(T′))`): route R-LOC, section
       "A4-1b (iii)" below (W1144): the chain returns its family as the formula `newLevelCoeffBg` (base layer proved), the recomputed family
       is the formula on `Gb(T′)`; the radius loss of the read datum is real but enters only identities.
     * (b) The castG gap: CLOSED by W1141 (cores for an arbitrary generating set in LocalPairIndexMatch/LevelInner/Depth/HatLift/Collar/LocalClassTau/LatTau/LocalGeneratorRestriction; `LocalPairCast.lean`). Was: W1084's local pieces live on the literal `localB` at `minSep` on the step torus, while the cast theorem
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
     * (i) The SF→LF interface watch item (item 3): decided by W1136, not needed (section "LFStepInput sub-inputs").
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
   lowers `c₈`; the flow bound then costs `β ≥ c_ξ/c₈` (LF-7 (d)). (W1116) The rate is now the last clause of `PrefixInput` (`FlowRateAt`), `prefixInput_exists` produces it (`c₈ = (1 − q)/(20 q)`), and `flowRateInput_of_prefix` gives `FlowRateInput`.

## SFStepInput sub-inputs (W1115)

**PROVED** (`Balaban/Spine/SFStep.lean`, with `Spine/StepDensity.lean` and `Spine/SFStepClauses.lean`; no `sorry`; axioms
`propext, Classical.choice, Quot.sound`):
```
theorem sfStepInput_of_parts (hd : 3 ≤ d) (hL : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → 3 ≤ (T κ c₉).L)
    (hϱ : ∀ κ, 0 < κ → ∀ c₉, 0 < c₉ → bgR0 d (T κ c₉).L ≤ ϱ κ c₉)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
    (ΦE : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ)
    (hI : SFInheritInput d N T P6 C7 cs₀ ϱ Φ) (hNw : SFNewLevelInput d N T P6 C7 cs₀ ϱ Φ)
    (hRn : SFRenormInput d N T P6 C7 cs₀ ϱ Φ) (hDn : SFDensityInput d N T P6 C7 cs₀ ϱ Φ)
    (hRt : SFRemainderInput d N T P6 C7 cs₀ ϱ Φ) (hCo : SFCoherenceInput d N T P6 C7 cs₀ ϱ Φ)
    (hV : SFVacuumInput d N T P6 C7 cs₀ ϱ Φ ΦE) (hLF : LFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ)
    (hInt : StepIntegrableInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    SFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ
```
and `sfStepInput_of_prefix` (the three typing facts from `PrefixInput`). General `d, N`, general constants, the class carriers.

**Changes to the spine's carriers (coordinator; W1119 finding; SUBSPINE-AUDIT defects 2, 5).**
* `RepClassAt := Nonempty RepRec` (`RootFInputs.lean`): the body with its witnesses as fields, as `PreClassAt := Nonempty PreRec`
  (W1118). Every proof that used the anonymous-constructor form still works (`flatClassAt_of_repClassAt`, `rootF_of_spine`,
  `rInput_of_parts`); `rootF_of_spine`'s conclusion is unchanged.
* The scale-indexed **vacuum flow**: `VacuumFlowTo C E β r := ∀ j ≤ r, |E_j| ≤ C (log β_j + 1)`; `RepRec` and `PreRec` gain the fields
  `Ev : ℕ → ℝ`, `vac : VacuumFlowTo cs₀.Cb Ev F.sf.β k` (the constant is `C_b` of (S0), which LFR Thm IV.1.1 (f) defines from the vacuum
  constants among others; a separate constant is a one-word change). `SFData.E` stays the torus-indexed constant of `E_k |T^{(k)}_1|`.
  `PreClassAt.succ` and `rInput_of_parts` carry the flow (one line in `RStep.lean`: `rec.Ev, rec.vac` in the output record);
  `flatClassAt_of_repClassAt` drops it (`FlatClassAt` is unchanged). Inhabited by the zero flow (`vacuumFlowTo_zero`; the witnesses have
  `C_b = 0`). `VacuumTied` (`RStep.lean`) still reads `sf.E`; its restatement on `Ev` is the coordinator's next task.
* `SFStepInput` is restated over the input record: `∀ rec : RepRec … k ρ νk, ∃ ρ' νk' (rec' : PreRec … (k+1) k ρ' νk'),
  (∀ j ≤ k, β′_j = β_j ∧ ν′_j = ν_j ∧ a′_j = a_j ∧ z′_j = z_j ∧ E′_j = E_j) ∧ IntegralStep ρ ρ'` (defect 5: the birth domain `sfDom`
  reads `ν_j` at every level). `classStepInput_of_parts` is re-proved (destructuring only).
* `stepDensity` carries the vacuum normalization `s` of the step: `ρ' = e^{-s|T^{(k+1)}_1|} S^{(k)} T^{(k)} ρ`. The forward vacuum flow
  `E_{k+1} = L^d E_k + g_k` grows like `L^{dk}` (`Fluctuation/VacuumFlow.lean`, W965), so a flow bounded by `C(log β_j + 1)` at every step
  needs the per-step normalization; `IntegralStep` allows the positive constant `e^{-s|T^{(k+1)}_1|}`. `s = 0` is LFR's `ρ' = S T ρ`.

**Why the construction maps.** The parts of LF-3 are properties of one construction. A split "∃ small-field data with clauses X" +
"∀ small-field data with clauses X, ∃ large-field data with (D1) for `ρ'`" is false in its second half: the clauses are bounds and do not
determine the data, while (D1) holds only for the small-field data the step constructs (a different decomposition of the new level moves
`O(E₀)` terms between polymers, which the boundary terms cannot absorb). The source fixes the small-field image (LFR Thm IV.1.1 (e):
"the small-field data of `rep'` are the image of those of `rep` under I-9"), so the sub-spine takes the image as a map `Φ` and the vacuum
constant as a map `ΦE`, and every part is a statement about them. `SFStepInput` follows for every `Φ, ΦE`; the provider supplies the
maps of the source (the R8 objects, P5 Props 3.1–3.4 for `ℛ`, `ξ^{(k)}` of `rg_step_infty`) and proves the parts. Given `SFStepInput`,
maps satisfying the parts exist only if the image of the small-field data does not depend on the large-field data, which is LFR's (e).

**Proved inside** (no hypothesis beyond the sub-inputs and the typing facts):
* `sfSucc_clauses` (`SFStepClauses.lean`): (D2) of `IsRepPre2` at `k + 1` (`IsSFFamily2` on the birth domains with `preFac`), (D8SF),
  (D9) for the image, from `SFClassAt` of the input and A4-1a–f. Inherited levels: the landed `sfTermClauses_splice_birth`,
  `gsStrong_splice`, `torusIndep_splice`, `renorm_splice_birth` (general `d, L, N`, `Terms` on `birthXiDom`), with the old clauses moved to
  the domain of the new data by `sfTermClauses_congr_le` (new; through `SFTermClauses.inherit_le`), the background hypothesis of the
  inherited levels from (I.2) and `ν_k ≤ ν̄ ≤ 7/8 L⁻²` (`physMass_cap_of_top`), and (D8) of the inherited `ℳ^{(j)}` by
  `liftOldTermsFam_M_eq_of_d8` (new; the `M` analogue of `liftOldTermsFam_E_eq_of_torusIndep`). The density clause from the reality
  of the exponent: `exists_isSF2_of_real` (new).
* the new level is stated on `newLevelTerms` (the levels `j > k` of a family; zero terms and the whole-level sets `levelGS j` below), so
  `SFTermClauses`, `TorusIndep`, `D8SF` on it are the clauses of the new level alone, without restating their bodies;
* `integralStep_stepDensity`: `∫ ρ' = e^{-s|T^{(k+1)}_1|} ∫ ρ` (Gaussian normalization `integral_prod_gaussT_smul`, Fubini
  `integral_stepKernel_mul`, change of variables `θ ↦ zθ`), from the integrability A4-1i;
* (I.2) up to `k`, `β_0 = β`, `ν_0 = ν` and the ties `j ≤ k` from A4-1a (`runningHypTo_congr`); the flow `E′ = E` on `j ≤ k`, `E′_{k+1} = ΦE`
  with its bound; `k + 1 ≤ k̂_f + 1` (`kZero_le_of_isHorizon`, threshold `β ≥ 2`); the threshold is the largest of the nine and `2`.

Rule 10: `SFClassAt` (`sfClassAt_witness`), `RepRec` (`repClassAt_witness`), `VacuumFlowTo` (`vacuumFlowTo_zero`). The nine
sub-inputs (and the combinator `SFImageInput`) need the exemption of the spine inputs.

**The sub-inputs** (each: statement; source; landed pieces and the bridge to the sub-input; open; size, rough). `SFClassAt sf` is the
small-field half of a member of `ℛ_k` ((D2) with `fac = 1`, (D8SF), (D9), `a_j = compWeight L a j`, `β_0 = β`, `ν_0 = ν`, (I.2) up to
`k`); A4-1a–g are `∀ sf, SFClassAt sf → Q (Φ sf)` for `1 ≤ k < k₀`, `β ≥ β₀`, `ν L² ≤ 7/8` (`SFImageInput`).

1. **A4-1a `SFInheritInput`** (I-9, inherited part; R6; the free flow (II.1)). `Φ sf` has `β_j, ν_j, z_j, a_j` of `sf` and the terms
   `ℰ^{(j)}, ℳ^{(j)}`, `𝔹_j` of `liftOldTermsFam sf.Tm` at `j ≤ k`; `a_{k+1} = compWeight L a (k+1)`; `z_{k+1} > 0`.
   Landed: `liftOldTerms`, `liftOldTermsFam`, `oldTorusEquiv` (general `d, L, N`). Bridge: none; true by construction once `Φ` is defined
   as the splice of the inherited levels with the new level (`z_{k+1} > 0` from the flow). ~50.
2. **A4-1b `SFNewLevelInput`** (P3 (4.44)–(4.47), P4 Prop. 4.1, R8). `SFTermClauses (sfDom … (Φ sf) N₂) (newLevelTerms (Φ sf).Tm N₂)`,
   `GsSpecStrong (k+1)` of the new sets, `TorusIndep` of the new level.
   Landed: `localClass_newLevel_of_expansion_cast` (general `d, L, N`; the level-`(k+1)` clauses as a conjunction, on `xiFieldDom` with the
   sets `castG hc (localB …)`), its inputs from the chain at `d = L = 3`, `N = 2` (`e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot`,
   `e0CoeffFamily_class_fromTower_of_irrelBounds_X`, `newLabels_castInputs_of_localFamily`, `tower_E0_closure_agree`), `localClass_termClausesE/M`.
   Bridges (not landed): (i) the conjunction ⇒ `SFTermClauses` of `newLevelTerms` (the levels `≤ k` are trivial; at the top level
   `birthXiDom` is `completeXiDom`, `birthXiDom_dom_self`), ~150; (ii) `StepTower` (3, 3, 2) ⇒ `StepTowerG d L N` (open (f) of A4-1),
   `3 ∣ N₁`, `5 < N₁` ⇒ every `N₁ ≥ 1`; (iii) (A1)–(A5) on the local sets: route R-LOC (section "A4-1b (iii)", W1144; ~7,000);
   (iv) the castG gap (closed, W1141); (v) `TorusIndep` of the new level of a general class (only the core family is two-torus exact,
   W1089/W1090; after R-LOC L2 it is the two-torus agreement of the objects of `NewLevelFormula`). ~8,850.
3. **A4-1c `SFRenormInput`** (P4 (4.14)–(4.22), (5.28), (H.5), (H.6)). `CoeffBounds (k+1)` and `RenormCond (k+1)` of `Φ sf`.
   Landed: `rg_step_infty` (general), `renLocC1_scale_of_tower`, `renLoc_fields_scale_of_tower_at` (3, 3, 2). Bridges: (H.6) at `k + 1`
   from (H.6) at `k` and the bound of `ξ^{(k)}` (the flow is extended by one entry; ~150, not landed); (H.5) for the renormalized new level,
   the counterterm assembly `D_E = ℰ''₀(θ_ξ) + oldE + C₁ + C₂ −` vacuum (open (e) of A4-1: `oldE` of a general class, physical `locC2`,
   `locDφ`, `renE0_fibre`; `D_M`, `T_M` for the zero class only). ~1500.
4. **A4-1d `SFDensityInput`** (P4 (H.1) at `k + 1`). `(exp (expo2 P6 ⟨k₀, ν′⟩ β′ a′ (Φ sf).Tm N₂ ((Φ sf).E N₂) D g)).im = 0` at real realized
   data in `Ξ_{k+1}`. Landed: reality of the step's pieces (Lemma IV.1.3's `Δ` real for real arguments, the real old density `IsSF2.density`
   at `k`). Open: reality of the new level's terms at real data (not a clause of `SFTermClauses`) and of the composites. ~400.
5. **A4-1e `SFRemainderInput`** (P5 Props 3.1–3.4, LFR Lemma IV.1.8). `RTermsH4 … ((Φ sf).Rt N₂) (preFac (m₀ + m₁))`. Landed: the old
   `ℛ^{(k)}` clauses (input); FLUCTUATION Thm 3.4 marked expansion inputs (cited). Open: the remainders of the step at a general class. ~1500.
6. **A4-1f `SFCoherenceInput`** (LFR Thm IV.1.1 (h), D-IV.9). `D8SF m₀ {Φ sf with Tm := newLevelTerms}` (new level and `ℛ^{(k+1)}`).
   Landed: `e0CoeffFamily_value_fromTowerG_core_twoTorus` (W1089, `StepTowerG d L N`, `m₀ = 1`), `coreE0_unique` (W1090). Open: the
   chain's `e` of a general class is not a core family (open (c) of A4-1); `R_eq` of `ℛ^{(k+1)}`. The inherited levels are proved
   (`liftOldTermsFam_M_eq_of_d8`). ~800.
7. **A4-1g `SFVacuumInput`** (P4 (2.1), (2.41), (2.63); R5, R5′). **ΦE defined and the bound proved (W1132, `Spine/SFVacuum.lean`,
   `Spine/SFVacuumRatio.lean`).** The map is `vacMap` = `vacIncrement d L N aKer β_k (p(β_k))`, the Gaussian increment
   `Γ_k = L^d(E‴_k − E_k) = ½N(L^d−1) log β_k − ½N log(a₁L^{d−2}/2π) − L^d log Z₁(p₁)` (`vacIncrement_eq_step`, from `step_increment_eq`).
   It does not depend on the record or on `Ev`. The physical recursion is `E^{tot}_{k+1} = L^d E_k + Γ_k − e₀/|T^{(k+1)}_1|`
   (`vacuumEnergy_succ_eq_increment`); the class keeps `Γ_k` and the normalization `s = L^d E_k − e₀/|T^{(k+1)}_1|` of `stepDensity` carries
   the extensive rest (`vacIncrement_add_normalization`: `E^{tot}_{k+1} = Γ_k + s`). This is the one convention to confirm: `e₀` (determinant
   `½ log det C^{(k)}` plus `ℰ₁^{(k+1)}` at the zero datum) is put into `s`, not into `ΦE`; `s` is a free output of `LFStepInput`, and the tie
   only needs `|ΦE| ≲ log β`. **Proved:** `sfVacuumInput_of_inherit_renorm : SFInheritInput → SFRenormInput → SFVacuumInput … (vacMap …)`, with two
   range premises on the constants: `p(x) ≥ 1` for large `x` (`hp`) and `vacConst d L N aKer ≤ Cb` (`hCb`; `vacConst = ½N(L^d−1)(1 + log(5/4)) + ½N|log(aKer L^{d−2}/2π)|
   + L^d(|log Z₁(1)| + ½N|log 2π|)`). Ingredients: `abs_vacIncrement_le`, `abs_log_fluctNorm_le`, `CoeffBounds.beta_succ_ge`
   (`β_{k+1} ≥ (4/5) β_k L^{d−2}`) and (I.2) for `β_k ≥ (19/20) β`. **Open:** nothing in A4-1g itself; the size of `e₀/|T^{(k+1)}_1|`
   (needed for `s`, not for `ΦE`) and the tie `RecB0Bound` are A4-1h. If the orchestrator wants `e₀` inside `ΦE`, the added input is
   `|e₀|/|T^{(k+1)}_1| ≤ A' log β_k + B'` for the new terms (determinant part: `abs_halfLogDetC_le`, `O(1)`; `ℰ₁` part: new source mathematics, ~300).
8. **A4-1h `LFStepInput`** (LF-3 (b)–(d), (h); P5 §§2–3, P6 §§2–3; LFR Lemmas IV.1.2–IV.1.6, LF-2 (i), Lemma IV.1.5). For a record of
   `ℛ_k` whose image `Φ rec.F.sf` has (D2) with `preFac`, (D8SF), (D9), `a_j = compWeight` up to `k + 1` and the inherited `β, ν, z`:
   `∃ cs' P' lf' St' vc' s` with the outer constants, `IsRepPre2 … (k+1) ⟨Φ rec.F.sf, lf'⟩ (stepDensity … (β_k a L^{d-2}) z_{k+1} s ρ) St' vc'`,
   `LFCoherent` and the vacuum tie. **Split (W1136):** `lfStepInput_of_parts` (`Spine/LFStep.lean`) from ten clause parts on a step map `Λ` (two
   proved: (D5), (D6)) and the sign part; the kept data (S3) defined and proved; see "LFStepInput sub-inputs" below. ~6750 remaining.
9. **A4-1i `StepIntegrableInput`** (premise of P1 (1.11)). Members of `ℛ_k` are integrable in `ψ_k` on every torus, for `‖g‖₁ < 1`.
   Landed: `baseRho1_integrable` (the first density). Open: integrability of a (D1) sum from (D5) and the Gaussian decay. ~300.

**Watch.** (i) The SF→LF interface (item 3 of the inputs) is not used, and is not needed by A4-1h (W1136, below). (ii) `SFStepInput` now asks the ties `E′_j = E_j`; the frozen step's
analogue (`FrozenSFStepInput`) ties `β, ν, a` (W1121) but not the flow, and `FlatClassAt` carries no flow. (iii) The duplicates of private
lemmas of `Base/BasePhysicalDensity.lean` (`integral_gaussT`, `baseKernel_smul_integral`, the Fubini core) are special cases of
`integral_gaussT_left`, `integral_prod_gaussT_smul`, `integral_stepKernel_mul`; the base file can be re-based on them.

## A4-1b (iii): the new level on the local generating sets (W1144)

Target: a family `f z T′` with (A1)–(A5) of `newLabels_castInputs_of_localFamily` (`Inhabited/StepTowerLocalChart.lean`) on the local sets
`Gb(T′) = castG hc (localB (k+1) … (Yp Y⁺(T′)) hsep)` (`Yp` the collar of width `2L^{k+1+m₁′}`, `m₁′ = m₁ + 4`),
`Y⁺(T′) = sitesOf (piHull m₀ (thickSet S.G' (sitesOf T′)))`.

**(B4) Verdict: the radius loss of the read datum is real, and no clause pays it.**
* Radii. Class chart `ε_{k+1}`; chain step radius `t = λε_{k+1}` with the room `t + K₂Qt + K₂F·min(t, ηλε_k) ≤ ε_j` (`…_classEps_ren_rot`). At
  `Gb(T′)`: (A1), (A2), (A4) on the local chart of radius `ε_{k+1}`; (A3) on the local chart of radius `K_loc ε_{k+1}`, `K_loc = (2K₁+2)C₁`;
  (A5) at the data of the step chart of radius `ε_{k+1}`, whose datum read on `Gb` (`BgTransport.canon … .gdat`) lies in the local chart at
  `K_loc ε_{k+1}` (`castG_canon_gdat_xiCData_of_xiCData`, **proved**: `Ξ^c(S.G';1,ε) ⊆ Ψ̃^c(C₁ε, C₁ε)`, restriction to `Gb`, backgrounds
  recomputed on `Gb` at `ε + (2K₁+1)δ`).
* The loss is real: there is no inclusion at `(1 + o(1))ε`. `Ξ^c(Gb;1,ε′)` contains `collarBond`, `|Ψ(z) − Ψ(z′)| < ε′` for adjacent collar
  sites of `Gb` (real datum; the same for the displacement `Ψ″`), and on the layers `n ≤ k` of `Gb` the bounds `ε′/L^n`, `ε′/L^{2n}` on the
  gradient and Laplacian of a background whose `n`-block data are the step's `(k+1)`-block values. The step chart (a level set: no collar)
  bounds adjacent block values only through `close` (`|Ψ − Qφ| < ε` per block) and `grad` (`|Qφ(B) − Qφ(B′)| < ε`). A checkerboard datum
  `Ψ₀(B) = φ₀ ± ρεu` (`u ⊥ φ₀`, `ρ < 1`), whose background follows the checkerboard with the ratio `r = a/(a + O(d)) ≈ 0.1`, meets `grad`,
  `lap`, `close` at radius `ε` (hand estimate, not formalized: it needs the background of an explicit datum) and has adjacent block values
  `2ρε` apart; where a collar line of `Gb` crosses a block face, the read datum violates `collarBond` unless `ε′ > 2ρε`. So `ε′ ≥ 2ε(1 − o(1))`
  is necessary; the landed `K_loc ε` is sufficient. At `d = L = 3`, `q = ε_{k+1}/ε_k = 3^{−(1/2−γ)} > 0.577`, so even `2t > ε_k`: the chain
  cannot run at the read datum's radius (W1141's risk confirmed). (At `L = 7`, `q ≥ 0.378`; whether the true loss fits is open and irrelevant.)
* The source (P3 p. 79): the recomputed term is analytic on `Ξ^c_{k+1}(𝔹_{k+1}(Y);1,ε′)` (4.46) "with `ε′, δ₁` as discussed in connection with
  Lemma 4.2" — the local chart of the step's radius `ε′ ≤ ε_{k+1}`, under the same condition (4.37) `ε′ + (K₂+1)δ₃ ≤ ε_k` — and it equals the
  step's term as a function "depending on `θ, ψ′` restricted to `Y₁`" (pp. 78–79). The source never maps the step chart into the local chart.
* Why it costs nothing. No clause asks the read datum in the analyticity chart. (A1), (A2), (A4) are on the local chart of radius `ε_{k+1}`,
  where Lemma 4.2 at `Gb` has the step's room (`K₂ = xiK2 d L N` does not depend on the generating set). (A3) and (A5) are identities whose
  hypotheses are smallness conditions of `K_loc ε_{k+1}` against absolute constants (`FlCore`, `decDomMargin`, the coercivity margin,
  `C₁ε ≤ c₇`, `(3+K₄)C₁ε < 1/2`, `δ₀ ≥ 2K₄C₁ε`): the landed `coef_eTermFun_replacement_localB_restrict` is proved at `ε″ ≥ (2K₁+2)C₁ε′` with
  exactly these, and so are `detActivityBg_cross` and `newLevelDetBg_castG_canon` (L1′). Consequences: (i) the objects recomputed on `Gb`
  are gated and pinned at a radius `r_gate ≥ K_loc ε_{k+1}`, decoupled from the analyticity radius; (ii) the formula takes the activities as
  functions (`newLevelCoeffBg`), so it has a value at the read datum even where the bound of a `LabelAct` fails, the bundled `LabelAct`
  being formed only on the analyticity chart; (iii) A1′ gains the absolute smallness `K_loc ε₁ ≤ ε_*` (the provider's `α₀`).

**(B1) Route R-LOC: the chain's family as a formula, recomputed on `Gb`.** A family given only existentially cannot be recomputed, and the
chain's clauses do not determine it (W1076). R-LOC makes the chain return `e = newLevelCoeffBg S.G' …` on the step chart (determinant part
`newLevelDetBg` plus the interpolation coefficient of the marked cluster expansion, P3 (4.41)–(4.47), P4 (2.56)), and sets
`f z T′ p := newLevelCoeffBg (Gb(T′)) … (π_b (clipRaw Gb(T′) p), 0) T′` with the objects recomputed on `Gb(T′)` (R8's generic objects at
`Tr = canon`, gates at `r_gate`) and `π_b` a continuous linear projection onto `rawSub Gb` (as `π` of the step). (A5) is then the replacement
identity term by term: `newLevelCoeffBg_eq_of_agree` reduces it to the determinant part (proved, L1′), the activities on the labels whose cubes
lie in `T′` and the marks on the anchors inside `T′` (L3). (A1)–(A4) are Lemma 4.2 at `Gb` (L4).

| layer | content | status | rem |
|---|---|---|--:|
| L1 | `newLevelDetBg`, `newLevelCoeffBg` (generic in `Gb`, activities as functions), `gsumCoeff_eq_integral_of_agree`, `newLevelCoeffBg_eq_of_agree`; the base of the class chain returns its family as the formula, with the pins of the decoupling pairs `F₁`, `Sol` of the marks: `StepTowerG.e0CoeffFamily_class_agree_rot_formula` (`e = newLevelDetBg S.G' … (S.blockU z) + c` on `physV`, `c` the landed `gsumCoeff` formula; the landed `…_agree_rot` is its corollary) | **P** (`Fluctuation/NewLevelCoeffBg.lean`, `Inhabited/StepTowerRotClass.lean`) | 0 |
| L1′ | (B4) `castG_canon_gdat_xiCData_of_xiCData`, `canon_gdat_eq_of_mem_one`; determinant half of (A5): `newLevelDetBg_cross`, `newLevelDetBg_castG_canon` (margin `8L^{k+1+m₁}` from the collar `2L^{k+1+m₁+4}`) | **P** (`Inhabited/NewLevelCoeffBgCast.lean`) | 0 |
| L1″ | (B3) the determinant part on `Gb` without `HatConn`: `newLevelDetBg_analyticOnNhd` (on `physVBg`), `norm_newLevelDetBg_le_of_avoid`, `newLevelDetBg_ne_zero_imp_of_avoid`, `newLevelDetBg_eq_of_agree`, `newLevelDetBg_rot` | **P** (`Fluctuation/NewLevelDetBgClauses.lean`) | 0 |
| L2 | forward the formula to the endpoint. (a) **P**: `StepTowerG.e0CoeffFamily_class_of_labels_gen_onSet_agree_pad_rot_formula` (RotLabels, as L1). (b) **P**: `StepTowerG.zeroSourceFamily_fields_agree_rot_formula` (`StepTowerRotFields`: the direct terms `I` with `I.𝒴`, the pins `F₂`, `Sol₂`, the formulas of `I.T` and of `val`, `A = labelActFamilyOn … I`, `A₀ = zeroSourceAct A 2` on `thickLabels I.𝒴 I.dom`, `ZeroSourceFields`; `zeroSourceActivity_common_agree_rot` already returned all of these, with `hAeq`, so it is unchanged). (c) **P**: `NewLevelSystem`, `NewLevelFormulaFor`, `NewLevelFormula` (`Inhabited/NewLevelSystem.lean`); proved at the Families layer (`…of_families_core_onSet_agree_phi_formula`) and carried, as one more premise of `hΦ`, through Red, Collar{Core, X, Base, Struct, Step, Uniform, Class}, `…classEps_ren_phi`, `…classEps_phi` (each `_phi_formula` core; the landed `_phi` theorem is its corollary, statement unchanged) and returned as a conjunct by `…classEps_ren_rot_formula`, `…classEps_rot_formula`. (d) **P**: the Collar core discharges `OldTermsAreIrrel` (the old term of `τ` is `irrelTorus C.m₀ C.Tm i₀ i₁ j y X`), turning `NewLevelFormulaFor` (explicit `OldTermSystem`) into `NewLevelFormula` (inhabitation of the chain's `ι`, `Eτ`) | **P** | 0 |
| L3 | replacement of each object at `(Gb, canon)` (any cube-aligned, sup-separated `Gl`, `Gd ≺ Gl` with the layer `k` and no layer `k+1`; the recomputed maps pinned at their own level `δ₀′ ≥ 2K₄C₁ε′`) against `(S.G', self)` at the read datum `clipRaw Gl (rawOf D)`, for labels whose `2M₁L^{k+1}`-neighbourhood lies in the top layer of `Gl`: the block energy along the masked tangent (`coef_blockEnergyFun_replacement_marked_gen`, from `coef_blockEnergyFun_replacement_gen`); the terms from the coefficients, one core for both energies (`evDecBg_canon_eq_evDec_of_coef`; instances `evDecBg_canon_eq_evDec` (old terms), `evDecBg_canon_eq_evDec_block`); old marks and activities (`oldMarkGBg_canon_eq`, `oldActBg_canon_eq`); bridge marks on the parameter of `Gl` (`e1MarkGParamGBgOn` — `e1MarkGParamGBg` its instance `Gg = S.G'` — and `e1MarkGParamGBgOn_canon_eq`, via `decMarkGBg_eq_of_evDecBg`, `decMarkCorrBg_eq_of_evDecBg`); zero-source terms and activities on `Gb` (`zeroTermBg`, `zeroActBg`: the block-energy term at the marks `(1,0)` read at `Tr.res ψ̂`; `zeroTermBg_self`, `zeroTermBg_canon_eq`, `zeroActBg_canon_eq`; the chain's zero-source family is `zeroActBg` at the step's set: `zeroSourceAct_labelActFamilyOn_H_eq`); (A5) assembled: `newLevelCoeffBg_class_canon_eq_of_det` (the class family `commonAct (A₀.sum (commonAct A_C …))` of the Families layer, `classActFun`, `newLevelCoeffBg_class_eq_of_agree`), reduced to the determinant part (L1′) | **P** (`Fluctuation/LocalSetActMarked.lean`, `NewLevelOldTermsBg.lean`, `NewLevelBlockTermsBg.lean`, `NewLevelZeroSourceBg.lean`, `Inhabited/NewLevelOldTermsBgCast.lean`, `NewLevelBridgeMarksBgCast.lean`, `NewLevelCoeffBgClass.lean`, `NewLevelCoeffBgClassCast.lean`; W1146) | 0 |
| L4 | clauses of `newLevelCoeffBg (Gb(T′))` on the local chart: `ParamMarkFamily` over `physVBg Gb` (bundled `LabelAct` on the chart of radius `ε_{k+1}`); Lemma 4.2 at `Gb` (`BgSetting N Gb (Gk τ) (Gj τ)`, `FlSetting` at castG sets from `flCore_castG_localB`, the composed data in the old terms' domains: the premise `hchart` of the chain, open item (d), at `Gb`); the bridge marks' `hloc/hcau/hJ2/hJ4` at `Gb` (R8-AUDIT D2: per label inside the top layer); (A3) Gb-vs-Gb locality on the `K_loc` chart, which needs `Gst_congr` with a `DepOn` hypothesis in place of the bundled activity (a core in `Polymer/MarkedCubesLocal.lean`, landed statement its instance; low in the import graph: a large rebuild); (A4) covariance at `Gb`. **Done (W1146):** L4-1, the R8 field lemmas of the marks on the chart of any generating set `Gg` (`XiCRaw Gg`, `physVBg N Gg`): `deriv_evDecBg_hatOf_fields_gen`, `decMarkGBg_dep_gen`, `norm_decMarkGBg_le_gen`, `decMarkCorrBg_fields_of_gen`, `decMarkGBg_eq_zero_of_gen`, `decMarkCorrBg_eq_zero_of_gen`, `e1MarkGParamGBgOn_fields_label/_of` (the landed lemmas at `Gg = S.G'` their instances); L4-2a, Lemma 4.2 at `Gb`, (AE1) part (`Fluctuation/NewLevelTermsBgAnalytic.lean`): `evDecBg_canon_bound_analytic` (every term `evDecBg` recomputed on `Gb` with `BgTransport.canon`, for a functional analytic and bounded on `FlRealLC Gb Gd … X₁g`, `X₁g ⊆ X₁` in the top layer of `Gb`, is bounded by `E_b e^{-κ₀Δ - 2κ_dec d̃(Y)}` and jointly analytic in `((Θ, ψ̂), (um, tm))` on the chart of `Gb`), `evDecBg_canon_fields` (the hypotheses `hcau`, `hJ2`, `hJ4` of the R8 field lemmas at `Gg = Gb`); cover-form marked fan `fanLocalHatMarked_analytic_cover`, `fanLocalHatMarked_norm_le_cover` (the marked local hat field `u ψ'_loc + t M_Z ψ'_loc`; the landed `fanLocalHat_*_cover` the instances `(u, t) = (1, 0)`), the multiplier cores `localHatLiftMul_*`, `markedEv_physVBg_of_joint`. L4-2b, Lemma 4.2 at `Gb`, (AE2) part, by the cover-form row-local theory (decision (a)): the row-local cores ask the connectedness of the thickened cubes only at the admissible centres (`HatConnAdm G X₁ 𝒞`, `Dec2.HatConnAdm`; `hdich_aux_adm`, `dg5'_inner_adm`, `dg5x'_inner_adm`, `local_step_rows_adm`, `i4a_local_rows_adm`, `i4b_local_rows_adm`, `incUnion_of_nnComp_adm`, `SYF_subset_SY_adm`; standing hypotheses `LocHypAdm` with `LocHyp.toAdm`, `locHypAdm_nonempty`, through `Gsx_agree_local2_adm` … `I4c_local_sqrt_rows_adm`, `hatSqrtF_rows_of_bgAgree_adm`) and the footprint inclusion as a hypothesis or from margin hypotheses (`footprint_subset_component_of`, `approxDep_subset_component_of_near`, `resSites_coord_bound_of`, `approxDep_coord_bound_of`, `approxDep_subset_hatBox_of_near_of`; `rowsDep_subset_component_of`, `i4b_local_of_agree_on_component_adm`, `bgField_/bgAgree_of_agree_on_component_adm`, `fluct_correction_rows_of_tangent_agree_adm` with the collar of `H⁻` next to `S_Y^F` a hypothesis); every landed statement is an instance.  The fan at a component for any tangents agreeing there, `fan_value_eq_of_component` (`marked_fan_local_rawY_of` its instance); at `Gb` (`Fluctuation/NewLevelTermsBgLocal.lean`): the admissible centres of a component in the top layer are top centres (`top_of_adm`, `hatConnAdm_of_top`, `hatBox_subset_Omega_of_top`), the sites near a label with margin are in the top layer (`layer_near_of_labelMargin`), the transported parameters (`extS_canon_par_one/_zero`), the marked local hat field in the ball and on the component (`markedHatPsiFBg_liftZ_mem_flBallLC_core`, `markedHatPsiFBg_liftZ_rows`), the term of one family (`fanBg_canon_eq_of_family`) and **`evDecBg_canon_local_of`**: for every label `Y` with `LabelMargin Gb Y`, the terms `evDecBg … Y (Θ, res ψ̂)` agree at two data of the chart of `Gb` with `AgHatDir Y` (the hypothesis `hloc` of the R8 lemmas at `Gg = Gb`), for a functional with the agreement property of the row theorems (typing data: `H⁻` without layer `k + 1`, covering `Ω_{k+1}(Gb)`, `RowInHat`). L4-2c: the agreement property of the block energies at any generating set with the block margin (`blockEnergyFun_rowAgree`, the core of the agreement step of `marked_vblock_fan_local_rawY`), the block margin at `Gb` from the step's when `X₁` is in the top layer (`blockMargin_of_top`), and the locality of the block-energy terms at `Gb` (`evDecBg_canon_local_blockEnergy`; no top-layer hypothesis: otherwise no family has a label with the margin). L4-3 (parts 1–2): the bundling of the activities at the configuration restricted to the blocks of the label (`Fluctuation/LabelActRestr.lean`: `restrConf`, `labelActRestr`, `labelActRestr_H_of_dep`, `paramMarkFamily_restr`; no ψ̂-`dep` field, (A5) through the step's own `dep`), `sum_rayTerm_dl3_analytic_bound`, and the fields of the zero-source activities on `Gb` from the bounds and analyticity of the block terms (`Fluctuation/NewLevelZeroSourceBgFields.lean`: `zeroEvBg`, `zeroTermBg_analytic_bound`, `zeroActBg_fields`: bound, analyticity on `physVBg Gb × {‖u‖ < 2}`, continuity and measurability in the configuration). L4-3 (piece 6): the fields on `Gb` of every object of the formula, for the labels inside the top layer of `Gb`: zero-source activities (`Fluctuation/NewLevelZeroSourceBgCanon.lean`: `zeroEvBg_canon_bound_analytic`, `zeroActBg_canon_fields`, bound `8 |β| (6 M_ω c₁ M^d |E_sc| / r³) e^{-(2κ_dec-1) d^{cov,1}(Y)}`); the old terms on `Gb` have the step's settings (`Fluctuation/NewLevelOldTermsBgSetting.lean`: `bgSetting_of_top`, `flSetting_of_top`, `eTermFun_analytic_bound_of_top`: the premise `hchart`/(d) at `Gb` follows from the step's when the data sites of `Gk` lie in the top layer); old activities and marks (`Fluctuation/NewLevelOldTermsBgFields.lean`: `gatedMarkDiff_fields`, `oldActBg_canon_fields`, `oldMarkGBg_canon_fields`); bridge marks for the labels with `LabelMargin Gb` (`Inhabited/NewLevelBridgeMarksBgFields.lean`: `blockEvBg_canon_R8`, `e1MarkGParamGBgOn_canon_fields`, through the class-restricted cores `norm_markedOutDec_le_of_term_bounds_on`, `corrected_markedOutDecBg_bound_on`, `markedOutDecCorrBg_fields_of_gen`, `continuous_markedOutDec_decMarkCorrTermBg_on`, `evDecBg_eq_zero_of_not_subset`, landed statements their instances); the truncated bundled family (`Fluctuation/ParamMarkFamilyTrunc.lean`: `truncAct`, `truncMark`, `truncMark_dep`, `paramMarkFamily_trunc`). L4-4 (piece 8, W1146): the recomputed family as the local formula and the reduction of (A1)–(A5) to its parts. `Fluctuation/NewLevelCoeffLoc.lean`: `InPoly`, `locAct` (activities of the labels inside `T` at the configuration restricted to their blocks, `0` otherwise), `newLevelCoeffLoc` (the formula with `locAct` and `truncMark … (InPoly T)`); `newLevelCoeffBg_eq_loc_of_agree` ((A5) form: the step's coefficient equals the local formula of functions agreeing with it inside `T`; through the step's own locality, `LabelAct.dep`, `hGdep`), `newLevelCoeffLoc_congr` ((A3) form), `newLevelCoeffLoc_eq_gsumCoeff`, `newLevelCoeffLoc_analytic_bound` ((A1), (A2) form, via `paramMarkFamily_trunc` with the class `InPoly T`), `newLevelCoeffLoc_rot` ((A4) form, via `gsumCoeff_rot`). Truncation to the labels inside `T` replaces a Gst locality for function activities: the patch `Gst_congr_of_dep` of `MarkedCubesLocal` (patch_part2, G) is not needed and was dropped. Label by label (A5): `newLevelCoeffBg_class_canon_agree` (the agreement facts of `…_canon_eq_of_det_gen`, whose proof is now `newLevelCoeffBg_class_eq_of_agree` + it; `commonAct_sum_H_agree`, core of `newLevelCoeffBg_class_eq_of_agree`), `NewLevelSystem.agree_canon` (`coeff_eq_coeffBg_canon_of_det` now its corollary), `NewLevelSystem.actBg`, `markBg` (the recomputed activities and marks; `coeffBg` built from them, body definitionally unchanged), `NewLevelSystem.coeffLoc`. System level (`Inhabited/NewLevelSystemLoc.lean`): `xiCRaw_mono_radius`, `actBg_gate`, `markBg_gate`, `coeffLoc_gate`, `coeffLoc_congr_of_parts`, `coeff_eq_coeffLoc_of_agree`, `coeffLoc_analytic_bound_of_parts`, `coeffLoc_rot_of_parts`. Objects (`Inhabited/NewLevelObjectsBgLocal.lean`, `NewLevelTermsBgRot.lean`, `NewLevelObjectsBgRot.lean`): `zeroTermBg_canon_local`, `zeroActBg_canon_local`, `oldActBg_congr_of_terms`, `oldMarkGBg_congr_of_terms`, `e1MarkGParamGBgOn_congr_of_terms` (two configurations: (A3) and (A4)); `liftZ_rotFld`, `resZ_rotFld`, `evDecBg_canon_rot` (spin covariance of the terms recomputed on `Gb`: `fanLC_rot_cover` and `markedHatPsiFBg_rot`, the lift-generic core of `markedHatPsiF_rot`), `blockEvBg_canon_rot`, `zeroTermBg_canon_rot`, `zeroActBg_canon_rot`; `rotFld_lin`; two-line cores `lineD_congr_line_of`, `dl3_congr_line_of`, `rayTerm_dl3_congr_of_line_of` (landed one-line versions their instances). L5 groundwork: `castG_localB_pair` (the facts of the local pair), `localFamily_of_coeff` (the clauses (A1)–(A5) of the family of the pair of fields `f T p = c T (π_b (clipRaw (Gb T) p), 0)` from those of a family `c T` of the parameters of `Gb T`). **Open:** the agreement property and the covariance of the old terms' functionals `eTermFun Gb …` at `Gb` (piece 7, drafted: the cores `eTermFun_eq_of_component_of`, `approxDep_composeDep_subset_X1_of`, `active_layer_of_near`, `approxField_congr_of_reads`; ≈155-module rebuild; `Gst_congr_of_dep` no longer needed); they enter L5 as the hypotheses `holdloc`, `holdrot` | O | 300 |
| L5 | `f`, `π_b`, the inputs (A1)–(A5), then `localClass_newLevel_of_expansion_cast`. **Done (W1146, piece 9):** the clauses of the recomputed family at a generic local pair `(Gl, Gd)` (cube aligned, sup-separated, `Gd ≺ Gl` with the layer `k` of `Gl` and no layer `k + 1`): (A5) `NewLevelSystem.coeffLoc_read_of` (`Inhabited/NewLevelSystemRead.lean`; `agree_canon` + `coeff_eq_coeffLoc_of_agree`, the determinant part at the read data a hypothesis, given for the cast local sets by `newLevelDetBg_castG_canon`); (A3) `NewLevelSystem.coeffLoc_local_of` (`Inhabited/NewLevelSystemLocality.lean`: determinant `newLevelDetBg_local_of_margin` from `resDep_eq_of_top` (`Fluctuation/ResDepTop.lean`, `Fluctuation/NewLevelDetBgLocal.lean`), zero-source `zeroActBg_canon_local`, bridges `e1MarkGParamGBgOn_congr_of_terms` + `evDecBg_canon_local_blockEnergy`, old activities and marks `oldActBg_congr_of_terms`, `oldMarkGBg_congr_of_terms` from the locality `holdloc` of the old terms); (A4) `NewLevelSystem.coeffLoc_rot_of` (`Inhabited/NewLevelSystemRot.lean`: `newLevelDetBg_rot_param`, `zeroActBg_canon_rot`, `blockEvBg_canon_rot_of_margin`, the old terms through `holdrot`; sitewise rotation of the block variables `exists_blockSplit_equiv`, reference configuration `0`); two-configuration cores `decMarkGBg_eq_of_evDecBg_conf`, `decMarkCorrBg_eq_of_evDecBg_conf` (`Fluctuation/NewLevelBlockTermsBg.lean`, the landed one-configuration statements their instances). **Done (W1146, pieces 10, 11a–c):** (A1), (A2) at `(Gl, Gd)` (`Inhabited/NewLevelSystemAnalytic.lean`: `NewLevelSystem.coeffLoc_analytic_bound_of`, from `zeroAct_fields_of`, `oldAct_fields_of`, `marks_fields_of`, the step's bounds `ε_H e^{-κ_H d}`, `F₀ e^{-κ_G d}` numerical premises); the old terms' locality and covariance from their settings (piece 7: `evDecBg_canon_local_eTerm`, `evDecBg_canon_rot_eTerm`); the five clauses at a generic local pair from the settings of the old terms (`Inhabited/NewLevelLocalClauses.lean`: `clause_local_of`, `clause_rot_of`, `oldFun_fields_of`, `clause_analytic_of`, `clause_rot_full_of`, **`clauses_of`**); the instantiation at `Gb(T′)` (`Inhabited/NewLevelLocalCast.lean`: `flCore_castG_localB_of`, `newLevelDetBg_castLocal_read` (deep margin `8L^{k+1+m₁} ≤ 2L^{k+1+m₁'}`, `m₁ + 2 ≤ m₁'`), `clauses_castLocal_of` (pair facts, cover base, cores, the pairs `Dec2.i4b_analytic`/`Dec2.i4a_analytic`, `π_b`, margins) and **`NewLevelSystem.localFamily_castLocal_of`**: `f`, `b` of the root `z` with the forms `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval` of `newLabels_castInputs_of_localFamily`); the step's `FlSetting` of the old terms at free cover constants (`flSetting_of_top_gen`, `eTermFun_analytic_bound_of_top_gen`, landed statements instances) and the settings at the gate radius `ε′` from those at `t` and `ChainNum`, `FlNum` at `ε′`. **Open (chain gap, piece 12):** `localFamily_castLocal_of` is stated for a given system `NS` and takes (a) the old terms' settings at `t` (`BgSetting`, `FlSetting`, `CovSetup`, `X₁f = X1`, the trees `hoptL`, `FkL` analyticity), (b) the chart, bounds and covariance of `Eτ` on `XiCRaw (Gj τ) b ε₃`, (c) numerical conditions on the constants of `NS` and `NS.O` (those of the chain at `t`; at the gate radius `ε′`: `FlCore` of the step, `ChainNum`, `FlNum`; at the cover constants `mixedKc`/`selfKc`: `DecSpecs`, the caps `c e^{N₀κ} ≤ L^{m₁}`). Plan: (a) and the numerics at `t` are base-layer premises of the chain (`StepTowerBeta0Families`): fields of `OldTermSystem`/`NewLevelSystem` built there; the constants of `NS` exposed by `NewLevelFormula` (equalities with the tower's constants) so that the numerics at `ε′`, `mixedKc` can be discharged by the tower; (b) is not proved by the chain: its `hchart`, `hEbd` (P1 (3.128), open) are stated at the composed **step** data, and the composed data of `Gb(T′)` are not composed step data (no extension, `WIDEGEN.md`), so the open input must be stated on the term domain (or at the composed data of every local pair with the step's settings) — ruling requested | O | 1,500 |

**L5 R1 (W1146) — done.** `NewLevelSystem.OS : OldTermSettings` (the settings of the inherited levels at `t`: `BgSetting`, `FlSetting`, `CovSetup`, `X₁f = X1`, the trees of `XL`, analyticity of `FkL`, `L^{m₀} ∣ N₁`; built in `StepTowerBeta0Families` from the base premises), `NewLevelConsts`, `NewLevelSystem.consts`, `NewLevelSystem.HasConsts`; `NewLevelFormulaFor … O K e` and `NewLevelFormula … K e` carry the constants `K` through `Beta0Red`, `CollarCore` (`of_for`), `CollarX`, `CollarBase`, `CollarStruct` (`ρ = p₁`), `CollarStep`, `CollarUniform`, `CollarClass`, `RenThetaClass`, `RotChain`, `RotChainRen`: at the top `K = ⟨Tk.κ, Tk.BG, Tk.BG₂, p₁, Tk.κ0, Tk.κ, Tk.BG, Tk.BG₂, min Tk.t (η (λ ε_k)), p₁, C.m₀, Tk.c, 4dL³+L, Q Tk.t, levelKc, C_χ, Tk.c₂, F min Tk.t (η (λ ε_k))⟩`. **Next (R13, approved in the amended form):** the generating-set field `Tm.gs j X = 𝔹_j(X⁺)` alongside `gsStrong` (`IsSF2`, `SFTermClausesStrong`, `SFNewLevelInput`) and the 7 construction sites; the chain composing on `Tm.gs j X` with the cover set `X⁺ ∪ □(y)`; the class domain with the step's weights and background mass; then the final theorem of row (iii) with `d2raw_mem_birthXiDom_of_top` in place of `hchart` and `NewLevelNumerics`.

**L5 piece 12 rulings (coordinator, 2026-10-21).** R1: `NewLevelSystem`/`OldTermSystem` carry the old terms' settings at `t` (`BgSetting`, `FlSetting`, `CovSetup`, `X₁f = X1`, `hoptL`, analyticity of `FkL`) and the constants with equalities to the tower's as fields, built in `StepTowerBeta0Families` and carried up through `StepTowerBeta0Red`/`StepTowerCollarCore`; `NewLevelFormula` exposes them; landed statements unchanged where possible. R2: the open inputs `hEbd` (P1 (3.128)) and `hchart` restated on the class term domain (the bound and chart of `Eτ` on its own analyticity domain), the bound at the composed data of a local pair derived by domain inclusion, the inclusion proved in piece 12; the class-domain `hEbd` stays the open input A4-1b (ii). R3: the numerics at `ε′` and at the cover constants stay premises of the final theorem (conditions on constants), with `exists_newLevelNumerics` for their simultaneous satisfiability by the chain's admissible constants. **Obstruction to the R2 inclusion (W1146):** the class term domain of the label `τ = (j, y, X)` is `Dom.dom j (Tm.gs j X) ∩ {dot (Ψ y) (Ψ y) ∈ slitPlane}` (`irrelTorus_analyticOnNhd`), over the class generating set `Tm.gs j X`, which the class specifies only by `GsSpecStrong j X` (layer `j` on `X`, no layer above `j`; `levelGS_strong`: the whole-level set satisfies it). The composed data `D2raw (Gk τ) (Gj τ) … (d1Triple Gp (Gk τ) Hm …)` of any local pair (the step's or `Gb(T′)`'s) vanish off `Ω₁(Gj τ) ∪ collar (Gj τ)` (`composeField`), `Gj τ = castG hc (𝔹_j(XL τ))` (`settings_family_castLocalB_spec`), while every point of `Dom.dom j G` with `Dom = sfDom = birthXiDom` has `Ψ(x) ≠ 0` at every data site of `G` (`XiDom` → `RealizesC` + `InUnionDomainC` (R2), (C2a)). For `Tm.gs j X = levelGS j` the inclusion is therefore false (also for the step: the chain's present `hchart` premise is unsatisfiable for such classes), and the route through the locality `localE` of `Tm.E` needs a small-field extension of the composed field from `X` to the data sites of `Tm.gs j X`, which fails for `N = 2` around a hole of `X` (`WIDEGEN.md`). The inclusion needs a locality property of the class generating sets (the source's `𝔹_j(X)`: e.g. `Tm.gs j X` the cast local set `𝔹_j(X)` and the chain composing on it), or the open input stated at the composed data of the local pairs with the step's settings — ruling requested. **R13 asked** (PLAN-B; option (a)); checks of (a) landed (W1146): `stPlus_mem_dataSites` (the sites `y + L^j e_μ` of `irrelTorus` are data sites of `𝔹_j(X)`, one-site collar), `settings_family_castLocalB_spec_gen` (the settings with `Gj τ = castG (𝔹_j(X_τ))`), `d2raw_d1Triple_mem_xiDom_of_top`, `dot_mem_slitPlane_of_xiDom`, `aIdeal_eq_compWeight`, `aIdeal_compWeight`, `physMass_nuIdeal`, `d2raw_mem_birthXiDom_of_top` (`Fluctuation/OldTermClassDomain.lean`: the inclusion under (a) with the weight and mass matching).

**L3 interface (W1146).** `newLevelCoeffBg_class_canon_eq_of_det` takes the step's objects through their formulas at the step's own set at the read parameter `θ`: `h0eq` ((A₀ θ s).H Y = `zeroActBg` self …; from the zero-source equation of L2 (b) by `zeroSourceAct_labelActFamilyOn_H_eq` and `zeroTermBg_self`), `h1eq` ((AC θ s).H Y = `oldActBg` self …: the chain's `hAC` with `hH`, `oldActBg_self` by `rfl`), `hG₁eq` (`hG₁`, `oldMarkGBg_self` by `rfl`); the bridge marks are `e1MarkGParamG` itself; `hGdep` (locality of the step's marks, (M2)); the read condition `hkX` (data sites of `Gk τ` in `X₁(τ)`: from `BgSetting.dsX₀` and `.hN`); the radius conditions `17/16 ≤ R_u`, `R_u m_R < δ₁`, `2ρ₀ ≤ c_ψ` (zero source, `ρ₀ = p₁`), `ρ ≤ c_ψ`. L5 supplies the margin of `sitesOf T′` in the top layer of `Gb(T′)` (`castG_localB_collar_margin`) and `hdet` (`newLevelDetBg_castG_canon`). **For the system** (`Inhabited/NewLevelSystemCanon.lean`, W1146): `NewLevelSystem.coeffBg` (the coefficient of a system recomputed on `Gl` at a parameter of `Gl`) and `NewLevelSystem.coeff_eq_coeffBg_canon_of_det` (`NS.coeff θ T = NS.coeffBg … θ_b T` at the read datum when the determinant parts agree; `h0eq` by `NewLevelSystem.zeroAct_eq_zeroActBg`, `h1eq` by `hAC`, `hH`, `hG₁eq` by `hG₁`; the pins of the system for the step's pairs; the old terms keep their own constants `O.κ`, `O.BG`, `O.BG₂`, `O.δ₁`, through the core `newLevelCoeffBg_class_canon_eq_of_det_gen`). The locality of the marks is carried by the system: fields `hG₁dep` (the mark of `q` depends on the blocks of `bridge 1 z q.1.2`) and `hbrdep` (the bridge mark of `i` on the blocks of `i`), `NewLevelSystem.G_dep`; proved at the Families layer from what the chain proves: RotLabels returns the locality of `G₁` (from `classMarks_M2_of_family_gen_onSet_pad`), the base layer `…agree_rot_formula` that of the bridge marks (from `e1MarkParam_pairs_fromTowerG`). L5 reads `NS.G_dep` for `hGdep`.

Specification of L2 (c), for L3 (**as built**, `Inhabited/NewLevelSystem.lean`). `NewLevelSystem S C z Jr` (`Jr : S.JointRep t pp`, so `t` is
its index) bundles, with `p₁` and the constants `κ BG BG₂` of the decoupling pairs:
* `Z : ZeroSourceSystem S hp t p₁ κ BG BG₂`: `I : DirectTerms S 1 hp …` (with the family `hF` and the constants `εU κH cψ Rr κ0`), the source `val`, the
  pins `F₂`, `Sol₂` (`hF₂ : ∀ z, DecFieldPin S κ BG (F₂ z)`, `hSol₂ : ∀ z, DecSolPin S κ BG₂ (2 K₄ ξ t) t (Sol₂ z)`), `hT : ZeroSourceTermFormula S F₂ Sol₂ I.T`
  (the formula of the direct terms at a source-free datum) and `hval : ZeroSourceValFormula S κ BG₂ t val`; defined from it: `Z.A = labelActFamilyOn … I` (so
  `hAeq` holds by definition), `Z.Lab₀ = thickLabels I.𝒴 I.dom`, `Z.A₀ = zeroSourceAct Z.A 2`;
* `O : OldTermSystem S t`: the inherited levels, `ι` finite, `m₀ jL X₁f 𝒦X ϱ₁ Gk Gj`, the old terms `Eτ`, the localization fields `F₁L SolL FkL`, `ρ`, and the pins
  `hF₁L`, `hSolL`, `hFkL` (`FkPin`) with their constants; `hEJ`: `Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w))` on the chart;
* the marks `G₁` of the old terms with their equation `hG₁` (the `evDec`/`eTermFun` formula), the domains `𝒴C` (`h𝒴`, `h𝒴dj`), the explicit thick activities
  `H` with `hH`, `AC` with `hAC : ∀ θ ∈ physV, ∀ u Y, (AC θ u).H Y = H θ Y u`, `hZ : ZeroSourceFields S hp Jr Z.Lab₀ Z.A₀`, and the decoupling pairs `F₁`, `Sol` of the
  bridge marks with their pins `hF₁`, `hSol`;
* derived (abbreviations): `Lab1 = Z.Lab₀.sum (commonLabels (thickLabels 𝒴C …) …)`, `Lab = commonLabels Lab1 … (e1DomG S) …`, `A = commonAct (A1 …)` with
  `A1 θ u = (Z.A₀ θ u).sum (commonAct AC … θ u)`, `y0 = Sum.elim (commonAnchor …) y1`, `G θ = Sum.elim (e1MarkGParamG S (F₁ (z, ·)) (Sol (z, ·)) p₁ hp z t θ) (G₁ θ)`, and
  `coeff θ T′ = newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N BG κ) (S.blockU z) θ T′ + gsumCoeff μ Lab (A θ) y0 (G θ) T′`.
`NewLevelFormulaFor S C z Jr O e := ∃ NS, NS.O = O ∧ ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T′, e θ T′ = NS.coeff θ T′` (the layers from Families to Red, where `ι`, `Eτ` are the
chain's variables); `OldTermsAreIrrel S C O` (`O.m₀ = C.m₀` and `Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (jL τ) (y τ) (X τ) r.1 r.2`, the equation of (d)) and
`NewLevelFormula S C z Jr e := ∃ NS, OldTermsAreIrrel S C NS.O ∧ ∀ θ ∈ physV …, e θ T′ = NS.coeff θ T′` (from the Collar core up). Inhabitation (rule 10):
`NewLevelSystem.formulaFor_coeff`, `.formula_coeff` (every system's `coeff` satisfies them); the systems of the physical step are those constructed by the chain
(`…ren_rot_formula` returns `NewLevelFormula S C z Jr e` for the family `e` at every admissible parameter of the chain). L3 reads `Z.hF₂ Z.hSol₂ Z.hT Z.hval`, `O.hF₁L O.hSolL
O.hFkL`, `hH`, `hG₁`, `hF₁`, `hSol`, and the equation `OldTermsAreIrrel`; the bounds of the activities are not part of the system.

Order: L2 (b)–(d) done (W1147); L3 done (W1146, reads their objects); L4 needs L3's objects (Opus: Lemma 4.2 at `Gb`); L5 last. Remaining
≈ 2,700 (after L3 and L4-1, L4-2a, L4-2b, W1146) (SPINE-PLAN's 1,300 for (iii) assumed `e` recomputable from the chain's statement). No landed definition changes: the R8 objects take
the gate radius as a parameter, and `DetExpansionLocCBg` (indexed by the step's datum) is not used for `f`, whose determinant part is
`newLevelDetBg` on `Gb`'s parameter. No ruling is requested.

**(B3).** `exists_detExpansionLocCBg_of_chart` needs `HatConn Gb`, false for local sets; `f` does not use it. L1″ proves the determinant clauses
on `Gb` from W1084's per-polymer forms (`norm_detActivityBg_le_of_avoid`, `detActivityBg_ne_zero_imp_of_avoid`, `detActivityBg_eq_of_agree_core`)
for polymers avoiding the layer 1 of `Gb` (a label `T′` lies in the top layer `k + 1 ≥ 2` of `Gb(T′)`) and from
`exists_analytic_detActivityBg_raw` (no `HatConn`). The bound is the step's (`|Zb| ≤ L^d`), so `b z T′` of (A2) is the chain's.

**(B2).** The coefficient is `dz + gsumCoeff(commonAct(A₀, AC), (bridge marks, G₁))`; `AC`, `G₁` are built from the inherited terms `Eτ`, and
the cluster expansion is not additive in the activities, so there is no "new-level part alone" (such as the zero-class core `e0`) for which
(A1)–(A5) would suffice: they are statements about the whole formula, `AC^{Gb}`, `G₁^{Gb}` included. Of the inherited pieces they need only the
generic definitions on `Gb` (R8: `evDecBg`, `FFmarkedBg`, `decMarkGBg`), the replacement at matched data (L3) and Lemma 4.2 at `Gb` (L4), not
their two-torus agreement. A4-1f needs that other property, and with L2 it becomes the two-torus agreement of each object of
`NewLevelFormula` (W1090's obstruction "the chain's `e` is not a core family" disappears with the formula): `AC`, `G₁` agree on two tori where
the inherited terms do (D8 of the inherited levels, `liftOldTermsFam_M_eq_of_d8`) and `evDec`, `decSol` do (W1089: `decSol_value_twoTorus`,
`explicit_evDec_of_core`). So A4-1f lands nothing that (A1)–(A5) need; both need L2; A4-1f after L2 ≈ 700.

## LFStepInput sub-inputs (W1136)

**PROVED** (`Balaban/Spine/LFStep.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`; `…` = `d N T P6 C7 PB cs₀ M1 c rH ϱ`):
```
theorem lfStepInput_of_parts (Λ : LFStepMap …) (hH : LFHistInput … Φ Λ) (hS : LFStepDataInput … Φ ΦE Λ)
    (hB : LFBdryInput … Φ Λ) (hBs : LFBdrySrcInput … Φ Λ) (hF : LFFormInput … Φ Λ) (hO : LFOpBoundInput … Φ Λ)
    (hP : LFPinInput … Φ Λ) (hG : LFBudgetInput … Φ Λ) (hC : LFCoherenceInput … Φ Λ) (hc : LFCorrInput … Φ) :
    LFStepInput … Φ ΦE
theorem lfOpBoundInput_of_signs (Λ : LFStepMap …) (hz : LFSignInput … Φ) : LFOpBoundInput … Φ Λ
theorem lfSignInput_of_inherit (hI : SFInheritInput … Φ) : LFSignInput … Φ   -- W1142
theorem lfBudgetInput_of_pin (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) (Λ : LFStepMap …) (hP : LFPinInput … Φ Λ) :
    LFBudgetInput … Φ Λ
theorem lfStepInput_of_prefix (hA1 : PrefixInput …) (Λ) hH hS hB hBs hF (hI : SFInheritInput … Φ) hP hC hc : LFStepInput … Φ ΦE
```
One landed proof was generalized (statement unchanged, `stmtcheck` CHANGED empty): `Rep.budgetPre_of_LF2` is now the instance
`K' = K` of `Rep.budgetPre_of_LF2_trunc` (`Def7Basic.lean`; (H6′)^pre from the counter history truncated at `K' ≤ K`, `K' ≤ top`).

**Why a map `Λ`.** As for `Φ`, `ΦE`: (D1) of the step density holds only for the histories, kernels and boundary terms that the step
constructs, and the other clauses (bounds, coherence) do not determine them; parts "∃ data with X" and "∀ data with Y, Z" would not
combine. A `Rep` contains the proofs (S0)–(S3) (fields of `StepData`, `KeptData`), so `Λ` gives the data created by the step only:
`LFStepRaw` (on every torus: histories `hist`, step kernels `ker`, boundary terms `B`; and the normalization `s`).
`LFStepRaw.Matches SD`: step data carrying these kernels; `LFStepRaw.fam`: the successor family; `RepRec.SuccFams sf' D Q`: `Q` for the
family with `sf'`, `D`, the kept data `succKD` and every such `SD`. The clauses read `SD` only through `ker` (`preOpTop_congr`,
`locOp_congr`), so a `SuccFams` statement is a statement about `Φ rec.F.sf`, `Λ rec` and `rec`.

**Maps, definitions and existentials** (formula ⇒ map or Lean definition; asserted to exist ⇒ existential in the part):
* maps (`Λ`): histories (LF-3 (c)), step kernels (LF-3 (d): quiet kernels, P5 (2.47)·P6 (3.2), boundary factors of P6 (2.32)–(2.33),
  (3.3)), `ℬ^{(k+1)}` (Lemma IV.1.5: three kinds), `s = L^d E_k − e₀/|T^{(k+1)}_1|`;
* Lean definitions (their clauses proved, not asked): `cs' = rec.succCs sf'` (`succOpConsts`: `rec.cs` at the scales `≤ k`, the running
  constants of the image at `k + 1` and beyond (`vacExt`); masses per R2), `P' = rec.succP sf'` (`succBudgetConsts`), and the kept data
  `rec.succKD sf'` with the exponents of `rec` ("no kept data are created by a step": `KeptData.upTo`, the input's kept data at the
  scales `≤ k`, zero kernels above; (S3) at `cs'` proved, `chiDomAt_congr`: `χ^{dom}` at scale `j ≤ k` reads `δ_i, p₀(β_i), C_ψ` with `i ≤ j`,
  which `cs'` shares with `rec.cs`);
* existentials: the (S1) witnesses, `b⁰`, the offsets `δ″, δ‴` (in `LFStepDataInput`; read by no other part, `b⁰` fixed by `b_vac`); the
  proofs (S0)–(S2); `St', vc'` (in `LFCorrInput`: P1 (3.110) asserts the limits; `LFFormInput` asks the form for every `vc'` with
  `D1CorrLim`, which fixes `vc'` at the scales `1 ≤ j ≤ k + 1` the form reads, `src_pos` with `ν_{k+1} > 0`).

**The parts** (`LFImageInput … Q`: every record `rec` of `ℛ_k`, `1 ≤ k < k₀`, `β ≥ β₀(κ, c₉)`, `ν L² ≤ 7/8`, unit `h`, horizon `kf`,
whose image `Φ rec.F.sf` has the hypotheses of `LFStepInput`; `F'` ranges over `rec.SuccFams (Φ rec.F.sf) (Λ rec)`):

| part | statement | source | status, landed | rem | R |
|---|---|---|---|--:|:-:|
| (c) `LFHistInput` | `IsComplete (k+1) (k+1)` of `Λ.hist nK` | LF-3 (c); Def. I.3.1, (R8) | O — `exists_isComplete` | 300 | L |
| (g1) `LFStepDataInput` | `∃ SD : StepData` at `cs'`, `P'` with `SD.ker = Λ.ker nK` and `SD.VacuumTie Set.univ (vacExt rec.Ev k ΦE) δ″ δ‴` | Lemmas II.5.14, IV.1.3, IV.1.4, IV.1.6; (S0) P6 (2.32)–(2.33); R5, R5′ | O — `quietStepData'`, `quietKernel`, `StepData.retie`, `vacExt` | 1,700 | H |
| (g1) kept data (S3) | `succKD` is `KeptData` at `cs'` | (S3) "no kept data are created" | **P** (`KeptData.upTo`, `chiDomAt_congr`) | 0 | – |
| (g2) `LFBdryInput` | `D7Bdry` (physical field, `B_st`, `3κ/2`, `Zpre (k+1)`) of `F'` | Lemma IV.1.5; P5 p. 512; P6 pp. 14–15, 34 | Rd — W1140: `lfBdryInput_of_parts` (`Spine/LFBdry.lean`) from the three kinds; blocker-3 piece proved under ruling R11 (`Spine/LFBdryHole.lean`); section "LFBdryInput sub-inputs" | 1,100 | H (B3 → R11) |
| (g5) `LFBdrySrcInput` | `D7BdryBall`: `analytic`, `bound` at `h' ∈ hSetB2 h r_h`, `h' ≠ h` | blocker 2 leaf 5; Q13-YM §§2, 5; R2 | O — R2 objects, `KerBoundSrc` | 600 | H (B2) |
| (g3) `LFFormInput` | `D1PreForm2 (F'.ctx …) vc' (F'.lf nK) h (stepDensity … (β_k a L^{d−2}) z_{k+1} Λ.s ρ nK)` for `D1CorrLim … St' h vc'` | P5 (2.1)–(2.14), (2.42)–(2.48), §3, (3.18); P6 §2, (3.3); P5 (1.8) | O — `stepDensity`, `integral_stepKernel_mul`, `preOpTop_congr` | 1,200 | M |
| (g3) `LFOpBoundInput` | `D5Bound (k+1)` of `F'` | Lemma II.6.3 (a) | **P** from `LFSignInput` (`lfOpBoundInput_of_signs`, `Rep.opBound_of_data`) | 0 | – |
| `LFSignInput` | `0 < (Φ rec.F.sf).z j`, `1 ≤ j ≤ k+1` | P1 (1.11), P4 (4.1) | **P** (W1142): `lfSignInput_of_inherit` from `SFInheritInput` (`z_{k+1} > 0`, A4-1a, and `z_j` kept at `j ≤ k`) and the new carrier field `RepRec.zpos` / `PreRec.zpos` (`z_j > 0`, `1 ≤ j ≤ k`: the class clauses `D9Coeff`/`CoeffBounds`/`SFClassAt`/`RepClassAt` do not constrain `z_j`); `lfStepInput_of_prefix` takes `SFInheritInput` instead of `LFSignInput`; `zpos` is produced by `sfStepInput_of_parts` (from the input's `zpos` and A4-1a), carried by `rInput_of_parts`, `PreRec.retie`, `PreClassAt.succ`, and proved in the witnesses | 0 | – |
| (g4) `LFPinInput` | `D4Pin (k+1)` of `F'` (the exponents and kept data of `rec`) | (D4), LF-3 proof; LF-3 (c) | O | 300 | L |
| (g4) `LFBudgetInput` | `D6Pre` of `F'` | LF-2 (i), Thm I.5.4 (i) | **P** from `LFPinInput` + prefix (`lfBudgetInput_of_pin`, `Rep.budgetPre_of_LF2_trunc`) | 0 | – |
| (h) `LFCoherenceInput` | `LFCoherent F'` | LF-3 (h), D-IV.9 | O — (D8) of `rec` (old data), `quietKernel_twoTorus`, `bgLocPiece_twoTorus` | 1,000 | M |
| (h) `LFCorrInput` | `∃ St' vc', D1CorrLim (P6.m₀) (Φ rec.F.sf) St' h vc'` | P1 (3.106)–(3.110), P5 (1.8) | O — `wD1Corr` (zero terms) | 400 | M |

**Proved in the assembly** (no hypothesis beyond the parts): the choice of `SD` on every torus (`LFStepDataInput`) and `Matches`;
`cs'`, `P'` and the seven ties to `cs₀`, `PB` (those of `rec`); `Coh` at `k + 1` (`coh_succ`: from `rec`'s `Coh` and the ties of the image
at `j ≤ k`, `δ_j`, `p₀(β_j)` reading `β_j` only (`deltaRun_congr`, `pZero_congr`); `a_j` from the hypothesis); `FieldClauses` at `k + 1`
(`field_succ`); the kept data (S3) (`succKD`); `IsRepPre2` from its clauses ((D2), (D8), (D9) are the hypotheses on the image); (D7) of the
second version from (g2) and (g5) (`D7Bdry.toD7Bdry2_of_ball`, by cases `h' = h`); `LFCoherent`; the vacuum tie of the chosen step data.
In `lfBudgetInput_of_pin`: `S.Good` (`exists_good_lamHat`), (Λ15)–(Λ17′) (`analyticK_at`), the budget data of the prefix, (I.2) up to
`k + 1` for the image (`runningHypTo_succ_of_coeffBounds` from (I.2) of `rec`, the ties, (H.6) at `k + 1` of (D2), `FlowRateAt`) and for
`P'.beta`, then LF-2 (i) truncated at `k + 1`. In `lfOpBoundInput_of_signs`: `β_j > 0` at every scale (`rec`'s at `j ≤ k` by (I.2),
`imageBeta_pos` at `k + 1` by `CoeffBounds.beta_succ_ge`), `a > 1`, and `z_{j+1} > 0` from `LFSignInput` with the `Coh` of `rec`.

**SF→LF interface (watch item of W1096): DECIDED — not needed.** Under the landed `FieldClauses` (ruling R2) both halves evaluate their
actions at the complete background: `cs.muBg j = sfBgMass j` (`muBg_eq_sfBgMass_of_fieldClauses`); the main action of the step reads
`cs.muBg (k + 1)` (`MainAction.lean`), the small-field factor `cs.muBg k` (`SFCtx.phiK`). The interface (`SFtoLFInterface`) is the chord
between the actions at `lfBgMass` and `sfBgMass` with its localized pieces; no exponent of `IsRepPre2` is evaluated at `lfBgMass` (`cs.mu`
= `lfBgMass` enters only the sharp characteristic functions). `IsRep2WithInterface` is used by no theorem and has no witness
(`Def7v2Inhabited`: its (D9) forces `k ≤ k₀`, where the chord bound (3.5) is open). The change of the small-field exponent when the region
shrinks (Q13-FACTOR (1.1)–(1.3): boundary flux of the P5 (1.8) correction and of the polymer sums, re-evaluation at the new composed field)
belongs to (g3) and to the bound (S0) of `b_k` in (g1), and reads only (D1), (D2) of the input. No class clause and no ruling is needed for it.

**Two clauses of the input that the class does not carry** (found in the split; each is asked by a part, not assumed):
* *the vacuum tie of the input's step data.* The tie of `LFStepInput` is on `Set.univ`, i.e. at every step; at the old steps `j < k` the
  kernels are those of `rec` (the composition in (D1)), so `LFStepDataInput` there is the retie of `rec`: `VacuumB0Bound` of
  `(rec.F.lf nK).SD` on `rec.Ev` (the A4-2v estimate), blocked on ruling R10 like A4-2v (`norm_stepVacuumTerm_le_of_stepData`: every
  `StepData` has `‖vacuum term‖ ≤ 2(C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|` on `χ^new`, so a tie to a flow with `E_k ≠ 0` needs region 1
  localized). `VacuumTied` is produced by `SFStepInput` and dropped by `classStepInput_of_parts`; `RepRec`, `PreRec` have no tie field.
  Proposal (coordinator, spine carriers, no Def-7 change): a field `tie` of `RepRec`/`PreRec` (`∀ nK, ∃ δ″ δ‴, (F.lf nK).SD.VacuumTie
  Set.univ Ev δ″ δ‴`), produced by A3, kept by `RInput` (`RKeptGasInput` keeps `SD`), consumed by A4-1h; then the old-step half of
  `LFStepDataInput` is inheritance.
* *`z_j > 0` at the old scales.* `Rep.opBound_of_data` needs `z_{j+1} > 0` at every scale; `z_{k+1} > 0` is A4-1a, `z_j` for `j ≤ k` is
  `rec`'s and no clause bounds it. Proposal: `z_pos : ∀ j, 1 ≤ j → j ≤ k → 0 < F.sf.z j` in `RepRec`/`PreRec` (or in `Coh`).

**Rule 10.** `LFStepRaw` (`LFStepRaw.zero`), `Matches` (`LFStepRaw.matches_zero`), `D7BdryBall` (`d7BdryBall_of_hist_eq_empty`). The
parts and the combinators `LFImageInput`, `RepRec.SuccFams` need the exemption of the spine inputs.

**Size.** ≈ 6,750 remaining (table), against ~6,000 before the split: the split exposed (c), (g4)'s `D4Pin` and `LFCorrInput`, which the old
estimate counted inside (g3) and (h); the kept data and (D5), (D6) are proved. H items: (g1) (non-quiet kernels, and the old-step tie after
R10), (g2) (B3; closed under ruling R11, W1140), (g5) (B2).

## LFBdryInput sub-inputs (W1140)

**PROVED** (`Balaban/Spine/LFBdry.lean`, `Balaban/Spine/LFBdryHole.lean`; no `sorry`; axioms `propext, Classical.choice,
Quot.sound`; `…` = `d N T P6 C7 PB cs₀ M1 c rH ϱ`):
```
theorem D7Bdry.add_B (rep) (h₁ : D7Bdry … { rep with B := B₁ } … fac₁ rate hv) (h₂ : … B₂ … fac₂ …)
    (hB : rep.B = B₁ + B₂) : D7Bdry … rep … (fac₁ + fac₂) rate hv
theorem lfBdryInput_of_parts (Λ : LFStepMap …) (Sb : LFBdrySplit … Λ) {Bn Bd Bo : ℝ → ℝ → ℝ}
    (hBst : ∀ κ c₉, Bn κ c₉ + Bd κ c₉ + Bo κ c₉ ≤ (C7 κ c₉).Bst)
    (hN : LFBdryNewInput … Φ Λ Sb Bn) (hD : LFBdryDeltaInput … Φ Λ Sb Bd) (hO : LFBdryOldInput … Φ Λ Sb Bo) :
    LFBdryInput … Φ Λ
theorem norm_sum_le_of_transfer (I : Finset ι) (T : ι → ℂ) (Dm mk : ι → ℝ) (hCre : 0 ≤ Cre) (hB₀ : 0 ≤ B₀)
    (hκ : 0 ≤ κ) (hκo : 0 ≤ κo) (hT : ∀ a ∈ I, ‖T a‖ ≤ Cre * B₀ * exp (-κ * Dm a) * exp (-κm * mk a))
    (hmin : ∀ a ∈ I, Dmin ≤ Dm a) (hB₀min : B₀ * exp (-(κ/2) * Dmin) ≤ 1) (hsize : ∀ a ∈ I, Dp ≤ Dm a / L + Cd * mk a)
    (hent : ∑ a ∈ I, exp (-(κ/2 - κo/L) * Dm a - (κm - κo*Cd) * mk a) ≤ Kent) :
    ‖∑ a ∈ I, T a‖ ≤ Cre * Kent * exp (-κo * Dp)
theorem Def7.exists_transfer_fineValidAt (F) (hnn) (hkK : k + 1 ≤ K) (hΩ : d7Pull F (k+1) Om' ⊆ d7Pull F k Om)
    (hX : FineValidAt F k Om X) : ∃ Y : Finset (Torus S.d (n (k+1))), d7Pull F k X ⊆ d7Pull F (k+1) Y ∧
      FineValidAt F (k+1) Om' Y ∧ d7SizeAt F (k+1) Om' Y ≤ (S.L)⁻¹ * d7SizeAt F k Om X
theorem Def7.exists_transfer_fineValidAt_of_open … (hopen : ∀ z ∈ (d7Pull F (k+1) Om')ᶜ,
      IsPiPrimeUnion m₀ (k+1) (OmegaComp (d7Pull F (k+1) Om') z)) (hX : FineValidAt F k Om X) :
    ∃ Y, … ∧ FineValidAt F (k+1) Om' Y ∧ d7SizeAt F (k+1) Om' Y ≤ (S.L)⁻¹ * d7SizeAt F k Om X
theorem Fluctuation.transfer_patches … : DjModFin m₀ (j+1) Ω' (holeClose Ω' (transferLabel … ∪ ⋃ p ∈ P, box p …)) ∧
    dcovMod … ≤ (L)⁻¹ * bondCost (scaleW L m₀ m₁ j) E + cG d L * P.card
theorem Fluctuation.spill_of_defect, Fluctuation.djModFin_Yhat, Fluctuation.dcovMod_ge_supDist,
  DjModFin.cellCount_le ((G1)), djModFin_union ((G3)), djMod_iff_djModFin, Def7.fineValidAt_iff_fineValidFinAt
theorem RegionHistory.d7Pull_OmegaCube_succ_subset (F) (hnn) (H) (hk : k + 1 ≤ K) :
    d7Pull F (k + 1) (OmegaCube H (k + 1)) ⊆ d7Pull F k (H.omegaPost k)
theorem RegionHistory.le_d7SizeAt_of_reach (F) (hnn) (H) (hk : k + 1 ≤ K)
    (hX : X ∈ bdryDomsAt F k (H.omegaPost k) (H.step k).Z)
    (hmeet : (d7Pull F k X ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty) :
    (S.L : ℝ) * (⌊R k⌋₊ + 2) ≤ d7SizeAt F k (H.omegaPost k) X
theorem Def7.FineValidAt.dmodOmega (F) (hnn) (hkK : k ≤ K) (h : FineValidAt F k Om Y) : DmodOmega Om Y
```

**The split** (LFR Lemma IV.1.5: three kinds with constants of rows 0–11, `B_st` their sum). `LFBdrySplit Λ` (a map,
like `Λ`: `LFBdryPieces` = `new`, `delta`, `old` with `Λ.B = new + delta + old` on every torus; inhabited) and
`LFBdryPart` (the statement of `LFBdryInput` with the boundary terms replaced by one kind and the constant `fac`):

| part | statement | source | status | rem | R |
|---|---|---|---|--:|:-:|
| (i) `LFBdryNewInput` | `D7Bdry` of `new` with `Bn` | P5 Props 3.1–3.4, P6 Props 2.1–2.3; P6 p. 15 | O — the labels `Ŷ(S)` of the marked expansion are R11 labels (`djModFin_Yhat`) | 400 | M |
| (ii) `LFBdryDeltaInput` | `D7Bdry` of `delta` with `Bd` | Lemma IV.1.3 (FLUCTUATION Thm 4.2, landed `theorem42_late_of_input`) | O — labels `Ŷ(T)` as in (i) | 300 | M |
| (iii) `LFBdryOldInput` | `D7Bdry` of `old` with `Bo` | Lemma IV.1.5 (iii); P6 (4.32)–(4.34); P3 (4.41)–(4.49) | Rd — bound by `norm_sum_le_of_transfer`; `hsize` (blocker 3) proved under R11 | 400 | H → M |

`lfBdryInput_of_parts` is the assembly (additivity `D7Bdry.add_B`, `D7Bdry.mono_fac`).

**Blocker 3 (route decision, W1140).** The obstruction is the π′-shape that `FineValidAt` (via `Fluctuation.DjMod`) asks
at the hole sites of every label. A transferred old label must contain every new hole it meets (`loc_hist`); a new hole
need not be a union of π′_{k+1}-cubes (seam, ALIGNED (23)–(26)); every landed label containing it then contains active
sites along the seam (`spill_of_defect`) and its size grows with the seam (`G1_cellCount`), with no decay of an
H7-admissible constant coefficient to pay it (ALIGNED (33)). The same holds for kinds (i), (ii) at `Ŷ(S)`. Routes:
(i) a property of the P6 construction — refuted for the class (the constant coefficient re-expands to itself);
(ii) a stronger H7 — refuted (the spill is created by the next scale's hole; also hits (i), (ii)); (iii) route B —
removes the spill but breaks the domain entropy (G2) (`G2_X`, `D7GasRootEntropy`) unless the size charges hole sites,
which re-indexes `Ŷ(S)` and the gas cores. **R11** (PLAN-B; APPLIED by W1148: `FineValidAt` is `Fluctuation.DjModFin` at the fine sets; the entropy core is `G2_XFin`, the size growth core `dcovMod_le_add_of_piCubesAt`): `FineValidAt := DjModFin` (π′-cubes at the active sites
only; size, `loc_hist`, H7 domain unchanged). Under R11 the transfer of every label across every new hole is proved
(`Def7.exists_transfer_fineValidAt`: `d_{k+1}(Y) ≤ L⁻¹ d_k(X)`; marks `transfer_patches`: `+ 2dL` per patch); in
the former class (`Fluctuation.DjMod`) only for π′-open new holes (`Def7.exists_transfer_djMod_of_open`).

**Leaves of (iii)** (each ≤ 300 lines; none involves a new hole once R11 is in):
* O1 `old_reexpansion`: the old part at a label is the finite sum over assignments (old label `X'`, marks `J`) of P6
  (4.32)–(4.34), with `‖T‖ ≤ C_re B₀ e^{-κ d_k(X')} e^{-κ_m |J|}` (the record's `D7BdryPost.bound` and the P3 mark
  factor) and output label the transfer of `X'` with its patches; structural clauses (locality, `loc_hist`, reality,
  analyticity, O(N), covariance: average over the optimal covers of `X'`, which form a covariant finite set). The
  analytic engine is the one of kind (i).
* O2 **PROVED** (`RegionHistory.d7Pull_OmegaCube_succ_subset`): `d7Pull F (k+1) (OmegaCube H (k+1)) ⊆
  d7Pull F k (H.omegaPost k)` (P5 (2.3): the opening misses `nbhd (U'_k)`, `(Ω_k^post)^c ⊆ Z_k`).
* O3 cube level **PROVED** (`Def7.FineValidAt.dmodOmega`: an R11 label is a cube-level `DmodOmega`); open: which
  transferred labels meet `Z^pre_{k+1}` and its complement (the others go to `b_k`, LFR Lemma IV.1.3) — part of O1.
* O4 **PROVED** (`RegionHistory.le_d7SizeAt_of_reach`): an old post-`R` label whose fine set meets the new region has
  `d7SizeAt ≥ L(⌊R_k⌋ + 2)` (exit of a hole `DmodOmega.exists_active_near`, `dcovMod_ge_supDist`); `hmin`, with (Λ28)
  `B₀ e^{-(κ/2) L(⌊R_k⌋+2)} ≤ 1` for `hB₀min`.
* O5 `assign_entropy`: `hent` from (G2) over the R11 labels (`G2_XFin`, landed with R11) and the mark count of P3 (4.49).
* **Status of O1 and O5 (W1148, 2026-10-20): not provable as stated; the obstruction is the interface, not the geometry.**
  `LFBdryOldInput` is a statement about the parameters `Λ : LFStepMap` and `Sb : LFBdrySplit Λ`. In `LFStepRaw` the
  boundary terms `B` are a bare field (`B : ∀ nK, BTerms …`), and `LFBdryPieces` constrains `old` only by
  `sum_eq : D.B = new + delta + old`. Nothing in Lean ties `Sb.old` to the old boundary terms of the record `rec`, to a
  re-expansion over assignments `(X′, J)`, or to the fluctuation integral. For the split `new = delta = 0`,
  `old = D.B` the statement `LFBdryOldInput` is the whole of `LFBdryInput` for `Λ`; for an arbitrary `Λ` it is false
  (take `B` large). So O1 cannot be proved from `norm_sum_le_of_transfer`, the transfer lemmas and `G2_XFin`: the
  hypotheses `hT` (the bound P6 (4.34) of each assignment), `hsize` (the transfer with patches) and `hent` are about
  objects that do not exist as definitions: the assignment set at an output label, the coefficient `T a` of an
  assignment (the old term integrated against the marked expansion, P3 (4.41)–(4.48)), and the identification of
  `Sb.old` with their sum.
  What is proved and usable: the geometry (`exists_transfer_fineValidAt` for `hsize` with `m(a) = 0`, `transfer_patches` for
  patches, `le_d7SizeAt_of_reach` for `hmin`, `norm_sum_le_of_transfer` for the ledger) and the entropy core `G2_XFin`
  for `hent` (the sum over the old labels `X′` containing a root cell of `Y`: at most `#roots · K₀`, `#roots ≤ c₁(1 + Dp)`
  by `DjModFin.cellCount_le`, which costs a factor `(1 + Dp)` absorbed by lowering `κ_o`).
  To close (iii) the following definitions are needed first (each a source definition, none a step of a proof):
  (a) the old part of the step's boundary terms as a defined object: for the record's term `ℬ^{(k)}(X′)` the coefficient of
  the re-expansion at an output label `Y`, `old B Y = ∑_{(X′, J) ↦ Y} T(X′, J)`, with `T` the P6 (4.32) integral;
  (b) `Λ.B` defined by `new + delta + old` (so that `sum_eq` is a theorem, not a field); (c) the assignment set and its
  transfer map (`transferLabel` with the optimal cover and the mark patches, a choice made covariantly).
  Then O1 is the estimate P6 (4.34) for `T`, which is analytic (the fluctuation machinery of `Fluctuation/StepActivity*`,
  `ClassOldTerm*`), and O5 is the counting above.
* **Status after W1154 (2026-10-21): O2–O5 and the geometry of O1 PROVED** (`Spine/LFBdryOldEntropy.lean`,
  `Spine/LFBdryOldAssign.lean`; axioms `propext, Classical.choice, Quot.sound`). Definitions: the assignments
  `Def7.oldAssign F H k` (old post-`R` boundary domain `X` meeting `Ω_{k+1}`, an optimal cover `𝒦 ∈ optCovers`, rooted
  patches `J`), the output label `assignOut` (= `transferCubes`, the transfer label of `𝒦 ∪ J`), the weight
  `assignWt = 1/#optCovers` (covariant average over the optimal covers). Proved: `oldAssign_spec` (validity of `X` and of
  the output, `X ⊆ Y`, patches, `d_{k+1}(Y) ≤ d_k(X)/L + c_G|J|`, O4 `d_k(X) ≥ L(⌊R_k⌋+2)`); O3 `assignOut_meets_Zpre`,
  `assignOut_mem_bdryDomsAt_iff` (an output is a boundary domain at `k+1` iff it meets `(Z^pre_{k+1})^c`); O5
  `sum_exp_oldIn_le`, `card_patchesIn_le`, `sum_exp_assign_le` (`assignEnt`), `assignEnt_le_exp`; and the per-label
  bound `norm_sum_oldAssign_fiber_le`: for any coefficients `T` on the fiber of `Y` with
  `‖T a‖ ≤ assignWt · C_re B₀ e^{-κ d_k(X)} e^{-κ_m |J|}` (hT), `‖∑ T‖ ≤ C_re · assignEnt(…) · e^{-κ_o d_{k+1}(Y)}`, the
  other hypotheses being the constant conditions `κ/2 - κ_o/L ≥ a_ent + 1` and (Λ28).
  **Open: O1 proper** — the coefficient `T(X, 𝒦, J)` and its bound hT. The old part of `ℬ^{(k+1)}` is FLUCTUATION
  Theorem 3.1 (c) (P5 (2.48), (3.2)): `∫₀¹ du ⟨ℬ''^{(k)}(ψ^{(k)}_loc(θ) + β_k^{-1/2} C^{(k)1/2}_loc ψ̂)⟩''_u`, which needs
  (1) the composed field (the map from the scale-`(k+1)` multiscale field to the scale-`k` one on `Ω_{k+1}`: at scale `k+1`
  the H7 domain leaves `ψ_k` free on `Ω_{k+1}` away from the collar, so no identity transport is bounded), (2) the
  measure of the step with holes (`Fluctuation.StepSetting` is the whole-lattice step; `Thm31cde.lean`), (3) the bound
  (Vmod) of each old term, conditional on OPEN-H7-MIXED, OPEN-P6-X1-INSTANTIATION, OPEN-P6-ACTIVE-COMPOSITE-LOC and the
  common-cover I-4a theorem (VMOD.md §1.4, VMOD-39). P6 (4.33) is the localized interaction: the step's terms are at the
  cluster labels `Ŷ(S) ⊇ Y₀` of Theorem 3.4; the landed assignments are the `Y₀` layer.
* **Status after W1154 pieces 2–3 (2026-10-21): the step with holes DEFINED with characterizations** (readings HS-1,
  OPEN-P6-X1-INSTANTIATION, OPEN-P6-ACTIVE-COMPOSITE-LOC, OPEN-H7-MIXED recorded in `PLAN-B.md`). Core (any
  `Fluctuation.HoleStep`, the whole-lattice `StepSetting` is the instance `toHole`, rfl lemmas): the composed field of P5
  (2.39) `HoleStep.composed` (decoupled background and covariance root of the pair (C, G′) at the localization vectors
  `slocOf`), the measure `nuIn`, the exponent `expW`, `avgOld`, `oldTotal` (= `∫₀¹ ⟨ℬ''⟩''_u`), `partFun_one_eq_mul_exp_oldTotal`
  (`HoleStepMeasure`); the coefficient `T(X, J) = oldCoef` (Lemma AE `coef` of the interpolated old term `oldInterp`),
  `sum_oldCoef_eq_of_analytic`, `oldCoef_eq_zero_of_core`, `oldCoef_eq_zero_of_far` (`HoleStepOldCoef`); the block
  structure `prodSplit` and Theorem 3.1 (c) on a region `oldTotal_eq_sum_of_marks`, `oldBOut`, `oldTotal_eq_sum_oldBOut`,
  `norm_oldBOut_le` (`HoleStepSplit`, through the region-general `Thm31cdeOn`: `ProdSplitOn`, `InterpMarksOn`,
  `interpAvg_eq_sum_interpTermOn`). History instance (`Spine/LFHoleStep*`, `Spine/LFOldCoef`): `holeStepLF` (θ = z ψ_{k+1}),
  `composedMulti`, `phiLF` (log of the integrand of (2.16): `logKernelC` + the holomorphic `𝒜_k + ℱ_k + ℛ^{(k)}`,
  `LargeField/Def7SmallFieldC`; `stepKernel_mul_sfFactor`), `oldDoms`, `oldLF`, `locSloc` (R_{k+1}(□′) = `locDomC`),
  `expWLF`, `oldTotalLF`, `oldCoefLF` (core: the `r`-collar of `X ∩ Ω_{k+1}`, `collarCoreC`). **(i) OPEN-P6-ACTIVE-
  COMPOSITE-LOC under reading HS-1 PROVED** (`Fluctuation/HoleStepActComp`, `HoleStepPointLocal`, `HoleStepOldLocal`: the active
  closure and its block hull; the composed field at a unit point agrees for two localization vectors with the same factors on
  the closure, `composed_eq_of_hull`, from `Dec2.decBg_component_cross` and `Dec2.localLift_eq_localLift_on_component`
  for (`coverOf` G′, G′) with itself; (AE2) `oldInterp_localityAEOn`, `oldCoef_eq_zero_of_not_reached`,
  `oldCoef_congr_of_agreeReach`); history instance `Spine/LFOldLocal.lean` `oldCoefLF_eq_zero_of_not_reached` with every
  geometric hypothesis proved and the standing conditions from the datum in the chart (`standing_of_xiCData`,
  `p6TopC_coverBase`). **Remaining for O1:** (ii) OPEN-H7-MIXED (the
  image of the target H7 domain and the polydisc in the source H7 domain; gives `hana` of `sum_oldCoef_eq_of_analytic`
  and the standing bounds); (iii) Proposition 3.3 on the region (`InterpMarksOn` for `expWLF`: the localization of the
  exponent, as for the whole lattice); (iv) the frame bridge between the cover torus of the step and the D7 frame
  (labels `Ŷ(S)` ↦ `Finset (Torus d n_{k+1})`) and the assembly of `old` as `BTerms`, then the (D7) clauses.
* **Status after W1154 pieces 4n–5 (2026-10-21): reading HS-1′ (the coefficient on the local pair, `PLAN-B.md`).**
  Under HS-1 the composite is `Dec2.decBgField` of the global pair, so (D7) `loc_field`/`analytic` cannot hold for the
  re-expanded terms (H7(Y) constrains only the cubes of Y); HS-1′ computes `T(X, J)` on the restriction of
  (`coverOf` G′, G′) to `𝔹_{k+1}(V(X, J))`. Landed pieces: `Spine/LFOldRead` (`oldTermLF_congr_of_locField`: the field
  locality `hB` of the old term from (D7) `loc_field`); `Spine/LFOldH7` (`deltaC_stencil`, `deltaPrimeC_stencil`,
  `h7Domain_composedMulti_of_inner`: **the transfer part of OPEN-H7-MIXED PROVED** — every condition of the source H7 domain
  at X that does not read the composed field near Ω_{k+1} follows from the target domain at Y ⊇ X);
  `Fluctuation/HoleStepLocal` (`GeneratingSet.inter`, `HoleStep.restrict`); `Spine/LFHoleStepLoc` (`locB`, `holeStepLoc`,
  cover bases of the local pair); `Spine/LFOldLocCoef` (`locSetXJ`, `oldCoefLoc`, the Cauchy bound `norm_oldCoefLoc_le`);
  `Spine/LFOldH7Loc` (`h7Domain_composedMulti_loc`); `Spine/LFOldMarkBound` (`norm_oldInterp_loc_lt`: at every parameter
  of the polydisc the interpolated old term of the local pair is below the record's `fac e^{-rate d^cov(X)}`, from the
  record's (D7) and `H7MixedInnerLoc`); `Fluctuation/HoleStepAnalytic` (`Dec2.analyticOnNhd_decBg`,
  `HoleStep.analyticAt_composed`, `HoleStep.analyticOnNhd_oldInterp`: the composed field and the interpolated old term are
  analytic in the parameters, I-4b (i) and I-4c (iii)); `Spine/LFOldCoefBound` (**`norm_oldCoefLoc_le_of_inputs`: the
  bound of P6 (4.34) at one coefficient, `|T(X, J)| ≤ fac e^{-rate d^cov(X)} e^{-(κ₁-1)|J_V|}`**, from the record's (D7),
  the standing conditions of the local pair and the two named inputs). **Named inputs (open):**
  - `H7MixedInnerLoc` — the composed field of the local pair lies in Δ^c_k(□; 1, ε_k) at the cubes □ ⊂ X near Ω_{k+1}
    (P5 (2.39)–(2.43): composition identity, locality of the background between `genCube` and the local pair, the
    fluctuation bound and the room ε_{k+1} → ε_k; size: the large-field analogue of W1146's `d2raw_*_mem_xiDom` chain);
  - `H7MixedDatumLoc` — the datum of the local pair lies in Ψ̃^c(G′_V; δ_b, δ_b) (patching the per-cube decompositions of
    RegC into one real slowly varying field on V; size: medium);
  - Proposition 3.3 on a region (the localized exponent of the measure of the step, `InterpMarksOn` minus the marks):
    still to be stated.
  Next: the marks (the coefficients as functions of the cube variables of the measure, with the bound above), Proposition
  3.3 on a region as a named input, `oldB` as `BTerms` (grouped by output label, with the assignments of
  `Spine/LFBdryOldAssign`) and its (D7) clauses, and the bound P6 (4.34) at one output label.

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
     W1111, W1112 (`Spine/InheritedBound.lean`): (a), (b), (c) proved; `inheritedBoundInput_of_prefix : PrefixInput → InheritedBoundInput`. The `BgHyp` mass cap
     `ν_j L^{2(k-j)} ≤ 1` at `k = k̂_f` follows from (I.2) and the class bound `ν_k ≤ 9/10` (`physMass_cap_of_top`: `δ_j ≤ e^{1/10} δ_k ≤ 10/9 δ_k`);
     `3 ≤ d` and `bgR0 d L ≤ ϱ` are clauses of `PrefixInput`.
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
     W1113 (`Spine/InheritedAgreeGeom.lean`, `Spine/InheritedAgree.lean`): (a), (b), (c) proved; `inheritedAgreeInput` is unconditional (needs only `FlatRep`: `D8SF.M_eq`, `SFFlat2` locality, `Geo.hc` for `M ≥ 14`).
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
   * **W1151 (A6-3 (a), the empty cut as the core over the cut).** Landed:
     `Green/FinalGaussBochner.lean` (`pd_withDensity_eq_map`, `integral_pd_gaussian_change`: `∫ F(v) e^{-Q_K(v)/2} dv = Z_K ∫ F(K^{-1/2}ψ) dγ` for
     every measurable complex `F`, no integrability hypothesis); `Green/FinalSpinCurry.lean` (`spinField`: fields of `N`-vectors as real fields on
     `blocks × Fin N`, measure preserving, `integral_spinField`); `Spine/FinalSfGauss.lean` (`integral_sfFactor2_gauss`: for every cut `Y`, every positive
     definite `Kq` on `blocks × Fin N` and centre `ψ₀`, `∫ sfFactor2 C vc Y = Z_Kq ∫ sfGaussIntegrand dγ`, `sfGaussIntegrand = sfFactor2(ψ₀ + Kq^{-1/2}w)·e^{Q_Kq(Kq^{-1/2}w)/2}`;
     `sfIntegral_eq_gauss` is `Y = univ`; measurability of `ψ ↦ sfFactor2` is a hypothesis); `Spine/FinalSfUniv.lean` (`EresJ2_univ`, `EresK2_univ`: `F_{k_f} = Σ_{j≤k} Edens` of
     Def-6 at `ψ^{(j)}_k`, minus the full double sum `corrSum`; `Fres_univ`: `⟨g,φ̄⟩ + Σ_j Floc`; `Rres_univ`).
     **Landed (P1, `Spine/FinalSfConst.lean`).** `phiK_const`, `phiBar_const_univ` (`φ̄_k ≡ h` on the torus for `ψ_k ≡ h`, `|h| = 1`), `actStar2_const_univ` (`A*_k(univ; h) = 0`, i.e. `V(h·1) = 0`). Edens at the constant field is not shown to vanish (no translation covariance of `E` on a finite torus in `Def6`); per the coordinator the constant value `Σ_j Edens(ψ ≡ h)` is field-independent and is carried into the vacuum term `E` of `Ξ^sf`.
     **Landed (P1b-P1d).** `Spine/FinalValue.lean`: `value_quadratic_limit(_mass)` (exact Lagrangian expansion `actionC_const_line`, `theorem72_linearResponse`; `V(t)/t² → A(E,0) − ½⟨φ̇,Ṡ⟩ [+ ½(ν'−ν)⟨φ̇,φ̇⟩]`). `Spine/FinalValueBridge.lean`: `actStar2_univ_eq_actionC`, `actStar2_univ_second_variation` (real part of `secondVariation` along `ψ_k = h + t u`). `Spine/FinalHessianAlg.lean`, `FinalHessianBridge.lean`: `second_variation_quad`, `secondVariation_top`, `actStar2_univ_hessian`: for equal action/background masses, `A*_k(univ; h + t u)/t² → ½ L^{k(d−2)} ⟨U, finalHessian_{ν L^{2k}, a_k, h} U⟩`. Open: the cubic remainder as an analytic function on a polydisc (PHYS-CUBIC localization), `muAct = muBg` at the final scale (otherwise the extra term `½(ν'−ν)|φ̇|²`).
     **Landed (P1e, P2, P3).** `Spine/FinalChart.lean`: `constUnitBg_xiCData` (`hθ` at the physical point: the constant unit datum is in `Ξ^c_n(𝔹; σ, ε)` for all `n`, `σ, ε > 0`; the late-scale parent-domain lemma for `χ_Y ≠ 0` already exists as `LateParentR3.inPsiTilde_genW_of_late_chiY_local`). `Spine/FinalConstField.lean`: `composeField_const`, `psiJ_const_univ` (`ψ^{(j)}_k ≡ h`), `Fres_const_univ` (`ℱ_k = ⟨g,h⟩ + Σ_j Floc` at the constant field), `EresK2_const_univ`. `Spine/FinalChain.lean`: `sfGaussIntegrand_eq` (for every cut `Y`), `sfGaussIntegrand_cubic` (for `K = β_k H`: exponent `= −β_k V³ + ℰ_k − E_k|Y| + ℱ_k + ℛ^{(k)}`, `V³ = A*_k − ½⟨v,Hv⟩`). **Open for A6-3 (a):** (i) the cubic remainder `V³ = O(|δ|³)` uniformly in the volume (PHYS-CUBIC localization; a per-torus analytic statement is available in principle from the analyticity of `bgFieldC` but has constants growing with the number of blocks); (ii) the polymer expansion of `exp(−β V³ + …)` over the box with the cut (the landed `cutoffInteraction_final_*`); (iii) the source part: the first-order response `φ̇ = (H⁻¹−Π)Ṡ` of `φ̄_k` is `const_response`, the Gaussian average of `exp⟨g, φ̇ δ⟩` gives the quadratic-in-`g` scale-`(k+1)` term; (iv) (c), (e).
     **Findings.** (C) `corrSum` vanishes on the whole torus only for symmetric coefficients (`EresJ2_univ_of_symm`; `corrSum_self_eq_zero`); `CorrCoef`/`D1CorrLim` do not
     state `vc.v1 j (-z) = vc.v1 j z` (same for `v2`), and without it `Ares2` at `Y = univ` carries the extra term `-corrSum`, a nonzero translation-invariant quadratic form in `ψ`
     (it would shift the Hessian). (D) The cutoff: `chiY` is the product of `Reg` conditions (`|ψ_y − ψ_{y'}| < δ`, `||ψ_y|²−1| < δ`, directional clauses) — a region in the
     `ψ`-space, sandwiched between `w`-boxes but not a `w`-box; the landed pipeline (`cutoffInteraction_final_*`, `norm_coef_cutoff_class_le_levels`) integrates over the box
     `∀ y, |ψ' y| ≤ pLog` of the Gaussian variable, so `sfIntegral` equals the model integral only up to `∫_{Reg ∖ box}`, which is a tail of Gaussian size but not a localized
     analytic term (decision needed: define the small-field class by the box in the Gaussian variable, or treat `Reg ∖ box` as tail gas as in `FinalTail*`). (E) The main action
     `−β₀ actStar` is not quadratic in `ψ_k`: `φ̄` is the unit-sphere minimizer. The Hessian at `ψ ≡ h` is `finalHessian` by `linearResponse` (`Background/LinearResponse`) and
     the envelope formula `V' = ⟨ψ − Qφ̄, aδ⟩`, `V'' = a − aQ(G − Π)Q*a`; the cubic part `V³` of the value function (analytic by `theorem52_analytic`) belongs to the interaction
     (DAPHYS PHYS-CUBIC), it is not in `F_{k_f} = Σ Edens`. Next pieces, in order: (P1) `V(h1) = 0`, `φ̄(h1) = h` (`bgFieldC_eq`, `ConstantConfig`), `Hess V = finalHessian` and
     `V³ = O(|δ|³)` on a polydisc; (P2) `hθ`/the datum lemma beyond `k₀`; (P3) the chain `sfFactor2 → ∫ over box of exp(F∘Λ)` with the cut `Y`.
   * **W1151s (A6-3 item 1 and the assembly).** Landed (`Spine/FinalDom*`, `FinalSf*`, `FinalNumerics`):
     * *Birth-domain transport on the `χ`-support, cut `Y = univ`.* `FinalDomCore` (`AllSitesBounds`, `inPsiTilde_of_allSites`, `xiDom_of_allSites`: a real field constant on the
       `j`-blocks with the bounds R1, R2, R3 at every site lies in `Ψ̃(𝔹; η)` and, for `(2K₁+2)η ≤ ε`, in `Ξ^c_j(𝔹; 1, ε)` for every generating set with empty layers above `j`);
       `FinalDomLevel` (`inPsiTilde_genW_univ_late`: on `χ_univ ≠ 0` at a scale with physical cube mass the level-`k` datum is in `Ψ̃(𝔹_k; 4(d+1)δ_k)`, no region history);
       `FinalDomCompose` (`inPsiTilde_composeField_bgFieldC`: Theorem 7.3 with the explicit radius `C₄K₁η`); `FinalDomPsiJ` (`psiJ_allSites`, `psiJ_xiDom`: the inherited field
       `ψ^{(j)}_k` of the whole torus is real, satisfies the bounds at every site, and lies in `XiDom` of every polymer chart `𝔹_j(X)`; `sfLiftK_xiDom`: the level-`k` lift lies in the domain of
       `ℛ^{(k)}_n`).
     * *Measurability and integrability.* `FinalSfCont` (continuity of `φ_k`, `φ̄_k`, `ψ^{(j)}_k` in `ψ_k` on the real domain, `contOn_bg`), `FinalSfChi` (`measurable_chiY`),
       `FinalSfMeas` (`measurable_sfFactor2_univ_of_dom`: Borel on the support, `0` off it), `FinalSfBound` (`exists_bound_sfFactor2`; `measInt_sfFactor2_univ_of_dom`),
       `FinalNumerics` (`delta_le_geom`, `exists_beta_delta_le`: `Γ δ_k ≤ min(c, α₀ (L^{-α})^k)` for `β` large, uniformly in `k`), `FinalSfDomain` (`measInt_sfFactor2_univ_of_delta_le`),
       `FinalSfIntegrable` (**`measInt_sfFactor2_of_flatRep`**: for `β ≥ β₀(κ, c₉)`, every member of `ℛ♭_k` at the stopping scale `ν_k L² > 7/8`, every torus and `g` in the unit `ℓ¹` ball:
       `BgHyp` of the cube, `sfFactor2 C vc univ` Borel and integrable in `ψ_k`). Typing premise added: `hsep : bgR0 d L ≤ 5 L M₁ = minSep L M₁` (separation of the cube generating
       sets; `PrefixInput` has `M₁ ≥ 1` only). `kZero_lt_of_stop`: `k₀ < k` at the stopping scale for `β ≥ 2L`.
     * *Assembly.* `FinalSfConstTerm` (`sum_inhObs_eq_Floc`, `const_exponent`: at `ψ_k ≡ h` the exponent `𝒜_k + ℱ_k` is the vacuum term `ℰ_k(h) − E_k|T|_k`, `⟨g, h⟩` and `Σ_j Σ_X q_j`),
       `FinalSfAssemble` (`finalSmallFieldInput_of_gaussForm`: `FinalSfGaussInput → FinalSmallFieldInput`), `FinalSfFluct` (**`finalSmallFieldInput_of_fluctForm`**: `FinalSfFluctInput →
       FinalSmallFieldInput`). `FinalSfFluctInput` is the exact remaining statement: for a member of `ℛ♭_k` at the stopping scale there are scale-`(k+1)` activities `a`
       (`ObservableActivitiesAt`, including the two-torus agreement) and a vacuum term `E` with `Z_K ∫ sfGaussIntegrand(centre h) · exp(−(𝒜_k + ℱ_k)(h)) dγ = exp(E + Σ_X a)`.
       Its content: (i) PHYS-CUBIC (`V³ = A*_k − ½⟨v, Hv⟩` volume uniform and localized, isolated by `sfGaussIntegrand_cubic`); (ii) the polymer expansion with the cut `χ_k`
       (`cutoffInteraction_final_*`, `abstract_expansion_taggedCfin_final`; the Gaussian average of the source's first-order response, `gauss_source_linear`; the regrouping and
       amplitude, `regroup_observableActivities`, `amplitude_split`); (iii) the exact two-torus agreement of `a` (blocker 7).
     * **Statements that are false as stated, to be repaired in `PrefixInput`:** `FinalSmallFieldInput` (and `FinalSfFluctInput`) needs `0 < C7.A0`: for `A₀ ≤ 0` the tolerance
       `δ_k = deltaRun A₀ … ≤ 0`, `χ_k ≡ 0`, `sfIntegral = 0` (`sfFactor2_univ_eq_zero_of_not_pos`) while the right side is an exponential. Also `bgR0 d L ≤ minSep L M₁` (above).
     * **Not done (genuine open point): A4-1i for the class (`FrozenIntegrableInput`) and any cut `Y = Z^c ≠ univ`.** The transport above uses that every site is over `Y`. For a cut,
       the chart of `𝔹_j(X)`, `X ⊂ Y^≈`, needs the regional statements of `Q13-COMPOSED.md` (`CanonicalPrecedes`, `RegionalLocalPairAgreement`, `ParentDomainFromFactors` for the retained
       components) and the integrability of the operator integrals `gOp` (PkgBound (1.26)).

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
   * **W1151 (A6-4 (a)(b)).** Landed, `Spine/FinalRepGroup.lean` (exact, from `D1Form2`, no new operator): `lastRegion A k = Z_k(𝔸)` as
     a finite set of cubes; `lastHistInt` (`∫ postTerm2 dψ_k` of one history); `lastRegionWeight Z` (sum over the histories of the representation
     with region `Z`); `integral_eq_sum_lastRegionWeight : ∫ρ = Σ_Z lastRegionWeight Z` under integrability of the terms; `postTerm2_of_region_empty`
     (no component, no boundary domain: the term is `sfFactor2 univ`); `lastRegionWeight_empty = n₀ • ∫ sfFactor2 univ` and
     `lastRegionWeight_empty_eq_sfIntegral` when `n₀ = 1`.
     **Finding (n₀).** `n₀ := #{A ∈ hist : Z_k(A) = ∅}`. The set `hist` is complete for `Agree k (k+1)`, which compares the removal records
     `Rem_j`, `j ≤ k`; a history whose earlier components were all removed by `R` has `Z_k = ∅` yet is not the trivial history, and by
     `postTerm2_of_region_empty` contributes the same `sfFactor2 univ` (its boundary domains must meet `Z_k = ∅`). So `∫ρ` contains `n₀ Ξ^sf`
     and `FinalLargeFieldInput` as stated holds only if `n₀ = 1` (or the removal histories are absent for the classes that occur). The class
     clauses (`IsRep2`) do not state `n₀ = 1`; to be decided: either a class clause / an `R`-step theorem that the removal histories
     carry their `R`-output elsewhere, or the representation of the empty region as `n₀ Ξ^sf` with `n₀` counted in the gas.
     **n₀ settled (W1151, `Spine/FinalRepRemoval.lean`).** (a) Yes: `IsComplete k (k+1)` keeps one history per class of `Agree k (k+1)`, which compares
     `P,Q,R,S` of the steps `j < k` and `Rem_j, j ≤ k`; the regions `Z_j, j ≤ k` are functions of these records (`LabHist.Agree.region_eq`). Two global
     histories with `Z_k = ∅` that do not agree therefore give two elements of every complete set with empty region (`two_le_card_empty_region`).
     (b) Each carries `postTerm2 = sfFactor2 C vc univ` with the same `C = F.ctx`, `vc` (`postTerm2_of_region_empty`): `C` is built from `F.sf` and constants,
     `PostComp A k` is empty and `bdryDoms _ ∅ = ∅`, so neither the removed components nor their gas weights enter the term of that history; `ℛ''` is one
     class-level term of `F.sf` and is not summed over histories. (c) n₀ = 1 is not derivable; a landed definition forces n₀ ≥ 2: at the genuine-radii
     witness (`wS`, `k₀ = k_f = T`, horizon `K = T+1`, `RipeRemoval.ripeRemHistory`, the ripe component of `Z^pre_T` removed at `T`, `Z_T = ∅`; against the
     trivial history) every `hist` with `IsComplete T (T+1)` has `2 ≤ #{A : lastRegion A T = ∅}` (`two_le_card_empty_region_ripeRem`). The same holds at
     every `k ≥ T` and for the pre class (`IsComplete k k`, removal at `j < k`). **Consequence:** for `D1Form2` the small-field part of `ρ` is `n₀ · sfFactor2 univ`,
     `n₀ ≥ 2`, while the source has one term whose exponent contains `ℛ''` (P7 (3.28)): the removed alternative must carry the weight `τ` of the removed
     cluster (P7 (3.22)-(3.27), R4), which `postTerm2` does not. **Defect:** `postTerm2`/`integrand2` (`Def7v2Form.lean`) together with `IsComplete`
     (`Def7Hist.lean:144`), `LabHist.Agree` (`Def7Hist.lean:81`). **Proposed change (either):** (i) `D1Form2` sums over classes of `Agree` modulo removal of components
     that do not meet `Z_k` (merge histories with the same post region and the same surviving records; their weights go into `ℛ''`); or (ii) multiply
     `postTerm2 A` by the removed-gas weight `∏_{c removed at scales ≤ k} τ_A(c)` (decorated by the removed members, R4) so that the removed alternatives are not copies of
     `sfFactor2 univ`. Not changed here (rule 3 of the brief); `FinalLargeFieldInput` as stated is false in a parameter range where a ripe removal with `Z_k = ∅` exists.
     **R12 landed (W1151).** `postTerm2` is `0` for a history with a removal record `Rem_j ≠ ∅`, `j ≤ k`, and `postTerm2Raw` (the old term) otherwise (`postTerm2_of_remFree`, `postTerm2_of_rem`). `Spine/FinalRepOne.lean`: `card_remFree_empty_eq_one` (**n₀ = 1**: a complete set of histories has exactly one history with empty region and no removal record; without removal a nonempty region has a nonempty successor, the new cubes lie in `Z^pre`, so removal-free histories with `Z_k = ∅` agree, and the trivial history exists) and `lastRegionWeight_empty_eq_sfIntegral_of_complete` (the weight of the empty region is exactly `sfIntegral = Ξ^sf`). The finding of `n₀ ≥ 2` below is the pre-R12 situation.
     **Landed (W1151, later).** `Green/GaussianMgf.lean`: `pdGaussian_integral_exp_lin` (`∫ e^{Σ a_x w_x} dγ = e^{½Σ a_x²}`), `pdGaussian_integral_exp_lin_sqrtInv` (in `v = K^{-1/2}w`: `e^{½ Jᵀ K⁻¹ J}`). `Spine/FinalSource.lean`: `response_top_mat` (`φ̇ = R u`, `R = (a_k/L^{2k}) Hr⁻¹(1−P_e)Q*`, `responseMat`), `gauss_source_linear` (Gaussian average of the linear part of `⟨g, φ̄_k − h⟩`: `exp(½⟨Rᵀg, K⁻¹ Rᵀg⟩)`, the quadratic-in-`g` scale-`(k+1)` term). `Spine/FinalAmplitude.lean` (amplitude `c₉/4`), `FinalRegroup*.lean` (Y ↦ Ȳ, two-torus agreement), `FinalRepOne.lean` (n₀ = 1, R12). **A4-1i is blocked** at `measurable_sfFactor2`/integrability: on the `χ`-support the composed fields `ψ^{(j)}_k` must lie in `XiDom (Tm.gs j X)` (analyticity of `Tm.E`, `Tm.M`, `Rt` is stated only there, `IsSF.analyticE/M`, `sfDom`); that membership is the birth-domain statement of R6 (`InheritedBound.birthXiDom`), not derivable from the landed clauses, and the `PkgBound` product bound needs it too.
     **Why `𝕋'_{k+1}` is not defined (design obstruction).** In the source `𝕋'_{k+1}(Z_{k+1}, 𝔸')` is not a datum of the class: it is produced by
     (4.2)–(4.9): the decomposition of unity on the layer, the Gaussian integral over the fluctuation of the exterior `Z_{k+1}^c` around the
     `Z_{k+1}`-dependent saddle `ψ_0^{(k)} = Q_k φ_{k,0}` ((4.3)–(4.8), massive problem), leaving an integration over the variables of `Z_{k+1}` only with
     the exterior contributing `exp(E' − E''|Z^c| + F + F' + ΣR_n)(Z^c)` and the boundary terms `B'`. Any Lean definition on the whole carrier is
     the cut version, for every `Z'`, of the analysis of A6-3 (a) (`sfIntegral` as the cut expansion: Gaussian change of variables,
     `det(U+E)/det(U)·J`), which is itself open; and the cluster factorization `cell Z = Q ∏ τ exp(boundary Z)` (`hOperator` of
     `final_large_integral_eq_gasXi_of_factorization`) is the statement that the integrals over distinct components decouple, the content of the
     Z-dependent background (item 18, L4). A split of `FinalLargeFieldInput` into representation, bounds and end needs a canonical gas datum to which
     the bounds refer; a bare `∃` datum with the identity does not pin it (any datum with the right `gasLinkedXi` would do), so the split cannot be
     stated before `𝕋'` exists. Recommended order: (1) A6-3 (a) for a general cut `Y = Z'^c` (the fluctuation integral of `sfFactor2 C vc Y`
     with the `Y`-dependent background; the `Z=∅` case is `sfIntegral`); (2) `𝕋'` as the remaining integral over `ψ_k|_{Z'}`; (3) then
     `∫ρ / Ξ^sf = gasLinkedXi` with `hOperator`, `hBoundary` proved, and (c), (d).

**Strength (watch).** A6-3 pins the inherited part to the class's (H.7) terms at the constant configuration. LastIntegralInput only
asks for some activities, so A6-3 is stronger than strictly needed. This is the form of the source (LFR (IV.4.2), Def. IV.5.2) and the
reading in LastIntegralInput's docstring. If the Lean class's `ℳ^{(j)}` at the constant configuration were not the source object
(open item (a) of A6-1), A6-3 would have to change with it.

## FrozenStepInput sub-inputs (W1114)

**PROVED** (`Balaban/Spine/FrozenStep.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`):
```
theorem frozenStepInput_of_parts (hSF : FrozenSFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hQ : FlowRateInput T P6) : FrozenStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ
```
It follows LFR Thm IV.2.2 (LF-5). The source has **no operation `R`** above `k₀` (clause (c): "no hull, no `R`"), so there is
no frozen analogue of `RInput`: the step is LF-5's small-field half, then the coefficient step. Threshold: that of `hSF`.

1. **`FrozenSFStepInput` (LF-5; LFR Thm IV.2.2 (a)–(f); P5/P6 Thm 4 repaired; P4 Thm 1, FLUCTUATION Thm 5.3, Lemma 2.9 for the
   switch at `k = k₀`).** For `max(k₀,1) ≤ k < k̂_f`, `ρ ∈ FlatClassAt k`, `ν_k L² ≤ 7/8`: `ρ'` in `FlatPreAt (k+1) k X`,
   i.e. `IsRepFlat2` at `k + 1`, `β_0 = β`, `ν_0 = ν`, (I.2) up to `k` only, `LFCoherent`, running mass at the scale `k`
   equal to `ν_k`, and, for `j ≤ k`, `β'_j = β_j`, `ν'_j = ν_j`, `a'_j = a_j` for the representation `F` of the input (W1121; the clause `X` of
   `FlatRepGen` reads `β, ν, a`; the input is stated through the witnesses of `FlatRep`), and `IntegralStep ρ ρ'`. The flow relation (H.6) at `k + 1` is `IsRepFlat2.sfData.coeff`.
   Open: all of it (same status as `SFStepInput`: the small-field step on complete backgrounds; (H6♭) at `K = k̂_f + 1` needs
   LF-2 (ii) truncated at `k + 1`; the R6 birth-mass domains, applied on main, see the ClassStepInput section).
2. **`FlowRateInput`** (reused from `Spine/ClassStep.lean`): `c₈ q ≤ (1 - q)/20`.

Proved inside:
* (I.2) at `k + 1`: `runningHypTo_succ_of_coeffBounds_core` (ClassStep's lemma with the hypothesis `P.Admissible` replaced by
  `γ > 0`, `c₈ > 0`; `runningHypTo_succ_of_coeffBounds` is now its instance), applied at `massOne P6` to `sfData.coeff`;
* the mass bound (D9♭) `ν_{k+1} ≤ 9/10`: `nu_succ_le_of_coeffBounds`. `ν_{k+1} = ν_k L² (1+ξ₃)/(1+ξ₂)` (`Flow.nuSeq`), `|ξ^{(k)}| ≤
  (c₈/4) q^{k+1} ≤ 1/80` from `c₈ q ≤ (1-q)/20`, so `ν_{k+1} ≤ (81/79) ν_k L² ≤ (81/79)(7/8) < 9/10`. `ν_k > 0` from `D9Flat`.

Refactor of a landed definition body: `FlatRep` (`Spine/RootFInputs.lean`) is now `FlatRepGen … k (fun _ _ _ => νk ≤ 9/10)`, where
`FlatRepGen` has the scale `r` of (I.2) and the closing clause `X F.sf.β F.sf.ν F.sf.a` as parameters. `FlatRep` and `FlatClassAt` have the
same statements (defeq), no dependent file changed.

Rule 10: `flatPreAt_witness` (from `flatClassAt_witness` via `FlatClassAt.toFlatPreAt`); `FlowRateInput`: `flowRateInput_of_lower`.
`FrozenSFStepInput` needs the exemption of the seven inputs.

## BaseStepInput sub-inputs (W1110)

**PROVED** (`Balaban/Spine/BaseStep.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`):
```
theorem baseStepInput_of_parts (hP : BasePreStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hR : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ) (hQ : FlowRateInput T P6)
    (hF : BaseFlatStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    BaseStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ
```
It follows LFR Thm II.7.10. The density is the physical one, not an arbitrary member:
`firstDensity d N T β a z₁ ν h kf : 𝒟[d, N, T, β, a, kf + 1, 1]` is the landed `baseRho1` (LFR (II.7.1),
`ρ₁(ψ₁; g) = z₁^{N|T^{(1)}|} ∫ ∏_y t₀(z₁ψ₁(y), (Qφ)(y)) e^{−βH(φ)+⟨g,φ⟩} dσ(φ)`) read on the tori of the family. On the torus `n_K`
the coarse torus is that of the `1`-blocks, side `M n_K L^{K−1}`; the fine source `g : 𝕋_ℓ × {1, …, N} → ℂ`, `ℓ = M n_K L^K`, is
read through `L · M n_K L^{K−1} = ℓ` (`firstDensityAt`, `firstSide_eq`). The kernel constant is `a = cs₀.aKer`; the field
renormalization `z₁ > 0` is existential in the sub-inputs. The threshold is the largest of the three thresholds.

Proved inside:
* `∫ρ₁ dψ₁ = Z(g)` with the constant `1` (LFR Thm II.7.10 (a)): `integral_firstDensityAt`, `integralIsZ_firstDensity`, from the
  landed exact starting identity `basePhysicalDensity`; `IntegralIsZ.of_integral_eq` carries it to a density with the same
  integrals;
* regime (A): (I.2) at the scale `1` from (H.6) at `1` (`PreClassAt.succ`, W1102, with `FlowRateInput`), then `R` at the scale `1`
  (`RInput` at `k = 1`). At the scale `1` no component is ripe (LFR Lemma II.7.2 (c)), so `R` keeps the density; `RInput` asserts
  only a member of `ℛ_1` with the same integral, which the source gives;
* `neZero_of_norm_eq_one` (`N ≥ 1` from the unit field, for `basePhysicalDensity`).

The base step reuses two sub-inputs of the class step (`RInput`, `FlowRateInput`, at `k = 1`); its new sub-inputs are the first step
proper in the two regimes of LFR §II.7.1. They need the exemption of the seven inputs (rule 10): their truth is the open work of
blocker 1. General `d, N` and general constants.

1. **`BasePreStepInput` (A3-1, regime (A), `k₀ ≥ 1`; LFR Def. II.7.6, Lemmas II.7.7, II.7.8, Prop. II.7.9, Thm II.7.10 (b)–(d);
   P4 (2.42)–(2.54); P5 p. 487, (2.47) and P6 (3.2) at `k = 0`).** There are `z₁ > 0` and `ν₁` with
   `PreClassAt … kf 1 0 (firstDensity … (cs₀ κ c₉).aKer z₁ ν h kf) ν₁`: `ρ₁ ∈ ℛ^pre_1` with (I.2) at the scale `0`, `β_0 = β`, `ν_0 = ν`
   and `LFCoherent`. The pre-`R` form is the one in which Prop. II.7.9 states the output (boundary terms with `3κ/2`, `B_st`;
   `ℛ^{(1)}_m ≤ ½β₁^{−m−1}`).
   * Landed (general `d, L`, `LargeField/Base/`):
     * exact identities: `basePhysicalDensity`, `baseFirst_partition_integral`, `baseRho1_eq_sum_firstP`,
       `baseRho1_eq_sum_firstP_conditional_recordInterior`, `baseRetained_disintegrate`, `baseRecord_good_region`,
       `baseChartIntegral_retained`;
     * charts, cut operators and determinants of a record: `baseFirstRecord_inner_pos_of_goodCubes`,
       `baseFirstRecord_chartIntegral_of_goodCubes`, `baseFirstCut_integral_of_posDef`, `baseFirstRecord_cut_posDef_of_goodCubes`,
       `baseFirstRecord_cut_logDet_factorization_of_goodCubes`, `baseFirstCut_multiplier_bound`;
     * the covariance `C^{(0)}`: `baseCovX_bound`, `baseCovX_analytic`, `baseCovX_sqrt`, `baseCovX_log`, `baseCovX_sub_decay`,
       `baseCovX_exact`, `cutXOperator_zero_eq_cutOperator`, `baseOp_shift_mul_constrainedCov`, `baseConstrainedCov_analytic`,
       `baseParametrix_analytic`, `baseDGSetting_exists`;
     * the background: `baseBackground_analytic_localB`, `decBg_one_eq_bgField_of_inDomainR`, `baseSectorDatum_decBg_one`,
       `baseSectorDatum_inDomainR_c7`; the activities of a chart: `baseActivity_LabelAct`;
     * the first components (W981): `baseFirstRecord_weighted_count_of_injectiveCoding`,
       `baseFirstRecord_localRestriction_weighted_count`, `baseFirst_operator_majorant_of_fiveShares`, `baseFirst_budget_ge_p2Run`;
     * the cutoff transfer: `baseCutoffTransfer`, `baseFootprint_margin_of_cutoff_of_bondCross` (named `bondCross`);
     * the R7 carrier `BaseSmallFieldInput` (defined and audited, inhabited only by the zero input), `baseKphys_eq_Kt0_mul_exp`,
       `baseKC_eq_baseK0_mul_exp`, `baseStepData_of_input`.
   * Open (sub-sub-inputs, in the order of the proof of Thm II.7.10):
     * (a) the small-field part (Prop. II.7.9): the small-field data at the scale `1` on `Z^c_1` from the hemisphere charts around the
       background, `C^{(0)}` and the chart Jacobian; in regime (A) the ν-free system (blocker 2); the first fluctuation integral's
       localization and cluster expansion (I-8 at `k = 0`: the step's engine asks `a_k ∈ [1/2, 2]` (`XSetting`, `XCover`), while the
       first step has `a_0 = 0`, and a lower generating set (`FlCore.hPmp`), which does not exist at `k = 0`, BASEPLAN W822, W856;
       the covariance itself is landed through the mass shift of BASEX); (H.5), (H.6) at `1` with one `c₈`; `ℛ^{(1)}_m` (P5 Prop. 3.2
       at `k = 0`); the boundary terms `ℬ^{(1)}`;
     * (b) the base kernels: the R7 carrier populated with `K̃^w_0 e^{b_0}` (with the obligation D4 of BASECARRIER-AUDIT,
       `Kphys^w(g) Kphys^{w'}(0) = Kphys^{w'}(g) Kphys^w(0)`), and the bound (II.7.5) with the gain `κ^{(0)}` (Lemma II.7.8; P5 (1.31)
       for the first components, item 17), with the margin across `∂Ω″` (BASEPLAN T1, the premise `bondCross`);
     * (c) the transform relation (BASECARRIER item T): `D1PreForm2 (F.ctx …) vc (F.lf nK) h (firstDensity …)`, the sum over histories
       of the base kernels times the small-field factor. It needs the localized background, the chart reconstruction, the cutoff
       transfer and the allocation of the action;
     * (d) the frame of the carrier. Ruling R7 specialized it to `M = K = 1` (`Geo S n R 1`, `RegionHistory S n R k0 1`,
       `H.localHistory 1 1 1 Z'`), while the class at the prefix's constants has `M = T.M = c M₁ ≥ 14` (`PrefixInput`) and
       `K = k̂_f + 1 ≥ 2` (`ν L² ≤ 7/8` forces `k̂_f ≥ 1`). No landed map carries the carrier's data into the scale-`0` step data of
       `RepFam … (kf + 1) T.M …`. The carrier must be restated at general `M, K`, or a transport proved, before it can populate
       the class;
     * (e) the budget (H6′)^pre at the scale `1`: `Rep.budgetPre_of_LF2` needs `K ≤ top` and a `BudgetSetup` at every scale, while
       `top = 1` (`D4Pin 1`) and `K ≥ 2`. The truncated counter history of `Rep.budgetFlat_of_LF2_trunc` (`Rep.lf2HypTrunc` with
       `BudgetSetupTo`, W1106) is the model; the base case of the recursion is LFR Lemma II.7.2 (e);
     * (f) (D8) of the base data (Thm II.7.10 (d)): the two-torus agreement of `K₀`, `b₀` and `ℬ^{(1)}`, as for the quiet kernel
       (W1103, W1104: `bgLocPiece_twoTorus`);
     * (g) `β_0 = β`, `ν_0 = ν` (by construction of the running constants).
2. **`BaseFlatStepInput` (A3-2, regime (B), `k₀ = 0`; the same sources with complete backgrounds and P4's system).** There are
   `z₁ > 0` and `ν₁` with `FlatClassAt … kf 1 (firstDensity … (cs₀ κ c₉).aKer z₁ ν h kf) ν₁`.
   * Landed: as for A3-1.
   * Open: (a)–(d), (f), (g) of A3-1 with complete backgrounds from the start (the switch at `0 → 1` is vacuous) and P4's system; the
     budget (H6♭) at the scale `1` at `K = k̂_f + 1` by `Rep.budgetFlat_of_LF2_trunc` (`k₀ = 0 ≤ 1 ≤ k̂_f`, `top = 2`,
     `BudgetSetupTo … 1`), with `S.Good` and (H-λ) `hH1`, `hH2` from the typing conditions of W1106 (`TransferTyping`;
     `exists_good_lamHat`, `hLam_window`).
   * (I.2) at the scale `1` is part of this sub-input, not proved from (H.6) as in regime (A): `FlatRep` fixes (I.2) up to its own
     scale, and a variant with (I.2) up to `r` would copy it. A core `FlatRep … r` with `FlatRep` as its instance belongs to
     `Spine/RootFInputs.lean`, outside this task.
   * The mass bound `ν₁ ≤ 9/10` of the frozen class (W1112, the last conjunct of `FlatRep`) is part of this sub-input, not assumed:
     in the source `ν₁ = νL²δ₁` with `νL² ≤ 7/8` and `δ₁ = (1+ξ₃)/(1+ξ₂) ≤ e^{c_ξ/β}` (Thm II.7.10, (D9♭)), so
     `ν₁ ≤ (7/8)e^{c_ξ/β} ≤ 9/10` for `β ≥ β₀`. Open with (a): the flow `ξ^{(0)}` of the first step and its bound.

**Why the first step is not split further.** The expected pieces (the small-field step, the first large-field component bound,
the assembly with (D8) and `β_0 = β`) are fields of one representation `F` of one density. Sub-inputs asserting the small-field half
for some `𝔰` and the large-field half for some data cannot be combined unless both speak of the same `F`, and no landed operator
constructs the representation of the first step (the R7 carrier is not in the class's frame, (d)). The clause `D2SF2.sfClass` has
its small-field density `ρsf` existential, so only (D1) ties `𝔰` to `ρ₁`, and (D1) involves both halves. A statement "every
representation of `ρ₁` satisfying (D1) has the small-field clauses" would be false, since the split of `ρ₁` into kernels and
small-field factor is not unique. (D8) and `β_0 = β` are likewise properties of the constructed representation; over all
representations of `ρ₁` they fail (audit D1: rescale the boundary terms on one torus). So (a)–(g) are sub-sub-inputs of A3-1 and
A3-2. Each becomes a theorem once the first step's representation is defined at the class's `M, K`.

## KfZeroInput sub-inputs (W1110)

**Superseded by route FR (W1149).** `KfZeroInput` is proved directly by `kfZeroInput_of_typing` (`Spine/KfZeroFRMain.lean`,
`notes/phase1/KF0-FR.md`) under the typing condition `kf0FRs0 d N L κ ≤ M L`. The sector split below (A7-1
`KF0GoodSectorInput` with `KF0ThresholdInput`, A7-2 `KF0BadSectorInput`, the threshold premise) is no longer on the path to
Root-F; the text is kept as the record of that route.

Files left without use by route FR (W1149, 20 October; computed from the constants that `kfZeroInput_of_typing` uses
transitively, and from the import graph). No declaration of the following is used by `kfZeroInput_of_typing`, and no
module outside the sector route imports them: `Spine/KfZero`, `Spine/KfZeroGood`; `LargeField/Base/KF0AllPlusComplex`,
`KF0AllPlusGas`, `KF0AllPlusGasC`, `KF0BadCharge`, `KF0BlockSplit`, `KF0BoundarySquare`, `KF0CollarBudget`,
`KF0CollarClosure`, `KF0F1Assembly`, `KF0GoodChart`, `KF0HaloAffine`, `KF0MeanShell`, `KF0SectorCharge`, `KF0SectorSum`,
`KF0ShiftedSector`, `KF0SmallUniform`, `KF0SqrtReal`, `KF0TaylorMajorant`; `Green/KF0CovarianceAtoms`,
`KF0CovarianceNoise`, `KF0DetWalks`, `KF0HoleWalk`, `KF0HoleWalkTorus`, `KF0KilledWalks`. They are still imported along
route FR's chain only through `Spine/KfZeroAct` (imports `Spine/KfZero`, needs only `RootFInputs`) and
`Spine/KfZeroGoodParts` (route FR uses only `kf0K0`, `kf0K0_ge_log`, `kf0K0_sq` from it). Used by route FR from the
earlier KF0 work: `KfZeroGoodParts` (those three), `KfZeroAct`, `KF0AllGoodGas`, `KF0Gaussian`, `KF0CutoffSplit`,
`KF0PolymerLift`, `KF0BlockLift`, `KF0BoxLift`, `Green/KF0Reference`, `KF0WalkHalo`, `KF0WalkSeries`, `KF0WalkTorus`,
`KF0WalkTruncation`. `KF0GoodGaussian`, `KF0WalkOrdinary` are unused by route FR but imported elsewhere
(`Green/GaussianChangeGeneral`, `Green/KernelSeriesGeneral`).

**PROVED** (`Balaban/Spine/KfZero.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`):
```
theorem kfZeroInput_of_parts (hG : KF0GoodSectorInput d N δ T thr)
    (hB : KF0BadSectorInput d N δ T thr) : KfZeroInput d N δ T
```
for every block threshold `thr : ℝ → ℝ → ℝ → ℝ → ℝ` (`r = thr κ c₉ β ν`; the notes take `r = δ_β = A log(βa)/√(βν)`, now `kf0Thr A a β ν`, W1142). The range premise `_hthr` is restricted to the regime of `KfZeroInput` (`7/8 < νL²`, `ν ≤ 1`, `β ≥ β₀`; it is false for all `ν` as `ν → 0`); `kf0Thr_range` proves `0 < kf0Thr A a β ν ≤ √2` there for `A > 0`, `a > 1`, `L > 0` (`β₀` from `log(βa) ≤ √β/(AL)`, `√2√ν L ≥ 1`), and `kfZeroInput_of_parts_kf0Thr` drops the premise for `thr = kf0Thr (A κ c₉) (a κ c₉)`. The source threshold never exceeds `√2` in the regime once `β ≥ β₀`. It follows
route (A) of `KF0-INFL.md`, hard physical sectors. On an admissible torus (`M L^{kf+1} ∣ ℓ`) the blocks have side `s = M L` (the cubes
of Root-F's scale-`1` polymers), `m = ℓ/(M L)` per side (`exists_blockCount`). A block is good if `|φ_x − h| < r` at all its sites.
`Z_B(g) = kf0Sector (M L) m r β ν h B g` is the sector of the bad set `B`.

Proved inside:
* the sector identity `Z(g) = Σ_B Z_B(g)` (landed `partitionFunction_eq_sum_kf0Sector`, (K0.2));
* the activities `p = a + b` (`actAdd`; the clause lemmas `ActSupportAt.add`, `ActAnalyticAt.add`, `ActLocalAt.add`, `ActBoundAt.add`,
  `ActAgree.add` of `Spine/LastIntegral.lean`), with the amplitudes `c₉/4 + c₉/4`; `E` is the vacuum term of the all-good sector;
* rule 10 for A7-2: for `r > 2` every block is good (`kf0Sector_eq_zero_of_two_lt`), so `KF0BadSectorInput` holds with `b = 0`
  (`kf0BadSectorInput_of_two_lt`). `KF0GoodSectorInput` needs the exemption of the seven inputs.

1. **`KF0GoodSectorInput` (A7-1, the all-good gas; LF-BASE-KF0 Part F.2, Thm F.1, (F.13); KF0.md "ordinary expansion").** There
   * (W1117) `not_kf0GoodSectorInput_of_thr_nonpos` (`Spine/KfZeroGood.lean`): the input is false for a threshold `thr ≤ 0` (the sector is 0), so the provider must supply `thr > 0`; the clauses (a)–(e) below, with the landed `KF0AllGoodGas` items (i)–(v) of its T4, are not derivable from landed results.
   are `a, E` with `ObservableActivities … κ (c₉/2) δ 1 kf a` and, on every admissible torus and the unit ball,
   `Z_∅(g) = exp(E_ℓ + ⟨g,h⟩ + Σ_X a_ℓ(X; g))`.
   * Landed: `block_gas`, `block_gas_hypotheses_d3` (KF0AllGoodGas); `allPlus_gas`, `allPlus_gas_instance`, `blockActivity_abs_le`
     (KF0AllPlusGas); `f1_integrand_eq`, `f1_weighted_small` (KF0F1Assembly, Thm F.1); `kf0_cutoff_good_sites`,
     `kwSqrt_cutoff_good_sites`, `integral_indicator_small_eq`; the walks `kf0Adj_pow_torus_eq`, `kf0CR_torus_eq`, `kf0_lemmaH1`,
     `kf0CovAtom_torus_eq` (`Green/KF0*`).
   * Open:
     * (a) `allPlus_gas` is the Gaussian chart integral with the product cutoff `sup_y |ψ_y| ≤ p` (on which every site is good,
       (F.6)). `Z_∅` has the physical threshold, which is not local in `ψ` (LF-BASE-KF0 E.4). The good sites with a large Gaussian
       variable must be expanded inside the all-good sector, or `Z_∅` expanded in the spin variables;
     * (W1145) items (b)-(e) DONE as lemmas: `Spine/KfZeroGoodParts.lean` (`kf0GoodAct` and its support / locality / analytic (`kf0GoodAct_analytic`) / bound (`kf0GoodAct_bound`, amplitude `c₉/4`) / two-torus agreement (`kf0GoodAct_agree`) clauses, `kf0GoodAct_sum`, `kf0_gas_facts`, `kf0_choose_eps`), `LargeField/Base/KF0AllPlusGasC` (complex source, `kf0PY_analyticOnNhd`), `KF0BoxLift`, `KF0BlockLift`, `KF0PolymerLift` (lifts, `kf0PY_agree`), `Polymer/MayerTransport`, `KF0SmallUniform`. The reduction is the theorem `kf0GoodSectorInput_of_threshold`: `KF0GoodSectorInput` follows from `KF0ThresholdInput` (the new Prop = item (a): activities `r` of amplitude `c₉/4` with `Z_∅ = exp(E₀ + Σ r) · (product-cutoff integral)`) and `M ≥ 3(κ+2κ₀+4)3^d(2d+1)L`. Only (a) is open.
     * (b) [done, see above] the complex source: `allPlus_gas` has a real source `src`; the activities must be analytic on the `ℓ¹` ball;
     * (c) the measurable walk terms with clipping (KF0AllGoodGas, T4 (i)–(ii));
     * (d) the regrouping onto `IsPolymer d ℓ (M L)` and the exact two-torus agreement of the increments (walk lifts, PE (f));
     * (e) the amplitude `c₉/4` (the rate (F.13)).
2. **`KF0BadSectorInput` (A7-2, the bad sectors with the reversed spins as a linked gas; LF-BASE-KF0 Parts D, E, G; KF0-HEAVY,
   KF0-LINK, KF0-ONECORE; `astra/KF0B.md`; P7 (4.11)–(4.14); blocker 1).** There is `b` with
   `ObservableActivities … κ (c₉/2) δ 1 kf b` and `Σ_B Z_B(g) = Z_∅(g) exp(Σ_X b_ℓ(X; g))`.
   * Landed: the sectors (`kf0Sector_iterated`, `energy_split`, `goodEnergy_expand`, `exp_neg_energy_le_peierls`, `kf0SectorLint_eq`,
     `partitionFunction_eq_sum_kwNormRatio`, `kf0SectorLint_le_peierls`, `kf0SectorNorm_peierls_charge`,
     `kf0SectorLint_le_charged_goodIntegral`, `kf0BadFactor_le_gas_charge`); the good chart and the shifted sector
     (`lintegral_goodInner_gaussian`, `lintegral_goodInner_shifted`, `goodReducedConst_ge`); the collars (`mean_outside_collars`,
     `collar_budget_uniform`); the hole walks (`kwTraceDiff_eq_inclExcl`, `kwRootedLoopCount_torus_eq`, `kwOp_inv_sub_trunc_hasSum`);
     the gas theorems (`gasOp_pe`, `gasOp_pe_hole`, `gasLinked_activity_bound`).
   * Open:
     * (a) the heavy objects (`CompleteHeavyLocality`, KF0-HEAVY): bounded heavy functions of finite support on one common product
       reference, with the support-weighted bound (K0.6);
     * (b) the integrated linked hard-chart estimate (KF0-LINK §5, L38.11): the influence of a bad core on the exterior through
       `C_G = K_G^{−1/2}` (KF0-ONECORE);
     * (c) the reversed spins (KF0B): Theorem B.1, the independent-spin reference is not a small-bond expansion; Theorem B.7, the raw
       exact cells are not a singleton gas, so the expansion must be linked (P7 (4.11));
     * (d) the exponentiation with exact lifts and the regrouping onto scale-`1` polymers; the amplitude `c₉/4`.
   * One sub-input, not two. The reversed-spin activity and its linked gas cannot be separated: the only statement between them would
     be "`Σ_{B≠∅} Z_B/Z_∅` is the linked gas of the heavy weights", and no heavy weight is landed (`CompleteHeavyLocality` has no
     producer). A split by hemisphere is definable but separates no open work: the bad cores of KF0-HEAVY have
     `a_Q = max|φ_y − h| ∈ [δ_β, 2]` on both sheets, and the exterior influence of KF0-ONECORE is the same for both.

**Strength.** A7-1 and A7-2 pin the decomposition to the physical sectors at the threshold `thr`; `KfZeroInput` asks only for some
activities. For `r > 2`, A7-2 holds with `b = 0` and A7-1 is `KfZeroInput` at half the amplitude, so the split separates open work
only for small thresholds (the provider's choice `δ_β → 0`). Given A7-1, A7-2 and `KfZeroInput` imply each other up to the
amplitudes (`b = p − a`, the difference of the vacuum terms on `X = ∅`, for a threshold that does not depend on `c₉`), so A7-2 is
plausible exactly when the whole case is. The landed `rootF_kf0_partial_of_oneScaleInput` takes the one-scale input in ratio form,
with `L, M` existential; `KfZeroInput` is that input in absolute form at the prefix's `L, M` (SPINE-AUDIT).

## RInput sub-inputs (W1118)

**PROVED** (`Balaban/Spine/RStep.lean`; no `sorry`; axioms `propext, Classical.choice, Quot.sound`):
```
theorem rInput_of_parts (hV : RVacuumInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hG : RKeptGasInput d N T P6 C7 PB cs₀ M1 c rH ϱ) : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ
```
It follows LFR Thm III.10.8 and Lemma III.8.4 (P7 Thm 2, (1.3)–(1.7), (3.1)–(3.29)) with ruling R4. Threshold: the larger of the two (W1121 merged the kept and gas halves).
`RInput` is stated unchanged; `RStep.lean` edits no existing file but `Balaban.lean`.

**Why two sub-inputs, and why they are existential.** No landed operator constructs the output representation: `Balaban/LargeField/R/` has
the gas, the kernels and the normalizations for abstract carriers, and nothing ties them to `Rep.B`, `Rep.κK`, `Rep.KD`, `Rep.hist`.
So each sub-input is "there are output data with these properties", over the input record. Statements "for all output data
with P, Q holds" would be false: two boundary terms can give the same `ρ'` and only one satisfies (D7); the kept exponent `κK` is part of
the type of the kept data. The output data are therefore produced in stages, and the later stage quantifies over the
earlier one's output under the earlier one's properties (`KeptOutput` includes its coherence).

Carrier: `PreRec …` (new, `Spine/RStep.lean`): the witnesses of `PreClassAt` as fields (`preClassAt_iff : PreClassAt … ↔ Nonempty (PreRec …)`;
`PreClassAt` is `Nonempty PreRec` (W1118)).
The output family is `repFamPost F lf₁ B' Rpp`: small-field data `sfAddRem F.sf Rpp` (`sf + ℛ''`, the other fields of `SFData` unchanged), large-field part
`lf₁` with the boundary terms replaced by `B'`.

0. **`RVacuumInput` (R5, R5′; P6 (3.2), P5 (3.18); LFR proof of Thm IV.1.1).** For `1 ≤ k ≤ k₀`, a record `rec : PreRec … k k ρ νk` is replaced by a record of the same
   `ρ, νk` with `VacuumTied`: for every torus, `StepData.VacuumTie (rec.F.lf nK).SD Set.univ rec.Ev dpp dppp` (the scale-indexed flow, W1125) for some offsets `dpp, dppp` (`δ″_k`, `δ‴_k`, independent of `E_k`).
   The kernels are unchanged (`b⁰_k = b_k + ` the vacuum term of the flow); the content is `StepData.b0_bound` for these constants: `b⁰_k` is bounded by
   `(C_b log β_k + C_b B_0)|Z_{k+1}∖Z_k|_{k+1}` with constants free of `E` (W965 normalization; W968 vacuum). `IsRepPre2` does not carry the tie, hence this
   sub-input; it is a property of the pre-`R` class and uses nothing of `R`.
   * **W1119 (not provable from `PreRec`).** Retying keeps `ker`, sets `vacE := sf.E j` etc., `b0 := b + vacTerm`; then `b0_bound` reads `‖b_k + (E V + δ″ v₂ + δ‴ v₃)‖ ≤ (C_b log β_k + C_b B_0)|Z_{k+1}∖Z_k|`, but `PreRec` carries only `b_bound` for `b_k` and no bound on `E` (`SFData.E : ℕ → ℝ` is indexed by the Def-6 torus `N₁`, the constant `E_k` of the record's one scale `k`; `VacuumTie` reads `E j` at step `j`, so the tie as stated conflates torus index and scale). Needed: a scale-indexed flow `E_j` with `|E_j| ≤ C(log β_j+1)` in the pre-class, or `RVacuumInput` stated on the physical step data (SFStepInput).
   * **W1125 (restated and reduced).** `VacuumTied` reads `rec.Ev`. `Spine/RVacuumTie.lean`: `StepData.retie` (vacuum constants of a flow; `ker` unchanged),
     `PreRec.retie` (all `IsRepPre2` clauses transported: `d5Bound_withSD`, `d1PreForm2_withSD`, `d7Bdry2_withSD`), `rVacuumInput_of_b0 : RVacuumB0Input → RVacuumInput`.
     The remaining named sub-input `RVacuumB0Input`: for every `PreRec` there are torus-independent offsets `dpp dppp` with
     `‖b_k + stepVacuumTerm a k (E_k) (E_k + δ″_k) (E_k + δ‴_k)‖ ≤ (C_b log β_k + C_b B_0)|Z_{k+1}∖Z_k|_{k+1}` (`RecB0Bound`); this needs the volume of the vacuum regions
     against `|Z_{k+1}∖Z_k|` and `|δ″_k|, |δ‴_k| = O(log β_k)` (P4 (2.1), (2.41), (2.63)) besides the flow bound.
   * Landed: `StepData.b_vac`, `stepVacuumTerm`, `stepVacuumVolume` (`stepVacuumVolume_eq_add_excess`), `StepData.VacuumTie`, `VacuumTie.b0_sub_shift`,
     `VacuumTie.removed_weight_shift`, `stepVacuum_removed_*`. Open: the bound of `b⁰_k` at the physical constants (P4 (2.1), (2.41), (2.63), (4.21)).
1. **`RKeptGasInput` (kept half and gas half in one existential; W1121 after the sub-spine audit, defect 1).** `KeptOutput` consists of inequalities
   and does not determine the kept kernels, so a universal gas input over every kept datum is likely false and a separate kept input is
   near trivial. For `1 ≤ k ≤ k₀`, a record `rec : PreRec … k k ρ νk` with `VacuumTied rec`: `∃ lf₁ B' Rpp ρ'` with
   (kept half) one `Rep` per torus with the step data of `rec.F`, histories complete at `(k, k+1)`, and `KeptOutput`: `D4Pin (k+1)`
   (the exponent `κ_k` of a kept component is `κ^pre_k`; OPEN-R-TOP-PIN), `D5Bound (k+1)` (the bound (1.26) of the kept operators `locOp`
   with exponent `κ_k − C_R λ_k^{2d+1} + γ(ϰ)`), `D6Budget` ((H6′) with the kept exponents; (Rg) of LF-2), and `LFCoherent` of the family with these data and
   no boundary terms; and (gas half, LFR Thm III.10.8 (b), (c), Lemma III.8.4; P7 (3.1)–(3.29); ruling R4) `GasOutput` for these `lf₁`.
   * Landed (kept half): `keptKernel_one_kerBound`, `keptKernel_two_kerBound`, `keptKernel_three_kerBound` (the kept outcomes `ϰ = 1, 2, 3`), `Rep.rg_ripe`,
     `Counter` (`CounterConclusion.Gp_ripe`, `flow_counter`), `isComplete_succ_of_enum`, `exists_isComplete`, `pin_succ_of_pin` (`d4Pin_succ_iff`),
     `Rep.budgetPre_of_LF2`.
   * Open (kept half): (e) the kept bounds `ϰ₄`, `ϰ₅` (`hquot`); OPEN-R-HISTORY-ENUM only as far as the new histories must agree with the old ones
     below `k`; the budget (`budget`, strict `k < t*` of the post book);
     `opBound` (`locOp` at `k` uses the kept data `keptOp` at ripe components, `preOpTop` does not).
   Gas half:
   `∃ B' Rpp ρ'` with `GasOutput`: (i) `ℛ''` has `RTermsH4` with the allowance `1/2` at `m = m₀ + m₁` and `0` elsewhere (OPEN-R-RM-H4; P7 (3.28)–(3.29)),
   and `D8SF` (`sfWithRem`: coherent) — `D8SF.R_eq` of `ℛ''` comes from `LFCoherent` of the input (audit D1); (ii) `D1Form2` for `ρ'` on the family `repFamPost`
   (the gas gives the form: OPEN `form`); (iii) `D7Bdry2Post` (OPEN-R-D7-PHYSICAL; the gas activity bound `d7Post_bound_of_avoid_of_gas`
   from the small factor (3.10″) gives its `bound` field; `real`, `analytic`, `loc_field`, `rot`, `support` label by label (`real_of_avoid`, …),
   `loc_hist`, `euclid` and the new gas labels remain); (iv) `LFCoherent` of the output (the boundary clause); (v) `∫ ρ' = ∫ ρ` (P7 (1.7)).
   Sub-sub-inputs, in the order of the proof (none is a Lean hypothesis; all are inside the existential):
   * (a) **the window bound** of the removed histories: `removedKernel_kerBound_of_hid_action_cl` (`hnamedCU`), `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du`, `…_cl`
     cores, `genSet_stability_core`, `removed_kerBound_logC_of_window`. Open: `hnamedC.1` (the ~60 numeric side conditions of Step 1, P7) and the P7
     Q-part of `hnamedC.2` at the physical collar (COLLAR-FIX 1.2);
   * (b) **the small factor** (3.10), pointwise (3.10″) of ruling R4: `lf4R_removed`, `norm_tau_le_of_removed_kernels`, `r4HeavyFamily_bound`,
     `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel`; open for the actual removed operators, and (H-op): hole closure, the two PE
     inequalities, the product measure; also `hosc` (§5.5 of `LF4R-PLAN.md`) and the transport `OutT ↔ BlockField` (§6);
   * (c) **ℬ′** (P7 (3.22)–(3.25)) and the representation as a gas of removed clusters: `RopC`, `rhoSigma`, `Rop_integral_coupling`, `gasDecor_eq`, `gasR4Decor_eq`,
     `gasR4DecorOp_eq`, `r4Fresh_aggregate_of_localization`, `r4HeavyActivity_bound`, `gasOp_pe_hole`, `r4Coupling`, `r4Fresh_*`, `gasLinked*`. Open: the physical extension that
     `r4Fresh` needs, and the tie of `r4Coupling` to `Rep.B`;
   * (d) **the vacuum cancellation**: `stepVacuum_removed_*`, `VacuumTie.removed_weight_*`: the cancellation of `e^{E_k|Z|_k}` with the
     vacuum term of the creating step uses `VacuumTied` (item 0);
   * (e) the normalization: `R_normalization_of_indep`, `R_normalization_sum_of_indep`, `R_normalizationPhysical` (named integrability hypotheses);
   * (f) the coherence of the new boundary terms (D8, from locality).

Proved inside `rInput_of_parts`: `coh_addRem`, `field_addRem`, `corr_addRem`, `coeff_addRem` (`Coh`, `FieldClauses`, `D1CorrLim`, `D9Coeff` read none of the remainders),
`d8SF_addRem` (sum of the two `R_eq`), `sfData_of_remainder_added` (the input allowance `1/2` at `m` plus the allowance `1/2` of `ℛ''`), `complete` (from 1),
`pin`, `opBound`, `budget` (from 1, they do not read `B`), the ties of `RepClassAt`, (I.2) and the running constants (those of the input, `repFamPost` has the same `β, ν`).

**Flags.**
* The window bound, the small factor, ℬ′ and the coherence of the new boundary terms are not separate Lean sub-inputs, because their objects (the removed
  operator `removedKernel` with its reference density, ℬ′) are not part of the output record; they are (a)–(c), (f) of item 2. The vacuum constants (item 0) and the kept data (item 1) are
  separate. The vacuum tie is a property of the input (not of `R`) that `PreClassAt` does not carry; asking it as `RVacuumInput` avoids changing `PreClassAt`/`IsRepPre2`; if
  `SFStepInput` is stated to give it, `RVacuumInput` becomes a corollary. Window and small factor are proved to chain (`removed_kerBound_logC_of_window`, `lf4R_removed`) at the gas level.
* Rule 10: the two sub-inputs need the exemption of the seven inputs (as `RInput`). `VacuumTied`, `KeptOutput` and `GasOutput` are not inhabited here; `preClassAt_witness` inhabits the hypothesis, and
  the landed post witness `Wit.wIsRep2` (`Inhabited/RFieldProjectionWitness.lean`) has the same small-field data (`rfl`).
* Generality: general `d, N` and the constants of the prefix, as `RInput`; the existentials of the two sub-inputs are at fixed `κ, c₉, β, ν, h, kf, k, ρ, νk`.

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

**StepIntegrableInput (W1131, decision 2026-10-19).** Not provable from the class clauses: `IsRep2` makes no
clause measure ψ ↦ ρ ψ g, and `rep.B`, the small-field data and `bgSF` are free off their domains. Kept as a
provider input: the step maps Φ, ΦE and the physical densities the provider constructs are bounded and
measurable, so integrability is proved for the construction, not from the class (no class-definition change).

## A4-2v: `RVacuumB0Input` is obstructed (W1134)

`VacuumB0Bound` needs `‖b_k + stepVacuumTerm(E_k, E_k+δ″, E_k+δ‴)‖ ≤ C |Z_{k+1}∖Z_k|_{k+1}`. In `localHistory`, `Z_j`, `Ω`, `Ω″` are
intersected with `fineSet Z'`, but `stepVacuumTerm`'s first region `(a.Z k)ᶜ ∖ a.Omega k` is a complement in the whole fine torus, so it contains
`(fineSet Z')ᶜ` (`compl_fineSet_subset_vacuumRegion`, `Spine/RVacuumB0Defect.lean`). The term `E_k · |that region|_k` grows with the torus
for fixed `Z'`; the offsets `δ″, δ‴` multiply the other two regions and cannot cancel it, and `b_k` is bounded by `b_bound` alone
(`norm_vacuumTerm_le_of_b0Bound`: the bound forces `‖vacuum term‖ ≤ 2C|Z_{k+1}∖Z_k|`). Only `E_k = 0` is consistent. LANDED (W1148, ruling R10, 2026-10-19): `Spine/RVacuumB0Defect.lean` keeps only the true lemmas, `compl_fineSet_subset_vacuumRegion` is deleted. Replacement
(ruling R10, edits `StepData.lean`, `StepVacuumR5/Volume`): region 1 := `(Z_k)ᶜ ∩ Z_{k+1} ∖ Ω` (P6 (3.2) localized to `Z'`; `a.Z (k+1) = fineSet Z'`
by `locRH_Z`), which makes excess 1 of `stepVacuumVolume_eq_add_excess` empty; excesses 2, 3 are `Ω∖Ω″` and `Ω″` inside `Z_k`, needing a geometric bound
`|Ω_{k+1} ∩ Z_k| ≲ |Z_{k+1}∖Z_k|` from the definition of `Ω`.

**Settlement of the constants (W1148, 2026-10-20).**
* Consumer: only `StepData.b_ref_bound` (`StepVacuumR5.lean`) and the removed-weight cancellation read `b0_bound`; both already carry the slack `D·V`
  (`‖b + E_ref V‖ ≤ (C_b log β + C_b B₀)|Z_{k+1}∖Z_k| + D V`, `D = C(log β + 1)`, `V = stepVacuumVolume`). `b_bound` is consumed only as the bound of `b` itself.
* The vacuum term is not absorbed by the normalization `s` for an input record: `s` and the vacuum map `vacMap` fix the *new* constant `E_{k+1}` of the
  step (tie by construction, inside `LFStepDataInput`); for a record of `ℛ^pre_k` the data `rec.F.lf.SD` already have their own constants `vacE, vacEpp, vacEppp`
  with `b0_bound`, and `rec.Ev` is a separate flow constrained only by `|E_j| ≤ C_b(log β_j + 1)` (`PreRec.vac`).
* Exact cost of retying to the flow (`norm_b_add_flowVacuumTerm_le`, `Spine/RVacuumRetieBound.lean`, proved): `‖b + vac(E, E+δ″, E+δ‴)‖ ≤ (C_b log β + C_b B₀)|Z_{k+1}∖Z_k| + D V`,
  `D ≥` the three differences to `vacE, vacEpp, vacEppp`. `VacuumB0Bound` asks the same bound with `D V` removed, which is a cancellation: it holds in general only when the
  constants of `SD` already equal the flow (up to `D V ≤ ` the slack in `C_b B₀`). It is not a consequence of the geometry `V ≲ |Z_{k+1}∖Z_k|`
  (which would give `D V ≲ C(log β + 1)|Z_{k+1}∖Z_k|`, exceeding the constant by `C(log β + 1)`).
* Consequence: `RVacuumB0Input` as stated (for an arbitrary `PreRec` and flow) is not provable: there is no inequality in P4 (2.1), (2.41), (2.63), (4.21) that gives
  it; in the source the flow `E_k` *is* the vacuum constant of the step that created the component (Lemma II.5.14, (S0) with the constants of the step), so the
  tie is a clause of the construction. Repair: put the tie into the record (`PreRec` carries `SD.vacE = Ev`, `VacuumTie` as a field, as `LFStepDataInput` already does
  for the successor) or weaken `VacuumB0Bound` to the bound with slack `D V` and give `StepData` a `b0_bound'` with that slack. Both change a landed statement:
  needs the orchestrator. The geometry `|Ω_{k+1} ∩ Z_k| ≲ |Z_{k+1}∖Z_k|` is then only needed for the slack form and is not attempted here.

**Resolved (W1148, 2026-10-20).** `PreRec` carries the field `vacTie` (the step data of every torus are tied to the flow `Ev`, offsets per torus), as the source's construction gives it
(P4 (2.1), (2.41), (2.63)); `SFStep` supplies it from `LFStepDataInput`, the rule-10 witness has the zero flow. `vacuumB0Bound_of_tie` (D = 0 in `norm_b_add_flowVacuumTerm_le`) proves
`VacuumB0Bound`, `rVacuumB0Input` proves `RVacuumB0Input` (`RecB0Bound` now has offsets per torus).

**Row (c) of A4-2ab, `ℬ′`: what blocks it (W1148, 2026-10-20; for the Opus queue).**
* `r4Fresh` (`LargeField/R/RGasRepR4Fresh.lean`) is the P3 mixed-derivative coefficient of a given decoupled extension `F S u : (ι → ℂ) → ℂ` of the P7 (3.23)–(3.25) exponent residual (old minus new exponent); `F` is an argument, not supplied (`AUDIT-DEFS-1018.md`).
* `r4Fresh_aggregate_of_localization` gives `Σ_Y r4Fresh = F S u 1` only under the P3 §4 premises (`Localization.localization_expansion`): `F` analytic in the cut parameters on the P3 polydisc, bounded, and cut-local (`hcut`: it depends on the removed members only through those meeting `Y`).
* `F` is not definable now: the residual is analytic and local only on the global H7 domain, and "analytic and local on the global domain" does not give a local analytic extension to cut-open parameters (`GENERATOR.md`, REFUTED, counterexample `1/(z - 3/2)`); an `h`-independent canonical extension off the fibre is also refuted (`OFFFIBRE.md`).
* Needed: a construction of `F` from the old kernels and the removed operators with its analyticity polydisc and cut-locality proved, then the tie `r4Coupling = Rep.B` (`r4Coupling_empty` is not a consequence of the aggregate identity, `AUDIT-DEFS-1018.md`). Rows (d)(e) depend on this: the integral identity `∫ρ' = ∫ρ` of `GasOutput` is about the `ρ'` it produces.

## FrozenSFStepInput split (W1148, 2026-10-20)

**PROVED** (`Spine/FrozenSFStep.lean`; axioms `propext, Classical.choice, Quot.sound`): `frozenSFStepInput_of_parts` from the frozen sub-inputs and `FrozenLFStepInput`
(parameters `hP : PrefixInput`, `hQ : FlowRateInput`, the map `Φ♭`). Pieces:
1. **Sub-spine core** (proved): `sfSucc_core` (`Spine/SFStepClauses.lean`) is the class-independent core of `sfSucc_clauses` (which is its instance for `D2SF2`); `sfFlatSucc_clauses`
   (`Spine/FrozenSFClauses.lean`) is its instance for `SFFlat2`/`D9Flat` at `massOne P6` and the allowance `1`. `SFFlatClassAt`, `FlatRep.sfFlatClassAt`, `sfFlatClassAt_witness` (rule 10).
2. **A4-1a–f, i at complete backgrounds** (`Spine/FrozenSFImage.lean`): `FrozenInheritInput`, `FrozenNewLevelInput`, `FrozenRenormInput` (`massOne P6`), `FrozenDensityInput`,
   `FrozenRemainderInput` (allowance 1), `FrozenCoherenceInput`, `FrozenIntegrableInput`: the landed properties `SFInheritQ`, … (extracted from `Spine/SFStep.lean`, body-only refactor,
   `SFImageInputGen`, `StepIntegrableInputGen`) over the scales `max(k₀,1) ≤ k < k̂_f` and the class `SFFlatClassAt` with `ν_k L² ≤ 7/8`. No copies. A4-1g has no frozen analogue (no vacuum flow in `ℛ♭`, no `R`).
   Status: open, same as the pre-`R` inputs (they need the exemption of the seven inputs).
3. **The switch at `k = k₀`.** FLUCT-A withdraws the two-stage switch: at `k = k₀` one complete small-field step, like every other scale. What remains is the SF/LF interface
   (`OPEN-SF-LF-INTERFACE`): `FrozenSwitchInput ifc` states `SFtoLFInterface` for the data of a member of `ℛ♭_{k₀}` (open); `frozenSwitch_of_lt` proves it for `k > k₀` (zero kernel data).
4. **Frozen large-field data**: `FrozenLFStepInput` (open): the data `lf'` of the successor (no hull, no `R`) with `D4Pin (k+2)`, `Coh`, `LFCoherent`, and `IsRepFlat2` **given** (H6♭).
   (H6♭) is proved: `frozenBudget_of_pin` (`Spine/FrozenSFBudget.lean`: `Rep.budgetFlat_of_LF2_trunc` on `budgetSetupToOfRun` (`Spine/BudgetSetupOfRun.lean`, extracted from the transfer)
   and `prefixBudgetFacts` (`Spine/PrefixBudget.lean`, extracted from `transferInput_of_prefix`)).
Refactors of landed proofs: `transferInput_of_prefix` now uses `prefixBudgetFacts` and `budgetSetupToOfRun`; `SFStep.lean` definitions `SFImageInput`, `StepIntegrableInput` and the six
sub-inputs are built from the new generic forms (definitionally the same statements).

## SF→LF interface at `k = k₀` (`FrozenSwitchInput ifc`; W1148, 2026-10-20)

`ifc` must provide, for the data `sf` of a member of `ℛ♭_{k₀}` and every Def-6 torus, `SFtoLFData` `X` with: `Σ_Y X.D_Y = chordD`, `Σ_Y X.E_Y = ΔE`, `Σ_Y X.F_Y(g) = ΔF(g)` on the overlap of the two background domains
(exact, by `sfToLF_identity`'s definitions); `F_Y` analytic on `‖g‖₁ < 1`; the polymer bounds `|D_Y| ≤ C_D β_k m_k² e^{-κ_D d(Y)}`, `‖E_Y‖ ≤ C_E E₀(m_k/ε_k) e^{-κ_E d(Y)}`, `‖F_Y‖ ≤ C_F(m_k + E₀ m_k/ε_k) e^{-κ_F d(Y)}`;
`β_{k₀} m_{k₀} ≤ C₀` and the reserve `C_int[C₀²/β + C₀E₀/(βε)] < η`. Landed that gives parts: `sfToLFInterface_complete` (`k > k₀`, trivial); `chordD` identity `(1.1)` of INTERFACE-A
(`chord_identity`, `expansion_chord`); the regime bound `β_{k₀}ν_{k₀} ≤ e^{1/10}` from (I.2) and `β ν L^{k₀ d} ≤ 1` (`beta_nu_kZero_le`, `Spine/FrozenSwitchMass.lean`, proved). The class members come from the transfer
(`transferInput_of_prefix`, `IsRep2.toFlat`), the budget setup from `budgetSetupToOfRun`/`prefixBudgetFacts`, but none of them gives the localized bounds.
**Obstruction (precise).** The three polymer bounds are estimates, not identities: for the full-torus action the chord is `½⟨w,(H_m+α^m)w⟩` with `w = φ⁰ - φ^m`, which localizes to blocks only through the weighted mass response
`‖w‖_loc ≤ 2K₂B_h m` (BG Prop. 5.1: `WeightedProp51S` under `Prop51Hyp`, which the overlap `InUnionDomainR` does not supply: OPEN common-collar BG application) and the Hessian bound `C_H n ‖w‖²`;
`E_Y`, `F_Y` need the Cauchy estimate (2.2) with the anisotropic I-6 bound uniformly on the complex segment (hypotheses "to be verified for the revised class", INTERFACE-A §2). For P7's regional half-bond action
the localized chord is false without a wall term (INTERFACE-A (1.4)); `SFtoLFInterface` has no wall field. So `FrozenSwitchInput` is not provable from landed results; it is not consumed by `frozenSFStepInput_of_parts`.

**`FrozenLFStepInput` split (W1148, 2026-10-20; `Spine/FrozenLFStep.lean`).** `frozenLFStepInput_of_parts` (PROVED, axioms `propext, Classical.choice, Quot.sound`) from the frozen step map
`Λ♭ : FrozenLFStepMap` (`LFStepRaw` for every `FlatRep`) and eight parts, as `lfStepInput_of_parts` with `IsRepFlat2` for `IsRepPre2`: `FrozenHistInput` (`IsComplete (k+1) (k+2)`), `FrozenStepDataInput`
((S0)–(S2) at the constants of the successor with the kernels of `Λ♭`), `FrozenBdryInput` (`D7Bdry2Post`, no hull, no `R`, `B_st ≤ B₀ - 1`), `FrozenFormInput` (`D1Form2` of `stepDensity`),
`FrozenOpBoundInput` (`D5Bound (k+2)`), `FrozenPinInput` (`D4Pin (k+2)`), `FrozenLFCoherenceInput` (`LFCoherent`), `FrozenCorrInput` (`D1CorrLim`). Proved inside: the constants (`succOpConsts`, `succBudgetConsts`),
`Coh` and `FieldClauses` of the successor (`coh_succ`, `field_succ`), the kept data (`KeptData.upTo`, (S3)), the assembly of `IsRepFlat2` with (H6♭) as the premise discharged by `frozenBudget_of_pin`.
All eight parts are open (same status as the pre-`R` parts (g1)–(g5), (h): they need the exemption of the seven inputs); there is no vacuum flow and no removal record in a frozen step, so neither A4-2v nor the removal-history ruling touches them.
`FrozenSwitchInput` is not provable from landed results (obstruction above) and is consumed by none of these.

**Generic parts of the large-field halves (W1148, 2026-10-20).**
* (c) histories: PROVED once, generically. `canonHist` (`Spine/HistCanon.lean`) is a fixed complete set (`exists_isComplete`; `IsComplete k r` refers to the setting only, D-III.8); `LFHistInput_of_canon`
  (`IsComplete (k+1) (k+1)`) and `FrozenHistInput_of_canon` (`IsComplete (k+1) (k+2)`) hold for every step map whose histories are the canonical ones (a constraint on the provider's map, not a premise on the analysis).
* (h′) coefficient data `LFCorrInput` / `FrozenCorrInput` (`∃ St' vc', D1CorrLim`): BLOCKED, not provable from landed results. `D1CorrLim` asks the thermodynamic limits `v1T`, `v2T` along the tori `torusSeq L m₀ n`
  of the image at every level `j ≤ k+1` with the normalization `nuIdeal L (k+1) ν_{k+1}`. Landed: only the radial limit `tendsto_v1T_aInfC` (`R/RadialCoefficientLimit.lean`) for `IsSFFamily` on all tori with the numeric premises `MomNum`,
  and the witnesses `wD1Corr`, `wD1CorrLim`. Missing: (i) the `v2` limit (transverse coefficient) for a class member, not landed at all; (ii) the same chain for the read-torus class `IsSFFamily2On` (R-N₁); (iii) for the inherited levels, the transfer of the old limits
  to the rescaled source (`nuIdeal L (k+1) ν_{k+1} j` against `nuIdeal L k ν_k j`, factor `ν_{k+1}/(L² ν_k)`) along `oldSideSeq`; (iv) the new level `k+1`. About 600 lines of new analysis; one generic statement (over a class `IsSFFamily2On` + `MomNum`)
  serves both the pre-`R` and the frozen part.
* (g4) pins `LFPinInput` / `FrozenPinInput` (`D4Pin`): reduces to a transport lemma that is not landed: for `A, B` with `A.Agree k (k+1) B`, the local histories and `kappaPreH A j Z`, `kappaH`, `keptExp` at the scales `j ≤ k` coincide
  (`RegionHistory.kappaPre` reads `H.parts`, `newCubes`, `outCubes` of the scales `< j` and `P.kappaStep`; the components of `A` and `B` live in different dependent types `Comp j`, equal only through `comps_zp_eq_of_agree`). With it, `D4Pin (k+1)`
  of the successor is `D4Pin (k+1)` of the input pulled along `Agree`; for the frozen part the new scale `k+1 > k₀` has no kept event (`IsKeptEvent` needs `k ≤ k₀`), so `D4Pin (k+2)` is the same statement. About 300–400 lines.

**Update (W1148, 2026-10-21): pins PROVED for both halves; the coefficient data scoped.**
* (g4) `lfPinInput` and `frozenPinInput` (`Spine/PinParts.lean`) hold for every step map `Λ` (no hypothesis on `Λ`). The transport lemma is `d4Pin_of_agree` (`Spine/AgreeTransportRep.lean`), built from
  `HAgr m H₁ H₂` (same steps `j < m`, same `Rem_j`, `j ≤ m`; `HAgr.of_agree` from `Agree m (m+1)`) and the transports `cequiv` (components), `parts_eq`, `newCubes_eq`, `outCubes_eq`
  (`AgreeTransport.lean`), `spineOK_iff`, `spineTarget_eq`, `nextSpine_eq`, `spine_eq`, `bk_eq` (`AgreeTransportSpine.lean`, with `nextBook_map`, `Spine/BookMap.lean`), `kappa_eq`, `kappaPre_eq`, `isKept_iff`
  (`AgreeTransportKappa.lean`), `desc_map`, `lin_eq`, `tailZ_eq`, `locStep_eq`, `localHistory_eq` (`AgreeTransportLocal.lean`) and the equality of the labels of non-removed kept components along `Agree`
  (`lab_eq_of_agree`). In the frozen step the new scale `k+1 > k₀` has no kept component, so `D4Pin (k+2)` is the transported `D4Pin (k+1)` (`d4Pin_succ_iff`).
* (h′) `LFCorrInput` / `FrozenCorrInput`: NOT done, and the estimate in the previous entry (≈ 600 lines) is too small. `D1CorrLim` needs the thermodynamic limits of `v1T` and `v2T` for the image at every level, for the class
  `IsSFFamily2On` (complete backgrounds, `IsSF2`). The landed limit theory (`tendsto_v1T_aInfC` and its chain: `Def6Avg*`, `Def6Inf*`, `Def6Bridge*`, `RadialCoefficient*`, ≈ 13,000 lines) is stated for the first-version class `IsSFFamily`
  (`IsSF`, massless domain) and only for the radial coordinate `Pi.single i₀ 1`; there is no `v2` limit, no rotation to a general unit field `hv`, and no version for `IsSF2`. Inherited levels would follow from the old limits
  (source rescaling and `oldSideSeq`), but the new level `k+1` needs the full theory for the second-version class. This is a campaign, not a lemma.

**R7′ implemented (W1148, 2026-10-21; A3-1 (d)).** The physical base carrier is stated at the class's block constant `M` and torus horizon `K`: `BaseSmallFieldInput M K k₀ geo cs N` with `geo : Geo S n R M`, histories
`RegionHistory S n R k₀ K`, local histories `H.localHistory M K 1 Z'` and the source `g : GIdx S n M K N → ℂ` on the fine sites of the torus (so `baseSource` is the identity); `Kphys` itself, its fields and the content
of the corrected carrier are unchanged. `BaseStepData M K`, `baseK0`, `baseKC`, `baseWit`, `baseStepData_of_input`, `baseSmallFieldInput_nonempty` are generalized in place (`Base/BaseSmallField.lean`, `BaseCarrierData.lean`:
`baseZsites M`, `baseSourceNorm M`); `Prop279Phys`, `Prop279Input`, `prop279Phys_nonempty` and `Inhabited/BaseStep.lean` are the instances at `M = K = 1` (the only textual changes: the extra arguments `1 1` and the source `g` for
`baseSource S n N g`). `Spine/BaseCarrier.lean`: `KphysT` (the remainder as a function of the source on `Torus d (L n₁)`, with `KphysT_baseSource`), `baseSmallFieldInput_class_nonempty` (rule 10 at every geometry of the class),
`baseStepData_at_class` (a family of carriers over the tori `sides L K n_K` gives the base step data on every torus). Changed statements: `BaseSmallFieldInput`, `BaseStepData` (parameters `M K`; the structure `BaseStepData` names its horizon
`Kh` because its field `K` is the kernel), and the theorems of `BaseSmallField.lean` and `Prop279.lean` that mention them.
Remaining in A3-1 (SPINE-PLAN): (a) small-field part at scale 1 (1,800, H, B2); (b) the base kernels `K̃⁰e^{b₀}` in the carrier and (II.7.5) (1,000, H, B1); (c) `D1PreForm2` for `firstDensity` (800, M); (e) (H6′)^pre at 1
(300, L; `Rep.budgetPre_of_LF2`/`budgetSetupToOfRun`); (f) (D8) of `K₀, b₀, ℬ^{(1)}` (400, M); (g) `β₀ = β`, `ν₀ = ν` (20, L); and the assembly of `BasePreStepInput` from them (not yet split: histories complete via `canonHist`, the pin `D4Pin 1` is
vacuous, the budget as in `lfBudgetInput_of_pin`). A3-2 (`BaseFlatStepInput`) needs the same at complete backgrounds.

**A3-1 / A3-2 assembly (W1148, 2026-10-21; `Spine/BasePre.lean`, `Spine/BaseFlat.lean`).** `basePreStepInput_of_parts`, `baseFlatStepInput_of_parts` and `baseStepInput_of_maps` (axioms `propext, Classical.choice, Quot.sound`)
prove `BasePreStepInput`, `BaseFlatStepInput` and `BaseStepInput` from the first-step map `Γ : BaseMap` (the record `BaseRaw`: `z₁`, `R`, `geo`, `cs`, `P`, `sf`, `κK`, `SD`, `KD`, `B`, `St`, `vc`, `Ev`; the histories
are the canonical complete sets `canonHist`, `BaseRaw.famR r`, `r = 1` before `R`, `r = 2` frozen) and the parts, which are generic in the regime (`BaseImageInput Reg`):
* shared by (A) and (B): `BaseConstsInput` (ties, `Coh`, `FieldClauses`), `BaseCorrInput` (`D1CorrLim`), `BaseOpBoundInput r` (`D5Bound r`), `BaseCoherenceInput r` (`LFCoherent`, A3-1 (f)), `BaseKernelInput` (A3-1 (b): the kernels of
  `SD` at the scale `0` are the base kernels `baseK0` of a carrier at the class geometry; documentation of what `Γ.SD` must satisfy, not consumed by the assembly);
* regime (A): `BaseSFInput` ((a), (g): (D2) `preFac`, (D8), (D9), `a_1` free flow, `β_0 = β`, `ν_0 = ν`, (I.2) at `0`, `z₁ > 0 = z_1`), `BaseFormInput` ((c): `D1PreForm2`), `BaseBdryInput` ((a): `D7Bdry2`), `BaseVacuumInput`
  (the flow `E_j`, `|E_j| ≤ C_b (log β_j + 1)`, and the tie of `SD`);
* regime (B): `BaseFlatSFInput` (`SFFlat2`, `D9Flat`), `BaseFlatFormInput` (`D1Form2`), `BaseFlatBdryInput` (`D7Bdry2Post`).
Proved inside: completeness of the histories (`canonHist_complete`); the pins `D4Pin 1` (A) and `D4Pin 2` (B: nothing is kept above `k₀ = 0`) — vacuous; the budget (H6′)^pre at the scale `1` (A3-1 (e); `budgetSetupToOfRun`,
`prefixBudgetFacts`, `Rep.budgetPre_of_LF2_trunc`, (I.2) at `1` from (H.6) by `runningHypTo_succ_of_coeffBounds`) and (H6♭) at the scale `1` (A3-2; `frozenBudget_of_pin`); (I.2) at the scale `1` and the mass bound `ν₁ ≤ (81/79)(7/8) ≤ 9/10`
(`nu_succ_le_of_coeffBounds`); `hM6` and the flow rate from `PrefixInput`. (g) `β_0 = β`, `ν_0 = ν`: clauses of `BaseSFInput`/`BaseFlatSFInput` (they say that the flow of the first step starts from the bare couplings; `sf` cannot be redefined
at `0`, the flow `CoeffBounds.flow` starts there). Open: (a) the small-field data and boundary terms, (b) the kernels, (c) the transform relation (`Σ_records ∏ K_0 = ρ_1`, BASECARRIER item T), (f) the coherence, the coefficient limits `D1CorrLim` (see the
coefficient-limit entry above). Rule 10: the parts need the exemption of the seven inputs; the assembled class members are inhabited by `preClassAt_witness`/`flatClassAt_witness`.

**A4-1f `SFCoherenceInput`: blocked on the map `Φ` (W1148, 2026-10-21).** `SFCoherenceQ` is a clause on `D8SF` of `{ Φ sf with Tm := newLevelTerms … }`, i.e. on the `M^{(k+1)}` and `ℛ^{(k+1)}` terms of the image `Φ sf` as functions of the
fields `(ψ, h, g)` on the Def-6 tori. No definition turns the output of the fluctuation chain (`NewLevelFormula`, `newLevelCoeffBg`, a coefficient family indexed by `physParam`/`physV` and the polymer `T′`) into `Terms d L N₁ m₁ (k+1) N ϱ`:
`Terms` is only produced by the witnesses (`Inhabited/GeneralClassWitness`, `V2*`) and by the splice `newLevelTerms`; the spine's `Φ` is a parameter (rows ★ `Φ`, A4-1b (iii)). Until `Φ` is built (the evaluation of the chain's coefficient at the
physical parameter of a field datum, with the background solves), `SFCoherenceInput` has no object to be proved about; `sfSucc_core` already consumes it as the hypothesis `hD8new`, and the inherited levels are `liftOldTermsFam_M_eq_of_d8`.
What the proof will need, in the chain's terms (to be proved for `Φ` once defined): for two tori `N₁, N₁'` the coefficient `NS.coeff θ T′ = newLevelDetBg … + gsumCoeff μ Lab (A θ) y0 (G θ) T′` agrees at corresponding arguments when its objects do:
`A = commonAct (A₀, AC)`: `A₀` (zero-class, `StepTowerG.e0CoeffFamily_value_fromTowerG_core_twoTorus`, `coreE0_unique`); `AC` and `G₁` from the inherited terms `Eτ` (D8 of the inherited levels) via `evDec` (`explicit_evDec_of_core`);
the bridge marks `G` via `decSol` (`decSol_value_twoTorus`, `decSol_value_twoTorus_of_decBg`); the determinant part `newLevelDetBg` (`newLevelDetBg_eq_of_agree`). The difficulty is not these ingredients but that the pins `F₁`, `Sol` are returned
existentially per torus: the agreement needs the value-uniqueness statements of W1089 for the bridge marks of the formula (as `coreE0_unique` for the core), not yet stated for `AC`, `G₁`.

## A4-1f chain-side value uniqueness (W1148r, 2026-10-21)

Landed: `NewLevelPinUnique` (pins unique on their domains), `NewLevelValueUnique.eTermFun_unique`
(the old-term functional reads `Fk` only through the union-domain pin, via `eTerm_chain_of_one_le`),
`fnOfDec_unique`/`evDec_unique` generalized to two functionals agreeing on `FlRealLC`,
`NewLevelMarkUnique.oldTermEvDec_unique` and `oldTermEvDec_deriv_unique` (the inherited terms of
`H` and `G₁` do not depend on `F₁L`, `SolL`, `FkL`; FlCore/BgSetting/FlSetting as typing premises).
Open: two-torus agreement of `NS.coeff`. (i) the old terms `Eτ` are fixed only by `hEJ` and
`OldTermsAreIrrel` (they are `irrelTorus` of `C.Tm`), so their two-torus agreement is a spine fact
(Agree-transport of `C.Tm`) and must enter as a premise; (ii) no two-torus statement exists for
`evDec` of a localized old term (needs `composeField`/`d1Triple`/`D2raw` on two tori and the
`StepTowerG` form of `FlCore`/`BgSetting`/`FlSetting`); the `coreE0_twoTorus` development is
stated for the tower `StepTowerG`, not for a bare `StepSetting`.

### A4-1f two-torus core for the localized old term: scoping (W1148r, 2026-10-21)

Premise 1 (old terms on two tori) is taken as the box form of the input class's D8/`TorusIndep`
clause: `RawBoxAgree R r r' → E r = E' r'` for the old terms; discharged by `sfSucc_core`'s inherited D8.
Landed tool: `Polymer/TwoTorusEv.lean` `evDec_twoTorus` (any `Φ`, `Φ'`), via `FFmarked_twoTorus`
(single use of `hΦ`, line ~964). Two gaps stop `Φ = eTermFun Gp Gk Gj Hm a Fk E`:
1. `hΦ` compares only the multiplier `t.1.2` (on `Rα`), the fluctuation field `t.2.1` (on `Rδ`) and
   the tangent (on `Rψ`).  `eTermFun` also reads the decoupled background field `t.1.1`
   (`composeField Gk Gp a φ …`) and the raw datum `t.2.2.1` (`d1Triple`, `D2raw`).  Both are available
   at the use of `hΦ` (`decBg_value_twoTorus` returns the `φ` correspondence; `hraw` the raw one), so
   `hΦ` must get two more antecedents.  `hΦ` is a binder of `FFmarked_twoTorus`, `coef_FFmarked_twoTorus`,
   `evDec_twoTorus`, `evDec_blockEnergy_twoTorus`, `Ev_twoTorus`, `Ev_blockEnergy_twoTorus` and is passed by
   `TwoTorusObsKernel` (`siteEv_twoTorus`), `TwoTorusGapClose`, `TwoTorusCoef` (3 sites): changing it in place
   rebuilds all of these modules.
2. `GA`, `HA` are `levelGS` on both tori.  In the chain `Gk`, `Gj` are `localB` sets of a polymer
   (`OldTermSystem.Gk : GeneratingSet … ϱ₁`, arbitrary), so a statement on two tori needs a correspondence
   of `Gk` with `Gk'` under `boxMap` (cells, layers, collar) plus the union-domain pin `FkPin` on
   both (a two-torus version of `decBg_value_twoTorus` for `bgFieldC Gk`, not landed).
Decision needed from the coordinator: (a) allow editing the `hΦ` binder in place across the modules
above, and (b) the form of the `Gk`/`Gk'` correspondence (`localB` of corresponding polymers).

Update (W1148r, f93e3771): the `hΦ` core is done: `FFmarked_twoTorus_core`, `coef_FFmarked_twoTorus_core`,
`evDec_twoTorus_core` (extra antecedents: the decoupled background `φ` on `Rφ` with `BlockMargin`, the raw
datum on `Rθ ⊆ X₁f`); the three landed theorems are instances.  `Ev_twoTorus`, `evDec_blockEnergy_twoTorus`,
`Ev_blockEnergy_twoTorus` are unchanged (not needed for the old term).  Next: the two-torus lemma for
`bgFieldC Gk` under `FkPin`, `Gk = localB` of corresponding polymers: there is no `bgFieldC` lemma for
`localB` or for two tori; `TwoTorusDecBg` (rows/component/value, ~900 lines) is `levelGS`-specific, so this is a
port with the collar of `localB` (residual and rows near the collar), then `composeField`/`d1Triple`/`D2raw`
on two tori, `hΦ` for `eTermFun`, `evDec` of the localized old term, `H`/`G₁`, `NS.coeff`.

### (b) localB two-torus decoupled background: inventory (W1148r, 2026-10-21)

The two-torus decoupled background is spread over `TwoTorusGreenRows` (845 lines), `TwoTorusSY` (624),
`TwoTorusDecBg` (929), `TwoTorusEv` (reads).  They use the `levelGS` facts (counts of uses): `levelGS_mem_Ω_*` (36),
`layerIndex_levelGS` (11), `approxField_`/`residual_levelGS_boxMap` (9), `spacing_levelGS` (5),
`mem_cubeIdx_levelGS` (5), `isLevel_levelGS`, `SY_subset_levelGS`, `subI_levelGS_iff`, `row_SY_levelGS`,
`mem_innerCentres_levelGS`, `inBox_of_mem_resSites_levelGS`, `not_mem_collar_levelGS`, `locSol_`/`interp_levelGS_boxMap`,
`active_levelGS_image`, `resSites_levelGS_image`, `mem_blockIdx_levelGS`.  A core over a generating-set pair
`(GA, GB)` needs these as a correspondence structure `GSCorr GA GB bm`.  `levelGS` is its instance; `localB`
is not: it has a collar (`not_mem_collar_levelGS` fails), so the residual and the rows at the collar need the
data agreement on the collar sites (new analysis, no landed `levelGS` analogue), and `Ω 1` is the polymer, so
`levelGS_mem_Ω_one` becomes membership in the corresponding polymers.  Estimate: 2500+ lines (core
generalization of three files plus the collar), then items 1-5.  Needs a design review before assigning.

Design finding for `GSCorr` (W1148r, 2026-10-21): the `levelGS` two-torus files are single-scale.  Every
cube of `levelGS j` is `(j, y0)` with `CubeBase`; `inner_base_mem`, `innerCentres_mapsTo`,
`sum_innerCentres_boxMap`, `cubeG_boxMap_inner` and the margins (`4R + 12 L^(j+m₁) + …`) use this, and
`TwoTorusCubeOps` (915 lines, 97 uses of `levelGS`) is the same.  `localB t` has layers `1..t` and so cubes at
every scale (and a collar).  A `GSCorr` that "bundles the levelGS facts" is therefore not enough: the cube index
sets, `innerCentres`, `cubeG`, and the margins have to be abstracted over a cube-scale structure (per-scale
base sets, per-scale `intBox` radii), i.e. the port covers `TwoTorusCubeOps` as well (~3500 lines) before the
collar.  Not started; needs a decision whether the localB cover of `Gk` can instead be handled through a
single-scale statement (e.g. `Gk` with `t = k + 1` only) or the full multi-scale port is wanted.

### Two-torus core for the localized old term: status (W1148r, 2026-10-21)

Option 2 holds, in a stronger form than a single-scale port: `bgFieldC` of a localized set is
exactly local (no estimate).  If `σ` carries `Ω₁(Gk)` bijectively onto `Ω₁(Gk')` preserving the spacing,
the entries of the Dirichlet operator at `α = 0` and the source of data agreeing on the read region, the
Euler-Lagrange systems are isomorphic and `bgFieldC`, `bgMultC` correspond (`GSIso`, `bgFieldC_of_gsIso`).
So the multi-scale port of `TwoTorusGreenRows/SY/DecBg` is not needed for `Fk`.
Landed (all build, 0 warnings): `Polymer/BgFieldTransport` (GSIso, transport), `ComposeFieldTransport`
(`SiteCorr`, `GSCorr`, `composeField_corr`, `svec_corr`, `barField_corr`), `FlDatumTransport`
(`flDatum_corr`, `composeData_corr`), `ETermFunTransport` (`eTermFun_twoTorus`), `LevelGSCorr`
(`gsCorr_levelGS`), `TwoTorusEvOld` (`evDec_oldTerm_twoTorus`), and the `hΦ` cores in `TwoTorusEv`.
Premises (typing/geometry data, not proof steps): `GSCorr Gk Gk'`, `GSCorr Gj Gj'`, `GSIso … Gk Gk'` on the
label margin `Z` (the localized sets of corresponding polymers; the `localB` instance is still to be
proved: spacing, `fullMatrix` entries and `source` of `localB t Yp` under `boxMap`), block closure of `Z`, and
the old terms agree on raw data agreeing under `boxMap` on `Z` (box form of D8/`TorusIndep`, discharged by
`sfSucc_core`'s inherited D8).
Open: (4) `H`/`G₁` of two `NewLevelSystem`s from `evDec_oldTerm_twoTorus` (needs a bijection of the index
types of the old terms and `hatOf_boxMap`); (5) `NS.coeff` from `gsumCoeff_transport` (generic, landed) with the
label bijection `ψ` of `Lab1` (zero-source, thick and bridge labels) and the det part
(`detExpansionLocC_term_twoTorus_fromTowerG` for the tower instance); (6) the `localB` instance of `GSIso`.

### (6) The localB instance of GSIso (W1148r, 2026-10-21)

`Polymer/GSIsoOfOmega`: `gsIso_of_omega` and `gsCorr_of_omega` give `GSIso` and `GSCorr` from the correspondence of the
domains `Ω_n` on the box (layers, layer indices, entries of `-Δ + ν + Q* a Q`, the collar and the source follow).
`Polymer/LocalBBoxCorr`: for a polymer `X` in the box of radius `ρ0` and `X' = boxMap '' X`, the domains of
`𝔹_j(X)` and `𝔹_j(X')` correspond on the box of radius `ρ0 + 6 j L^(j+m₁)` (`localB_omega_boxMap_all`; the
cube index is the floor quotient of the centred coordinate, so the recursion `nearStep` is an integer
statement, the same on both tori), whence `gsIso_localB` and `gsCorr_localB`.  Margins are the hypotheses
`hmA`, `hmB` (`2 (ρ0 + 1 + 6 j L^(j+m₁) + (5L+2) L^(n+m₁)) < N L^m₁ L^k`).  The premises `GSCorr Gk Gk'`,
`GSIso … Gk Gk'` (and `GSCorr Gj Gj'` for a localized `Gj`) of `evDec_oldTerm_twoTorus` are therefore proved
for `Gk = 𝔹_j(X)`.  Open: (4) `H`/`G₁` of two `NewLevelSystem`s (index bijection of the old terms, `polyDom`
under `boxMap`, `hatOf_boxMap`, the per-term premises of `evDec_oldTerm_twoTorus` at the marks
`(u,0)`, `(0,0)`); (5) `NS.coeff` via `gsumCoeff_transport`.

### A4-1f two-torus agreement of the chain objects (W1148r, 2026-10-21)

Landed: `OldTermPair` (premises structure), `TwoTorusEvOldGen`, `NewLevelTermPair`
(`TermPairPremises`, `evTerm_twoTorus_of_premises`), `NewLevelHPairs` (`H_twoTorus_of_pairs`),
`NewLevelGPairs` (`G₁_twoTorus_of_pairs`), `NewLevelDetTwoTorus`, `NewLevelCoeffTwoTorus`
(`NewLevelSystem.coeff_twoTorus` for two systems of the tower steps `hatStepKG`, roots `z`, `bc z`).
Premises are typing/geometry data (labels, bijections `ψ`, `κ`, `e`, margins, `GSCorr/GSIso`,
the D8 box form of the old terms).  What remains for the full A4-1f agreement: discharge those
premises for the actual systems (label/mark bijections on `Lab1`, from the class), and the map Φ.

### Obstruction to `newLevel_coeff_twoTorus_of_class` (W1148r, 2026-10-21)

The index bijection `e : NS.O.ι ≃ NS'.O.ι` (and so every premise of `H_twoTorus_of_pairs`,
`G₁_twoTorus_of_pairs`, `coeff_twoTorus`) cannot be produced from class membership.  The inherited levels
of a `NewLevelSystem` are existential data: `OldTermSystem.ι` is an arbitrary finite type, and the only
constraints are `hEJ` (`∑ τ, Eτ τ = Jr.EJ C`, a constraint on the sum) and `OldTermsAreIrrel`
(`Eτ τ = irrelTorus … (y τ) (X τ)`, with `y`, `X` arbitrary).  Neither says which pairs `(y, X)` occur or
that `τ ↦ (y τ, X τ)` is injective and onto the admissible pairs, so two systems on the two tori need not
correspond (duplicate, cancelling or missing terms give the same sum).  The same holds for the pinned
fields `Gk`, `Gj`, `F₁L`, ... (existential beyond their pins; the pin uniqueness of `NewLevelPinUnique`
only compares fields with the same index).
Smallest repair: strengthen `OldTermsAreIrrel` with the canonical index clause
`τ ↦ (jL τ, y τ, X τ)` is a bijection of `ι` onto the set of admissible irrelevant pairs of the class
(determined by the class geometry); then `e` is `boxMap` on pairs on the quarter box, and the remaining
premises are the D8 box form of `irrelTorus C.Tm` plus the landed `gsCorr_localB`/`gsIso_localB`.

`OldTermsCanon` (Inhabited/NewLevelCanon.lean, W1148r): the chain's producer must prove it for the inherited levels (to be added after R13 lands).
It pins the index set and `Eτ`; for `newLevel_coeff_twoTorus_of_class` it must also pin the other free fields of `OldTermSystem`
(`X₁f τ`, `𝒦X τ`, `Gk τ`, `Gj τ`, `ρ`) as canonical functions of `(jL τ, y τ, X τ)` (they are existential, constrained only by
`CovSetup`/`BgSetting`); the pinned decoupled fields `F₁L`, `SolL`, `FkL` are then unique by `NewLevelPinUnique`.
Also needed: a partial index bijection (the full index types have different sizes on the two tori): only the `τ` with `Y ∈ polyDom τ` correspond.

Partial-bijection layer (W1148r): `NewLevelSystem.H_twoTorus_partial(_of_pairs)`, `G₁_twoTorus_at_of_pairs`, `PolyDomBoxMap.polyDom_boxMap_iff`,
`OldTermsCanonPins` + `CanonCover` + `exists_domEquiv_of_canon` (NewLevelCanonPins) give the index bijection e from boxMap on pairs.
Still open for `newLevel_coeff_twoTorus_of_class`: discharge `hAdm/hAdm'/hbox/hcov/hdom` (geometry of the canonical covers), the ~60 premises of `OldTermPair`
per old term (typing + D8 box form of `irrelTorus C.Tm`), the label/mark bijections `ψ, κ` on `Lab1`, the zero-source activities, and the tower-only restriction of `coeff_twoTorus`.

### A4-1f two-torus agreement of the new-level coefficient from the canonical pins (W1160, 2026-10-21)

Landed (all build, 0 warnings): `NewLevelCanonBox` (`domEquiv_of_canon_box`: the partial index bijection of the old
terms in the box, split into small lemmas), `TwoTorusLabelBox`, `NewLevelZeroCorr`, `NewLevelThickCorr`,
`NewLevelAnchorCorr`, `NewLevelAnchorG`, `NewLevelPsiData`, `NewLevelKappaData`, `NewLevelCoeffPairs`
(`newLevel_coeff_twoTorus_of_pairs`: `NewLevelSystem.coeff_twoTorus` with `ψ`, `κ`, `hA`, `hG` discharged from
`hE` (index bijections of the old terms, with the relation `Q` of the canonical pairs) and `hprem` (premises of the
comparison of corresponding old terms)), `NewLevelCanonHE` (`canon_hE`), `NewLevelCanonHPrem` (`canon_hprem`:
`termPairPremisesAt_of_data` with the agreement of the old terms from `oldTerm_E_agree`), and
`NewLevelClassCoeff.newLevel_coeff_twoTorus_of_class_of_cellTerms`.  Refactors (statements unchanged): the label and
activity correspondence of the direct terms is the core `directTerms_labelCorr_twoTorus` of
`gsumCoeff_e1_twoTorus_of_directTerms`; `psiThick_fineBlock_iff` is extracted from `markedPair_boxMap_iff`.

Hypotheses of the main theorem: the pins `OldTermsCanonPinsAt` of both systems; the class (`TorusIndep`, `hlocB`);
the zero-source label pin `hI𝒴`; the per-pair geometry `hgeom` of the canonical covers (a margin `Z` with
`GSCorr`/`GSIso` of the localized generating sets, `BlockMargin`, and `CellTermsAgree` for the cell case); the
covers (`hcX`, `hcloc`, `hcov`); margins; the typing data of the decoupled fields (`FlCore`, `XiCData`, `HatConn`, radii).
Open for the producer: `hgeom` for the actual covers (instance `localB`, `gsCorr_localB`/`gsIso_localB` for `Gk`, `Gj`)
and `CellTermsAgree` (the cell case).
