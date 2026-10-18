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
4. **`TransferInput` (A4, Lemma IV.2.1)**: `ℛ_{k₀} ⊂ ℛ♭_{k₀}`, same `ρ`, `ν_{k₀}`. Landed: `IsRep2.toFlat` (with `D2SF2.toFlat2`,
   `D9Coeff.toFlat`), valid only for torus horizons `K ≤ k₀ + 1`. Named sub-inputs (D3, F6):
   * (a) LF-2 (ii) for a representation with the counter history truncated at `top = k + 1`, independent of `K`. The landed
     `Rep.lf2Hyp` needs `K ≤ top`, and `Rep.budgetFlat_of_LF2` / `frozen_budget` need `K ≤ k̂`;
   * (b) `IsRep2.toFlat` for every `K` from (a);
   * (c) `BudgetSetup` from the class: its `run : RunningHyp` asks (I.2) at every scale, while the class gives `RunningHypTo` up
     to `k`. A truncated `RunningHyp`, or `P.beta` pinned beyond `k`, is needed;
   * (d) `S.Good` and (H-λ) `hH1`, `hH2` (LFR Lemma IV.3.3 (c); window `(d−2)/2 < θ ≤ (d−2) log L`) as a lemma of the prefix.

   ~600.
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
