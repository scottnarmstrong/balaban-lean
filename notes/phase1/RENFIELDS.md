# RENFIELDS — zero-class renormalization input

**PROVED. Snapshot.** This is a read-only source audit of `/home/scott/Balaban` at `37ead0c294272a2954e1b33268c1e18d20be24a0` (2026-10-13). Existing declaration names below were checked in the Lean tree. `PROVED` describes only the cited result; `PROVED CONDITIONAL ON` keeps its hypotheses; `OPEN` marks missing physical instances; `REFUTED` rejects an invalid shortcut. No Lean build or repository edit is claimed.

## 1. The seven exact fields

**PROVED.** `Fluctuation/RenormExpG.lean:RenormExpInput` has parameters `G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE M0θ oldM`. Here `F` is the raw-datum/`Fin 3 → ℂ` solution pair, `blk` has block roots, `Ys` has block-root covers, and `YsM` has observable-site covers. The following quotes are its field types, with line wrapping only:

```lean
locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
  (fun D _ => bgClass G ν (cK * ε) D) (fun D φ ξ => renC1On G a ν ε (blk z) D.Ψ D.h φ ξ)
  (fun D _ => bgFieldC G a ν (bgC0 d L N) D)
locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
  (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
    (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
  (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
  (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1, bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2))
expE0 : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa BE0 (E0θ z) term
expOld : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Bold (oldE z)
  term ∧ ∀ Y ∈ Ys z, ∀ D : BgData G N, XiCOneReal G a ν ε D → term Y ((D.Ψ, D.h), 0) = 0
locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb Kloc
  (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))}) (fun _ v _ => v p)
  (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)
expM0 : ∀ p, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb BM0 (M0θ p) term
expOldM : ∀ p, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb BoldM
  (oldM p) term ∧ ∀ Y ∈ YsM p, ∀ D : BgData G N, XiCOneReal G a ν ε D →
    term Y ((D.Ψ, D.h), 0) = 0
```

**PROVED. Old fields.** `Fluctuation/RenormInputZero.lean:renormExpInput_zero_of_fields` takes the other five field types verbatim and returns this record with `oldE=oldM=0`, `Bold=BoldM=0`; it uses `isLocExp_zero_cover` on arbitrary `Ys,YsM,dY`. Thus `expOld` and `expOldM` are solved at zero class, but the five inputs are still premises.

**PROVED. `locC1`.** `Fluctuation/RenormLocC1Zero.lean:renLocC1_zero` fills exactly the first field for `G=lvTop`, `a=compWeight L a₁`, `blk z=blockSites … k z`, `Ys z=renYs (renCube G (X1 G m₀ k (fam m₀ (blockSite k z)))) G m₀ (X1 …)`, `dY=renDY G m₀`, `κa≤2κd`, `Kloc=1`, and `cK=2+2·K4 d L N BG κ·xiC1 d`. Its domain is `XiCOneReal` and its polydisc has `0<r₀≤1/16`. `Inhabited/RenormLocC1ZeroWitness.lean:renLocC1_scale_of_tower` gives this type at every scale of one `T : StepTower κmin`, with `m₀=1`, `ε=T.t`, `κd=T.κdec`, and any fixed `κa≤2T.κdec` and `r₀` in that interval.

**OPEN. Matching `locC2`.** It must use that identical block `blk`, `Ys`, `dY`, `κa`, `Kloc`, `r₀`, `cK`, plus one scale solution map `F` and `B`. The landed shifted mode-P data `RenormStrictData.lean:renEdat_decHyp_of_flCore`, `renEdat_strictDataM_of_flCore` use the same `XiCOneReal` domain, but have not supplied the decoupled solution, class membership, endpoint equality, or the `HasLocPrinciple` transfer clause. The proposed sharp class bound asks `cK·cK2 d L N·B ≥ cK2' d L N (famConst d L BG κ)·b_*·ε`; with `B=8ε`, the needed inequality is `8cK·cK2 ≥ cK2'·b_*`. **OPEN:** the fixed `locC1` value of `cK` has not been shown to satisfy it. Shrinking `r₀` or `ε` cancels from this inequality.

**OPEN. Matching `locDφ`.** Its site-root cover `YsM p` differs from the block-root `Ys z`, but its `dY`, `κb` rate convention, `Kloc=1`, `r₀`, `cK`, `B`, and `F` must be shared with `locC2`; choose `κb≤2T.κdec`. `RenormLocFibre.lean:renLoc_fin_domains` supplies proper block and site root domains and `renDY_nonneg`; `RenormRowAgree.lean:renDec_row_agree` supplies data row agreement under its component hypotheses. The local cut functional and endpoint still need a producer.

**OPEN. New energy and observable.** In P3 Theorem 3.1(a),(b), evaluated at `θ=(1+renZeta ε ξ)Ψ` in P4 Proposition 4.1 and 4.2, `E0θ z` is the new rooted energy `ℰ''₀(z)(θ)` and `M0θ p` is the coefficient of the rescaled new observable `β_k^{-1/2}ℳ''₀(p)(θ)`. Their types above demand jointly analytic, `RawAgree`-local terms on `XiCOneReal × {‖ξ‖<r₀}`, with decay at rates `κa,κb`; the old fields say nothing about them.

## 2. What the new-term producers actually give

| Field | Landed result | Verdict and required conversion |
|---|---|---|
| `expE0` | `Fluctuation/StepComplexThm31.lean:thm31aC_of_input_const`; `ParamDatumFamily.lean:thm31aC_coeff`; `DetStepInstance.lean:thm31aC_coeff_detLoc_withDatum`; `Inhabited/DetPackageFromTower.lean:detPackage_fromTower` | **PROVED CONDITIONAL ON** actual `E1MarksC`, determinant record, and rate/norm premises: fixed-datum rooted coefficient sum and bound `(N L^d BL+1)K0 e^{-κ' dExt(T)}`. **PROVED** one shared-tower determinant family with hull bound, anchor and covariance (W429); **OPEN:** the marked plus determinant physical family in `(D,ξ)`, `θ`/`XiCOneReal` chart inclusion, local fibre map `T↦Y`, equality with physical `E0θ`, and bound after fibre sum. |
| `expM0` | `Fluctuation/StepComplexThm31.lean:thm31bC_of_input_M0`; `Thm31CoeffB.lean:thm31b_coeff_M0`; `ObsMarksAssembly.lean:obsMarks_of_tilt` | **PROVED CONDITIONAL ON** actual `ObsMarks`, rate and tilt activity: `S.M0C=√S.betaU·∑T E(T)`, root support and `(I.B1+I.B2)e^{-κb dExt(T)}`. **OPEN:** physical source-family identification, division by `√S.betaU`, chart/`θ` transfer, site-root fibre grouping and the final `BM0` bound. |
| Both | `Fluctuation/RenormExpCauchy.lean:IsLocExp`, `.mono_radius`, `.mono_rate`; `RenormInputZero.lean:isLocExp_zero_cover` | **REFUTED** that zero inherited terms make either field trivial. The generic witness in `RenormExpG.lean:renormExpInput_witness` chooses zero new functions and a whole-torus cover; it does not instantiate physical `E0θ` or `M0θ`. |

**PROVED. New supporting marks leaves.** `Fluctuation/MarkRealDomain.lean:markReal_hdomT_of_disc`, `MarkRealRegular.lean:markReal_fderiv_mask_eq_neg_beta_sum`, and `MarkedCommonLabels.lean:paramMarkFamily_common` have landed at this snapshot. They discharge a real-slice domain/derivative part and common-label transport under their stated hypotheses. **OPEN:** the physical rooted `E1MarksC` family with a shared source/chart and the sum identity required by `expE0`; no `markedRootAssembly_zero_of_markReal` is landed.

**OPEN. Energy proof plan.** First obtain one jointly analytic, local, rooted physical coefficient `e(z,T,D,ξ)` with the actual marked plus determinant formula and a sum identity for `E0θ`. Prove `θ` lies in the unrenormalized step chart for every `D∈XiCOneReal`, `‖ξ‖<r₀`, with an open ambient extension. Regroup `e` over `renYs` by a support-preserving map and prove `∑_{T:Y(T)=Y}‖e‖≤BE0·exp(-κa·renDY Y)`. Package all four `IsLocExp` fields. The fixed-datum coefficient theorem alone cannot yield joint analyticity.

**OPEN. Observable proof plan.** Obtain the physical `ObsMarks` with the same source and tilted exponent, then a jointly analytic site-rooted family of the rescaled coefficients. Prove its sum is `M0θ`, transport support to `YsM`, and pay the fibre count and `BM0` inequality. `obsMarks_of_tilt` is conditional on `A.hW` and its other activity fields; its existence does not discharge the physical tilt. P4's advertised `BM0≤(1/2)β^{-1/4}ξ_{k+1}^{(d-2)/2+γ-α₁}` is still **OPEN** after regrouping.

## 3. Consumers and exact quantifier obligation

**PROVED CONDITIONAL ON `RenormExpInput`.** `Fluctuation/RenormExpG.lean:thm31g_C1_of_input`, `thm31g_C2_of_input`, `thm31g_Eu_of_input`, `thm31h_of_input` produce localized expansions of `C₁`, `C₂`, `E0θ+oldE`, and `M0θ+(F …).1 p+oldM`, respectively. `Fluctuation/RenormInputZero.lean:thm31g_C1_zero_of_fields`, `thm31g_C2_zero_of_fields`, `thm31g_Eu_zero_of_fields`, `thm31h_zero_of_fields` specialize the bounds to `Bold=BoldM=0`; at radius `εR≤r₀` the new-energy bound is `BE0` and the new-observable bound is `BM0+Kloc·cK·cK2·B·εR`. These are Theorem 3.1(g),(h) inputs for the next step, conditional on the physical record and displayed numerical premises.

**PROVED. Stronger clause to preserve.** `HasLocPrinciple` asks that *every* bound `M` on `f D v ξ` over all `D∈XiCOneReal` and all `v` in the class imply the coefficient bound `Kloc M e^{-κ dY}`. A pointwise bound on the true field, even an `IsLocExp`, is weaker. `renLocC1_zero` proves this transfer; `locC2` and `locDφ` must too. The source class is `XiCOneReal` at the full level, not merely the single zero-class datum. A proposed step output restricted to one datum would not fill these fields.

**OPEN. Physical target `renormExpInput_zeroClass_scale` (binder contract, not yet a final Lean command).** Fix `κmin`, then `T : StepTower κmin`; choose `r₀,β₀,κa,κb` and the formulas/majorant constants for `BE0,BM0` before `k,N₁,ν,β,p₁` and before a source. Evaluate the scalar `BE0,BM0` from those formulas at each scale; their sharp P4 values can depend on `k,β`. Set `cK=2+2·K4 3 3 2 T.BG T.κ·xiC1 3`, `Kloc=1`, `B=8T.t`, `m₀=1`; require `0<r₀≤1/16`, `κa,κb≤2T.κdec`, and the shifted margins below. For every `k≥1`, admissible `N₁` (`3∣N₁`, `5<N₁`), `ν>0` with `ν3^{2(k+1)}≤1`, `β≥β₀`, `p₁>0` in the step radius, and `D : StepScaleData T k hk N₁ ν β p₁`, choose one physical `F : RawData … × (Fin 3→ℂ) → (field×multiplier)` satisfying `IsRenSol` on the same radius, the proper block/site covers `Ys,YsM` and `dY=renDY`, and the *actual* functions `E0θ,M0θ`; conclude `RenormExpInput G (compWeight 3 1) ν T.t r₀ cK B F blk Ys YsM dY κa κb 1 BE0 0 BM0 0 E0θ 0 M0θ 0`. Keep `F`, covers and both functions inside the per-scale existential; neither is a free hypothesis. `β₀` may have to dominate the radius and output-family thresholds.

**OPEN. Why this is a contract.** No landed Lean declaration defines the physical full-chart `E0θ` or `M0θ` family on this renormalization domain. The exact final command must substitute those definitions and prove their equality with the step terms before freezing; leaving them as arbitrary binder functions would admit a zero witness and miss the physical theorem. `StepScaleData` is a `Prop` package for the same `T`, not a replacement for that equality.

**OPEN. Tower margin.** The shifted I-4a data require
`2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t)) < deltaStar' 3 3 2 (famConst 3 3 T.BG T.κ) (gamma1 3 / 8)`.
`Fluctuation/RenormStrictData.lean:renMargins_exists_r₀_of_flCore` takes this inequality and then chooses positive `r₀≤1/16` with `D₀=2K4·xiC1·T.t+3r₀≤1,deltaStar'` and `D₁=b_*·T.t·r₀≤deltaStar'`, where `b_*=3/2+(32/15)(3+(K4+bgK1)xiC1)`. **REFUTED:** the `B_le` field of `FlCore` is the needed fact; its right-hand constant uses `BG₂`, whereas this margin uses `BG`.

**OPEN. Tower change.** Add an explicit field for the displayed `BG`/`deltaStar'` margin to the physical tower, or prove it from a stronger existing field. `tower_core_rates_at_least` chooses `t` through an eventual-at-zero conjunction after `BG,κ,m₁` are fixed; positivity of `deltaStar'` permits one more strict eventual inequality, so its construction can be rerun with smaller `t` while retaining the old bounds. Its current theorem does not return that extra conjunct. Add or derive the uniqueness comparison margins `cK2'·b_*·T.t·r₀≤rho4,c6` and `r₀≤r_F` before scale quantification; shrinking `t`/`r₀` can pay these if their targets are positive. The rate/entropy join `T.κ0=aEnt+1` versus the common-root demand `aEnt+2≤κ0` is a separate tower repair (`TOWERJOIN.md`).

**OPEN. Radius/class mismatch.** `renLocC1_scale_of_tower` accepts any `r₀` in the interval; choose the one from the shifted margins once, rather than separately by scale. The coefficient inequality `8cK·cK2≥cK2'·b_*` is independent of `t,r₀`; either prove it at the fixed `cK`, choose a larger shared `cK` and transport `locC1` by monotonicity of `bgClass`, or revise the shifted estimate. The existing `renLocC1_zero` type alone supplies no such transport.

## 4. Exact discharge checks before record assembly

**PROVED CONDITIONAL ON the shifted data margins.** `renEdat_decHyp_of_flCore` provides the pointwise `DecHyp` in mode P at `D₀` and `b_* ε ‖ξ‖`; `renEdat_strictDataM_of_flCore` provides the strict family data at fixed radius `b_* ε r₀`. Their conclusions are data hypotheses for `Localization/DecoupledSolveAnalytic.lean:i4a_analytic`. They do not choose the analytic solution, nor identify its `s=1` value with `F`.

**OPEN. Two-radius argument.** The fixed radius yields analyticity but only a bound of order `r₀`. Reapply the landed pointwise `DecHyp` at each `ξ` and invoke uniqueness to obtain the order-`‖ξ‖` estimate needed for both `pertClass` and `SupBounds`. At `ξ=0`, obtain exact zero. The class membership must hold for every admitted complex cut, while `IsRenSol` controls the physical endpoint only.

**PROVED CONDITIONAL ON component agreement.** `renDec_row_agree` establishes `DataAgreeRows` for the shifted tuples on the required row set. Its hypotheses include agreement of underlying decoupled backgrounds on the component. Applying `i4a_local_rows` still needs both `DecHyp` records and the small fixed points. The final `renC2On` read region must include its root rows; `locDφ` needs the site root to lie in the localized component.

**OPEN. Endpoint equality.** At cut parameter one, use `i4b_one`, the mode-P/unit-mode equality at zero defect, `isPerturbedM_iff`, and `IsRenSol.unique` within their `rho4` and `c6` margins. A jointly analytic cut solution without this equality cannot fill `locC2` or `locDφ`, because their `u` functions contain the actual `F`.

**OPEN. Energy fibre obligation.** A fixed-datum `CubeB` coefficient has diameter `dExt(T)` and a block root. The `IsLocExp` term is indexed by a finset of physical sites `Y`, with size `renDY Y` and a `RawAgree Y` law. The map `T↦Y` must prove both support inclusion and a rate inequality after counting every `T` in a fibre. Choosing `Y=Finset.univ` merely reproduces the abstract witness.

**OPEN. Observable fibre obligation.** The source coefficient has a site root and an extra `√S.betaU` factor in `S.M0C`; use the rescaled coefficient in `M0θ`. Its activity and root label must be the same as in the physical `ObsMarks`, and its `BM0` must include the fibre count. A bound for each `T` cannot be assigned unchanged to every aggregate `Y`.

**OPEN. Quantifier check.** The final constants `r₀,κa,κb,β₀` and the formulas controlling `BE0,BM0` must be common to at least two distinct admissible scales; the evaluated amplitudes may vary with the scale. A per-scale `∃` for the tower-level constants is weaker. `renLocC1_scale_of_tower` already permits a common chosen `r₀`, but the remaining fields and physical coefficient bounds have not been joined to it.

## 5. Bounded leaves, in dependency order

| Leaf (proposed name) | Exact target sketch and landed inputs | Size; worker; start |
|---|---|
| 1 `renTower_margin` | Under a strengthened `StepTower` constructor, add the displayed strict `BG`/`deltaStar'` margin, one `r₀` and `r_F` comparison before scales; reuse `tower_core_rates_at_least`'s eventual choice and `renMargins_exists_r₀_of_flCore`. Keep the `κ0` retuning with the tower owner. | ≤240; strong; **start now** on the numeric proof, coordinate record edit. |
| 2 `renShared_cK` | Prove the fixed `cK` inequality above, or a `bgClass` monotonicity transport from `renLocC1_zero` to a larger shared `cK`; use `renBgClass_dec`, `renLocC1_zero`, `RenormExpLemma35.lean:exists_isRenSol`. State the chosen `cK,B` outside the scale binders. | ≤200; strong; **start now** as a numeric/API audit; stop if no uniform inequality follows. |
| 3 `renE0_theta_domain` | For physical `θ=(1+renZeta ε ξ)Ψ`, prove the unrenormalized chart/class inclusion and an ambient analytic map on `expDom G (XiCOneReal G a ν ε) r₀`; inputs `XiCOneReal.xiCOne`, `renZeta`, the step relative chart. This is an inclusion, not `expE0` itself. | ≤220; strong; **start now** after fixing the physical coefficient notation. |
| 4 `renE0_fibre` | Given a genuinely landed joint physical `e(z,T,D,ξ)` with sum/support/analytic/local/rate fields, form `term Y=∑_{T:Y(T)=Y}e` and prove `IsLocExp` at `BE0,κa` on `renYs`; use `IsLocExp`, `renLoc_fin_domains`, finite-sum analyticity. | ≤260; Sonnet; **wait** for the energy family; no conclusion-shaped hypothesis in the final physical theorem. |
| 5 `renM0_fibre` | Analogous site-rooted `term Y` from the physical rescaled observable family, with `YsM`, `BM0`, `κb`; use `thm31bC_of_input_M0` only after its `ObsMarks` are physical and chart-uniform. | ≤260; Sonnet; **wait** for the observable family and tilt. |
| 6 `renormExpInput_zeroClass_scale` | Supply `locC1` by `renLocC1_scale_of_tower`, `locC2/locDφ` from the RENPERT lane, `expE0/expM0` from leaves 4–5, and old fields by `renormExpInput_zero_of_fields`; return the one physical record with common `F,r₀,cK,Ys,YsM,dY,Kloc`. | ≤180; Sonnet; **wait** for the five physical fields and the tower/class joins. |

**PROVED. Lane boundary.** W431 is working on the shifted analytic/sharp solution (RENPERT leaves 2–3); the separate LOCC2 session owns leaves 4–8, so none is duplicated above. `renDec_row_agree` closed its row-data premise but does not itself prove `locC2` or `locDφ`. The new leaves here isolate the tower join and the two new-term conversions.

**OPEN. Closeout test.** At a nonzero `ξ` and a proper rooted `Y`, the final `E0θ,M0θ` sums must equal the physical step coefficients, with one `F`, one `r₀`, and the same `dY`; then apply all four zero-class consumers at `εR≤r₀`. A record obtained by setting `E0θ=M0θ=0` is not this test.
