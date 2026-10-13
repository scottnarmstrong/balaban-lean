# M0THETA — the physical new observable on the renormalization chart

**PROVED. Audit snapshot.** Read-only Lean tree `/home/scott/Balaban`, commit `4afce4744fb6811bd511f4cb7013190658d6a059`, 2026-10-13 UTC.
I compared the declarations below with P4, printed p. 704 (4.17)–(4.19), Theorem 3.1 (h), and the filed phase-1 notes.
Names of the form `File.declaration` identify a source file and a declaration there; names in the leaf table are proposed work items.
**OPEN. Scope.** No landed declaration constructs the physical full-chart `M0θ`, the marked part of `E0θ`, or their `expM0`/`expE0` fields.
The conditional `renormExpInput_scale_of_tower_of_exp` accepts arbitrary new functions, so its zero witness is not a physical result.

## 1. Exact observable and its datum

**PROVED. Record type.** In `RenormExpG.lean:RenormExpInput`, with `G` the next-level generating set and `N` spins:
```lean
(M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ)
expM0 : ∀ p, ∃ term, IsLocExp (N := N) G
  (XiCOneReal G a ν ε) r₀ (YsM p) dY κb BM0 (M0θ p) term
```
**PROVED. Consumer.** `thm31h_of_input` adds `M0θ p D ξ`, `(F ((D.Ψ,D.h),ξ)).1 p`, and `oldM p D ξ`.
At the zero class, `thm31h_zero_of_fields` omits `oldM` and bounds the expansion by `BM0 + Kloc·cK·cK2·B·εR` for `εR≤r₀`.
Neither consumer defines `M0θ`; `RenormExpInput.expM0` is a premise.
**PROVED. Source formula.** P4 (4.17)–(4.18) evaluates the already produced step observable at the scaled field and multiplies it by `β_k⁻¹ᐟ²`.
In landed notation the candidate at a fixed source `g` is `β_k⁻¹ᐟ² · M0C(S_θ, zeroClass, g, p.1, p.2)` with `θ=renThetaDatum S εren D ξ`.
`renThetaDatum` multiplies `D.Ψ` by `1+renZeta εren ξ` and retains `D.h`; the step mass stays `ν`, while `renMassU ν ξ` enters the separate `C₂` term.
`thm31bC_of_input_M0` states `S.M0C C g y i = (S.betaU)¹ᐟ² · ∑_T E(T)`, conditional on `ObsMarks` and a rate inequality.
Thus the rescaled physical new observable is the coefficient sum `∑_T E(T)` when those are the physical coefficients for the same datum and `g`.
**REFUTED. Unit-source shortcut.** The record has no `g` binder, but this does not make `M0θ` a kernel extracted by setting `g=δ_p e_i`.
`StepComplexOut.lean:M0C` puts `g` in `WtwoC C g`, hence in the tilted average, and in `McompAtC`; the dependence need not be linear.
The record can describe one externally fixed `g` slice; the full P4 observable family needs a source-parameterized version and analytic control in `g`.
Setting `g=0` or a unit source silently changes the object and cannot establish the full H7 source family.

**PROVED. Chart geometry.** `XiCOneReal` witnesses a real center `(Ψ₀,h₀)` with `h₀ : Fin N → ℝ`, complex spin displacement `Ψ″`, and zero external displacement.
It says `D.h` is constant across sites for that datum; it does not say its value equals the tower step's fixed `S.h₀` for every datum in the domain.
`renThetaDatum` keeps that varying real center field, so the full renormalization chart contains fibres with `D.h≠S.h₀`.
`StepSetting.withDatum D hD` requires `hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)` and changes only `D′`.
**REFUTED.** `S.withDatum (renThetaDatum S εren D ξ)` is not defined on the entire `XiCOneReal` domain from the chart hypothesis alone.
It is available on the constant-`S.h₀` fibre because `renThetaDatum` preserves `h`.
**PROVED CONDITIONAL ON the constant-field premise.** `StepComplexJoint.JointRep.withDatum`, `W1_withDatum`, `W2_withDatum`, `McJ_withDatum`, and `StepComplexOutAnalytic.M0J_withDatum` identify raw representatives with `M0C` on that fibre.
**OPEN. Full chart identification.** Define the observable from the raw-level `JointRep`/physical source family over all chart data, then prove its slice equality with `M0C` for every admissible real center, by re-basing the step or an equivalent source characterization.
A `withDatum` theorem for the tower's one fixed `h₀` is only a slice check, not that full-chart equality.

## 2. What `expM0` still requires

**PROVED. Inclusion.** `ThetaChartMargin` and `renE0_theta_domain` prove `XiCOneReal(εren)` and `‖ξ‖<r₀` place `renThetaDatum` in `XiCData(εstep)`.
`renE0_theta_domain_of_le` enlarges that conclusion to any `ε₂≥εstep`; `StepTowerTheta.εs_le` supplies `ε₂=2R.t` for its current `εren=R.t` tower.
`StepTowerTheta.detGrouped_ambient` uses the inclusion for determinant terms, not observable terms.
**PROVED CONDITIONAL ON `ObsMarks`.** `thm31bC_of_input_M0` is stated for an arbitrary `StepSetting S`, `StepClass C`, source `g`, site `(y,i)`, and `ObsMarks` at that same step.
It can therefore be applied to `S.withDatum D′ hD` on the fixed-`S.h₀` fibre, once the marks and chart hypotheses are supplied.
`Thm31b.lean:thm31b_of_input` is also abstract in its `ObsMarks` record.
**OPEN. Every-datum physical marks.** `obsMarks_zeroClass_family_of_ray` takes a ray-family premise `hray`, then returns marks for `T.step` at its own datum for every admitted `g,y,i`.
Its quantifiers do not give an `ObsMarks` record for every `D′∈XiCData(εstep)`, even on the constant-`S.h₀` fibre.
`ObsMarks.toConsumer` and `ObsMarks.congr_f` transport an already built record; they do not construct a chart-wide family.
The observable extension must keep one source, label activity, mark family, root label, and integrand identity across all data and the `u` interpolation parameter.
The already open physical ray/tilt premise cannot be replaced by the zero-interaction inhabitant of `ObsMarks`.

| Tower producer at `T.t` | Why it is tied to the datum | Needed for a chart family |
|---|---|---|
| `obsMarks_zeroClass_family_of_ray` | Its `val`, direct terms, ray clause, and `WtwoC/McompAtC` identity are built for `S=T.step`, with `g` fixed only after the tower constants. | One physical source/tilt and the same integrand identity for every fibre datum at the step chart radius. |
| `StepTower.scale`, `StepScaleData` | Their `core`, ray margin, fluctuation radius, and bounds are for the base step and `T.t`. | A parameter-independent scale package whose required margins hold at the chosen step chart radius. |
| `markedFamily_fromTower_allRoots` | The energy family `Ev` is already raw-chart analytic, but its `Q=shiftUC` and slice identity use `withDatum` at constant `S.h₀`. | An observable analogue with `WtwoC`, source marks, and a full-chart raw identity. |
| `markedRootAssembly_zero_fromTower` | Its `M` is raw-chart analytic, while `MarkRealAt` and `MarkedRootAssembly` identify the base step on the fixed-field slice. | A site-rooted mark/tilt record and equality with the physical observable on each real-center fibre. |
| `thm31bC_of_input_M0` | It consumes a fixed-datum `ObsMarks`; its existential `E` may be chosen afresh for each datum. | A single canonical coefficient function analytic and local in the parameter. |

**PROVED. Analytic mechanism.** `Thm31CoeffB.obsCoeff` is the canonical sum of a resummed first-order term and a remainder; `thm31b_coeff_M0` applies it at a fixed datum.
The first-order part reads the kernel `hker`, activity `A`, and marks `G1`; the remainder reads `A` and `Gr` through `ObsMarks.Erem_eq` and `gsumCoeff`.
`Thm31CoeffAnalytic.ParamMarkFamily` assumes one activity and marks jointly analytic on open `V×𝒰`, uniformly bounded and carried by a compact configuration set.
`gsumCoeff_analyticOnNhd` handles the remainder's ambient dependence; `norm_gsumCoeff_le` gives its common decay estimate.
The first-order `markIntTerm` and the kernel still need parameter analyticity and compatible bounds before the whole `obsCoeff` is analytic.
`ParamCarrierLocal.paramMarked_analytic_local_bound` adds parameter locality through separate agreement premises for activities and marks.
**OPEN.** There is no landed physical parameter family for the observable `A`, `G1`, `Gr`, and `hker` over the full `XiCOneReal` chart and source family.
A fixed-datum `ObsMarks` proof, even for every datum separately, does not select the same coefficients analytically in `(D,ξ)`.
The remainder part needs `ParamMarkFamily` with `holA`, `holG`, carrier/continuity, bounds, and raw locality; the first-order marks and kernel need analogous clauses.
Compose those canonical terms with `renThetaDatum`; its raw map is analytic (`analyticOnNhd_renThetaRaw`) and chart inclusion supplies the domain.
The resulting `term Y` must be analytic on the ambient `expDom`, satisfy `RawAgree Y`, sum to physical `M0θ p`, and obey `BM0·exp(-κb·renDY Y)`.

**PROVED. Fibre infrastructure.** `RenormDetFibreMap.renFibreMap_mem_renYs`, `subset_renFibreMap`, `renDY_renFibreMap_le`, `card_renFibre_le`, `renRegroup_norm_le`, and `sum_renRegroup` provide an abstract rooted-polymer regrouping.
**OPEN. Site-root instance.** For `p=(y,i)`, take `X₁=X1 G 1 k (fam 1 y)` and `YsM p=renYs (renCube G X₁) G 1 X₁` as in `renLoc_fields_scale_of_tower`.
Show each physical observable coefficient's support meets this `X₁`, lies in the selected `renFibreMap`, and inherits the count/size bound.
The root condition `rootCube (blockIndex y) ∈ T` from `thm31bC_of_input_M0` alone does not prove all those physical-site support and cover claims.
Divide out the `√S.betaU` factor only after the same physical `g` and datum have been identified; then pay the fibre multiplicity in `BM0` and ensure `κb` stays below the post-count rate.

## 3. Marked energy on the same chart

**PROVED.** `MarkedRootAssembly.markedRootAssembly_zero` is an abstract step theorem: its `Ev` sum, locality, bound and analyticity range over every datum in `XiCData(eps)`, and its `M` is raw-chart analytic.
The physical `shiftUC` and derivative identity in that theorem still quantify `D.h=S.h₀`; `markReal_slice_allRoots` has the same restriction.
`markedFamily_fromTower`, `markReal_slice_allRoots`, and `markedRootAssembly_zero_fromTower` currently instantiate those results at the tower radius `T.t`.
**OPEN.** The marked `E1locC` part of `E0θ` needs one common analytic family at the enlarged step chart, composed with `renThetaDatum`, with a zero-parameter identity and a fibre expansion on `renYs`.
`StepTowerTheta.core2`, `dom_margin2`, `coer_margin2` cover the doubled-radius core and determinant margins only; they do not supply all marked lane caps.
At datum radius `2t`, reprove the `eps`-dependent `c7le`, `dom_margin`, `coer_margin`, `bg1_cap`, `xi_small`, and any chart bounds used by the marked constructor.
If its fluctuation radius is also doubled, reprove `t_cap`, `bg0_cap`, `cK2_cap`, `cK2'_cap`, `bg1_cap`, and the scale/ray margins at `2t`.
Those doubled caps do not follow from their non-strict `t` versions; the tower construction's eventual-at-zero argument can choose `t` to satisfy them simultaneously.
Keeping the fluctuation radius at `t` while enlarging only the datum radius avoids some doubled caps, but still needs a mixed-radius wrapper for the abstract `markedRootAssembly_zero`.
The source identity for all varying real centers must be proved at raw level; the fixed-`S.h₀` `withDatum` identity alone is insufficient.

| Step-side field at `2t` | Landed now? | New tower choice |
|---|---|---|
| `core2`, `dom_margin2`, `coer_margin2` | Yes, in `StepTowerTheta`. | Already chosen by `tower_core_rates_at_least_two`. |
| `t_cap`, `bg0_cap` with doubled fluctuation radius | No; the old bounds use `2t` as their entire left radius. | Add the stricter inequalities to the eventual-at-zero list. |
| `cK2_cap`, `cK2'_cap` at doubled fluctuation radius | No; the old cap is only at `t`. | Add both linear inequalities to the same list. |
| `bg1_cap` with doubled chart and fluctuation radii | No; both radius terms grow. | Add its strengthened inequality to the same list. |
| `c7_cap`, `large_block`, determinant rate | Yes; they do not contain the radius. | Reuse unchanged. |
| `xi_small`, ray/scale margins at doubled radius | No direct tower wrapper; `core2.c7le` can supply the chart smallness numerically. | Recheck the physical `StepScaleData` bounds with the chosen fluctuation radius. |

## 4. Choose the two radii at the start

**PROVED. Current route A.** `StepTowerTheta` exists with `FlCore` and determinant margins at `2t`; `detGrouped_ambient` is already a usable determinant-only result.
**OPEN.** Completing A for energy marks and observables means re-instantiating the step activity, mark, ray, tilt, and `ObsMarks` lanes on that larger chart, in addition to the caps above.
**Recommendation: B.** Use the original `StepTower` step radius `t_step=t` and renormalization class radius `t_ren=t/2`, with one sufficiently small `r₀` satisfying `xiK2 3 3 2·(3/2)·r₀≤1`.
Then `ThetaChartMargin` gives `εstep=t/2+xiK2·(3/2)·(t/2)·r₀≤t`; apply `renE0_theta_domain_of_le` at the already landed step chart radius `t`.
This preserves the step-side `markedFamily_fromTower`, determinant expansion, and existing radius-dependent observable work at `t`; the renormalization solution must be rebuilt for `t/2`.
**PROVED CONDITIONAL ON a short new monotonicity lemma.** `FlCore` has `eps_pos`, `small1`, `c7le`, `B_le`, `B_one`, `phi_lt`; all upper bounds ease as `eps` decreases, and the other fields are independent of `eps`.
No declaration named `FlCore.mono_eps` was found in main; prove it using positivity of `xiC1`, `K4`, and `3+K4`, then set both `eps` and `δ₁` to `t/2` where the renormalization wrappers need equal radii.
The `δ₁_pos` and `δ₁_le` fields also ease; the abstract `flCore_level_transfer` can then carry the smaller core to each level.
**PROVED CONDITIONAL ON elementary inequalities.** `StepTowerRen`'s `ren_margin`, `D₀_le_one`, `D₀_le_star`, `D₁_le_star`, `StepTowerRenEnd.end_margin`, and `StepTowerRenSol.sol_margin`, `sol_K`, `sol_ζ` have nonnegative `eps` coefficients and fixed positive right sides.
At `t/2` their left sides decrease for the same `r₀`; the `ThetaChartMargin` fields `small`, `data`, `star`, `K₁`, `c₀`, `δ_one` are similarly inherited or strengthened after shrinking `r₀`.
The bound `B=8eps` becomes `4t`, and the `renCK_mul_ge` comparison is homogeneous in `eps`; reprove it by multiplying the constant inequality by `t/2`.
**REFUTED. Free radius substitution.** Existing `renLoc_fields_scale_of_tower`, `exists_isRenSol_scale_of_tower`, `renEndpoint_scale_of_tower`, and `renormExpInput_scale_of_tower_of_exp` print `R.t` in their types.
They cannot be rewritten at `R.t/2` by `simp`; `renZeta`, `renC1On`, the solution map, `B`, and the domain genuinely change.
Re-instantiate `renDec_sharp`, `renDec_pertClass`, `renLocC1_zero`, `renLocC2_zero_at`, `renLocDphi_zero_at`, and `exists_isRenSol` at arbitrary positive `eps=t/2`.
Then rebuild the tower wrappers `renDec_sharp_scale_of_tower`, `renDec_pertClass_scale_of_tower`, `renLocC2_scale_of_tower`, `renLocDphi_scale_of_tower`, `renLoc_fields_scale_of_tower`, and `renormExpInput_scale_of_tower_of_exp` in smaller-radius forms.
`thm31g_C1_scale_of_tower`, `thm31g_C2_scale_of_tower`, and the endpoint wrapper must follow the same radius and the same new `F`.
B is cheaper because these renormalization abstract theorems already expose `eps`, while A would reopen several physical step families, especially the source tilt.
It is a proposed refactor, not a landed two-radius tower theorem; its correctness still requires the wrapper builds and the physical analytic families.

## 5. Lean-ready leaves, in dependency order

| Leaf (proposed) | Exact conclusion sketch and inputs | Size / owner / start |
|---|---|---|
| `flCore_shrink_eps` | From `FlCore … eps … δ₁`, `0<eps'≤eps`, `0<δ₁'≤δ₁`, derive `FlCore … eps' … δ₁'`; prove the required coefficient signs from `DecSpecs`. | 80–150 lines, Sonnet, start now. |
| `ren_half_margins` | From `R : StepTowerRenSol`, derive the listed ren margins and `ThetaChartMargin 3 3 2 (R.t/2) εs R.r₀` with `εs≤R.t`; shrink `r₀` if necessary, preserving solution margins. | 150–240, Sonnet, start now. |
| `ren_half_core_and_solution` | At each admissible level give `FlCore … (R.t/2) … (R.t/2)` and `IsRenSol … (R.t/2) (R.t/2) r₀ (4R.t) F`; use the first two leaves, `flCore_level_transfer`, `exists_isRenSol`. | 170–260, strong, after margins. |
| `ren_half_loc_fields` | For the same `F`, give all three `HasLocPrinciple` fields on `XiCOneReal(R.t/2)` with block and site `renYs`, `renDY`, rates `κa,κb≤2R.κdec`, `B=4R.t`; use the abstract LOC and decoupling theorems. | 220–300, strong, after solution. |
| `obs_raw_source_family` | Construct one `g`-parameterized, raw-chart analytic tilted activity and observable marks with the physical integrand identity for every real-center fibre at step radius `R.t`; use the physical ray/direct terms and `JointRep`. | Split into ≤300-line leaves, strong, start source/ray portion now. |
| `obs_param_coeff_theta` | Build parameterized `A,G1,Gr,hker`; use `ParamMarkFamily` for the `gsumCoeff` remainder, prove analytic `markIntTerm` and kernel terms, compose `obsCoeff` with `renThetaDatum`, and prove slice equality to `β_k⁻¹ᐟ² M0C` for fixed `g`. | Split into ≤300-line leaves, strong, after source family. |
| `obs_site_fibre_expM0` | Instantiate `renFibreMap` on site `X₁`, regroup the canonical coefficients into `YsM p`, prove `IsLocExp … κb BM0 (M0θ_g p)` including the source and zero-chart identities. | 220–300, strong, after coefficients. |
| `energy_mark_theta` | Use the all-root marked family at step radius `R.t`, compose it with the half-radius chart map, prove full-chart source identity and `E1` equality at `ξ=0`; combine with `renE0θ_det`. | Split into ≤300-line leaves, strong, start chart composition now. |
| `energy_fibre_expE0` | Regroup the marked-plus-determinant rooted coefficients into `renYs z`; prove ambient `IsLocExp … κa BE0 (E0θ z)` and the physical zero-chart identity. | 220–300, strong, after marked and determinant fibres. |
| `ren_half_input_physical` | With one `F`, source `g`, physical `E0θ` and `M0θ_g`, assemble `RenormExpInput` through the three localization fields and both expansions; apply `thm31h_of_input` or `thm31h_zero_of_fields`. | 120–220, Sonnet, last. |

**OPEN. Closeout.** A proof of `expM0` must exhibit a nonzero physical source-dependent family on every datum of the full renormalization chart, with one analytic coefficient choice and a site-root fibre bound.
The existing fixed-step `ObsMarks` and determinant-only `StepTowerTheta` do not imply it; the half-radius refactor lowers the step-side duplication but does not remove the source-family mathematics.
