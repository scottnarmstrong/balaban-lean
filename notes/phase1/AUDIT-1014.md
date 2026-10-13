# AUDIT-1014 — second-half landing audit

**PROVED. Scope and freeze.** Read-only, refute-first statement/source audit at `/home/scott/Balaban` commit `31599634f6e222ccacfdbad8fd77d5120dff69b8` (2026-10-13 UTC). The 57-file SHA-256 manifest is
[AUDIT-1014.freeze.sha256](AUDIT-1014.freeze.sha256). It includes the frozen Root-F, P4/P5 PDFs, review sources, and the named Lean modules. No source or Lean proof was edited; no build or axiom census was run.

**PROVED. Method and envelope.** Focused correspondence audit: inspect declarations and their input types, seek a counterinterpretation, check producers by `rg`, compare the physical claims with P4/P5 printed pages, then classify the narrower
statement. The brief authorizes only this scratch report and read-only source inspection. The statuses below distinguish a proved Lean statement from whether it can fill the paper or root interface. “DEFECT” would mean an incorrect declaration
or a false claimed correspondence; I found no such proved declaration in this slice.

**REFUTED. Global closeout claim.** These landings do not establish either frozen root. Root-F quantifies all `d≥3,N≥2`, unit `h`, `0<ν≤1`, complex sources, and torus-coherent polymer coefficients; the shared step fixes `d=L=3,N=2` and
`ν3^{2(k+1)}≤1`. Root-C still needs actual remainder/limit producers. This is a scope result, not a claim that any Lean theorem is inconsistent. Anchor: `Frozen/Roots/LogPartitionMultiscale.lean:logPartition_multiscale`; P4 H.4/H.7, pp. 677–679;
P5 Proposition 3.4, p. 520.

## A. Shared tower and binder order

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `TowerCoreRatesAtLeast.lean:tower_core_rates_at_least` proves the numerical/core tuple with `κmin≤κ`; `StepTower.lean:exists_stepTower` selects `κ0=aEnt 3 3+2`, `κdec=100(κ0+c1+10)`,
`κ'=3κdec/2+κ0+1`, then one `m₁,c,BG,κ,t,…` independent of `β,k,N₁,ν`. The `κ0` retuning is real: `StepTower.κ0_two` states `aEnt+2≤T.κ0`. `TowerCoreRatesRen.lean:tower_core_rates_at_least_ren` and `StepTowerRen.lean:exists_stepTowerRen` add a
strict margin and `r₀` before scales. These records contain `FlCore` as a *field constructed by their inhabitation theorems*, not a premise silently assumed by the endpoint.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `StepTowerScale.lean:StepTower.scale` has the order `T,A₁>0,p → ∃βray → ∀k,N₁,ν,β,p₁ → Nonempty StepScaleData` under `3∣N₁`, `5<N₁`, `0≤ν`, `ν3^{2(k+1)}≤1`, `βray≤β`, `0<p₁≤pLog A₁ p (β3^k)`.
Thus auxiliary `A₁,p` precede `βray`, and the latter precedes scale and temperature. Root-F permits such fixed auxiliary choices before its `β₀`, but this theorem does not cover Root-F's full mass interval or arbitrary dimensions.
`StepTowerScaleLemmas.lean:StepScaleData.beta_pos` derives `β>0` from the package's `cψ_pos`, so the record is stronger than arbitrary raw input data.

**NOT YET USABLE BECAUSE — OPEN.** `StepScaleData` is a Prop *conclusion bundle*: `core`, central `xi`, `ray`, radius margins, and `covers`. Endpoints with `D : StepScaleData` and no `β≥βray` are sound implications on every inhabited `D`; they
are not vacuous as a theorem schema because `StepTower.scale` inhabits `D` in its stated range. They are not unconditional physical endpoints outside that range. Refutation attempt: set `β=0,p₁=1,ν=0`; `detPackage_fromTower` does not need `D`,
while `sourceActivityC_scale_fromTower` still requires both `β≥β₀` and `D`, so no contradiction or missing producer follows from omitting `βray` in its binder.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `StepOutputConsts.lean:stepOutput_consts_exists_ge` inhabits an independent numerical record; `StepOutputPhysical.lean:stepOutputPhysical` ties its `k0,kdec,k',kout,kH,kdet,lhull,Ktot` to the
*same* tower when `stepHullMin≤κmin`. `StepOutputConsts.kout_le`, `.kH_ge`, `.kdet_ge`, `.lhull_ge` are inequalities of that record. They do not assert the marked or class output terms exist. `StepTowerRen` extends the original tower and
preserves its witness data, rather than choosing a second incompatible tower.

## B. From-tower endpoints

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `expSourceChart_scale_fromTower`, `sourceFamilyRelative_scale_fromTower`, and `sourceDirectTerms_scale_fromTower` reuse one `T`, with their own thresholds after fixed `A₁,p` and before the
scale. `SourceDirectTermsFromTower.lean:directTermsFamily_shared_labels` is an equality/transport for a fixed domain family. The analytic direct-term family is on the relative `physV` chart; neither it nor the chart representative alone states
the source exponent `hW` at every chart point.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `SourceActivityFromTower.lean:sourceActivityC_scale_fromTower` really has `∃𝒴 ∃hdom, ∀g∈l1Ball, ∃BR ∃BC`; its shared `Lb` is `{Y∈𝒴} ⊕ {Y∈𝒴}` and its `HEq` clauses identify labels and block
splits. `stepActivityBound_zeroClass_source_of_directTerms_shared` supplies those equalities; they are usable by heterogeneous transport, though the activity *records* remain selected after `g`. Refutation of the stronger reading: there is no
`∃A, ∀g` or chart datum binder before `∀g`, hence no joint source-analytic `A` follows.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `DetPackageFromTower.lean:detPackage_fromTower` chooses one root-indexed family at the tower, with term formula, anchored collar grouping, hull-rate bound, locality, and lattice/rotation
clauses. `DetGroupedAnalytic.lean:detGrouped_chart_family_fromTower` proves grouped analyticity on raw-subspace and `physV` charts plus chart-relative locality. Its conclusions are not class-domain inclusion; P4 H.4 requires the terms on the
prescribed localized class domain (p. 677; P4 Proposition 2.1, p. 696), and P5 Proposition 3.4 also requires torus agreement (p. 520).

**NOT YET USABLE BECAUSE — OPEN.** The source and determinant endpoints now share `T`, but source labels, physical two-segment exponent identities over `physV`, all-root marked fields, and a common energy polymer index remain separate work. The
`HEq` witnesses address types, not those analytic/value equalities.

## C. Determinant symmetry

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `DetCollarHullSymm.lean:detCollarHull_cubeAct_genSymm` and `image_cubeAct_detCollarFibre` assume `hL : L=3`; the generic translation/coordinate-permutation lemmas have wider parameters, while
the reflection and full generated-group wrappers visibly specialize to `L=3`. `exists_detExpansionLocC_grouped_sym` does not secretly prove all `L` reflection covariance. This is compatible with the fixed `L=3` tower and narrower than P4 H.4's
general Euclidean covariance.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `DetRotation.lean:exists_detExpansionLocC_rot` asserts term invariance for complex `R` with `RᵀR=1`, from a datum `D` *in* `XiCData`; it does not assert `D.rot R∈XiCData`. The term is total on
background data, so the off-chart evaluation is meaningful. `exists_detExpansionLocC_rot_real` adds chart preservation for real orthogonal `Q`, and `detPackage_fromTower` records that distinction. Refutation attempt: take a non-real complex
orthogonal `R`; only the algebraic identity survives, not chart invariance, exactly as the statements say.

## D. Renormalization chain

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `RenormC1Analytic.lean:renC1Cut_analytic` supplies the analytic cut functional and its all-ones value. `RenormC1Local.lean:renC1_local_cut` supplies agreement on read sites.
`RenormLocC1Zero.lean:renLocC1_zero_at` concludes `HasLocPrinciple` on the *full* `XiCOneReal` domain for each root; `renLocC1_zero` quantifies all roots. This exactly matches `RenormExpInput.locC1` at `Kloc=1`, `blk=blockSites`, `Ys=renYs`,
`dY=renDY`, and the displayed `bgClass` constant. In `HasLocPrinciple`, the transfer clause quantifies `∀M` and all data in the domain; no class-wide bound `M` is assumed by `renLocC1_zero_at`.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `RenormSharedClass.lean:renLocC1_scale_of_tower_of_le` enlarges that class constant through `HasLocPrinciple.mono_class`; `renCK_ge` and `renCK_mul_ge` provide the shared numerical comparisons.
`RenormStrictData.lean:renEdat_decHyp_of_flCore` and `renEdat_strictDataM_of_flCore` provide shifted mode-P data; `RenormDecAnalytic.lean:renDec_sharp` produces a jointly analytic cut solution from explicit `D₀,D₁` margins, and
`StepTowerRen.lean:renDec_sharp_scale_of_tower` supplies those margins. `RenormRowAgree.lean:renDec_row_agree` is row equality under its named cut/data agreement premise, not an assertion for arbitrary unrelated pairs.

**NOT YET USABLE BECAUSE — OPEN.** `RenormPertClass.lean:renDec_pertClass` assumes the coefficient comparison `hCB`; `renCK_mul_ge` supplies the arithmetic only after the intended choice `B=8ε,cK=renCK` is made in a shared interface.
`RenormEndpoint.lean:renDec_one_unique` consumes an existing `IsRenSol` solution and `hball : rho4≤c6`. The generic `IsRenSol` existence theorem is landed in `RenormExpLemma35.lean`, but no tower-level producer of this `hball` was located. Its
own file says `rho4` and `c6` use unrelated constants. The endpoint theorem is valid as conditional, not a closed tower consequence.

**REFUTED. Mode-P overread.** `renDec_sharp` states `DecFixed … false` at every cut; `renDec_one_unique` identifies its value with `IsRenSol` only at `s=1`, using the unit field there. Neither asserts the continued field obeys the
unit-constraint Euler–Lagrange equations at `s≠1`. P4 (4.4)–(4.5), printed p. 701, are the physical variational equations; a complex decoupling continuation is an internal analytic device. The narrower Lean statements are faithful to that role.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `RenormLabelNonempty.lean:renLabel_nonempty`, `renLabel_card_ge`, `renYs_second_element` require `3∣N₁` and `15<N₁`, and prove at least 27 cut labels and a strict enlargement of `X₁`.
`renLocC1_nonempty_scale_one` gives `N₁=18,k=1,ν=0` with actual cut labels. Refutation of the older examples as evidence of active cuts: their `N₁=9` has `X₁` equal to the torus, hence `RenLabel` is empty.

## E. Marked and observable families

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `MarkedEvJoint.lean:markedEv_joint_physV` packages one `MarkedBlockExpansionDecPair` with joint chart/hat/mark analyticity, conditional on cover, zero tree length, read-site and block-margin
inputs; `MarkedJointWitness.lean:markedEvJoint_instance` supplies these at a physical witness with nonempty `physV` and a nonzero bidisc, but uses `X₁=Set.univ`. `MarkedCubicJoint.lean:markedCubic_joint_physV` and `markedCubic_joint_param` give
analytic marked cubic derivatives under the explicit radial margin. These are useful analytic producers, not the all-root physical mark record.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `MarkRealDomain.lean:markReal_hdomT_of_disc`, `MarkRealRegular.lean:markReal_fderiv_mask_eq_neg_beta_sum`, and `MarkRealDiscSlice.lean:markReal_disc_slice` supply the real-slice domain and
derivative identities when the analytic disc lies in `FlBall`; the from-tower slice takes `StepScaleData`, `D.h=h₀`, `D∈XiCData`, and `‖x‖≤p₁`. Its advertised `markReal_disc_slice_nonempty` tests `x=0,ν=0`: it establishes a satisfiable
interface, not a nonzero mark.

**NOT YET USABLE BECAUSE — OPEN.** `MarkedCommonLabels.lean:paramMarkFamily_common` takes `G`, `hbound`, `hholG`, `hcontG`, `hmeas` as inputs; it extends the activity and transports a family. `commonAct_hW_interp` transports an *existing* a.e.
exponent identity. `markedCommonLabels_nonempty` uses zero activities, a zero mark and a whole-torus base label. No physical all-root `E1MarksC` is produced by these theorems.

**NOT YET USABLE BECAUSE — OPEN.** `ObsRemainderMarks.lean:obsRemainder_of_sharpHat` produces `ObsRemFields` from a sharp-hat expansion; its a.e. `ae_obsHat_eq_true` is under `Measure.pi BS.μ`. `ObsMarksAssembly.lean:obsMarks_of_tilt` supplies
`ObsMarks` only after the activity `A` and its `holt`, `holσ`, `zero`, physical `hW`, numerical smallness, and the chart datum are given. `obsMarkHalves_of_sharpHat` supplies the kernel/remainder half; `ObsRayIdentity` is a separately proved
identity inside that route. The source exponent and common activity family are not constructed by `obsMarks_of_tilt`.

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `SourcePhysValBridge.lean:W2_eq_physVal_sub` says the zero-class `Jr.W2` is the difference of `physVal` at source `g/β` and source zero, on a chart ray; `sourcePhysVal_W2_fromTower` supplies
its central-datum tower instance. It does not identify the `Jr.W1` background value or assert the full `Jr.W1+Jr.W2` activity identity. P4 (2.51)–(2.57), pp. 694–695, separates the energy and source contributions, consistent with this two-part
bridge.

## F. One-scale branch; G. Root-C

**FAITHFUL WITH RECORDED SPECIALIZATION — PROVED.** `KF0AllGoodGas.lean:block_gas` is a conditional polymer-gas theorem. `KF0AllPlusGas.lean:allPlus_gas` uses real `src`, a unit `h`, positive `ν`, cutoff, weighted halo bounds and numerical gas
inequalities; it equates precisely the *all-plus, all-ψ-small* integral to a product-cutoff normalization times `exp(logSeries)`. `allPlus_gas_instance` supplies compatible numbers at `d=3,N=2,s=64800`, `src=0`, `ν=1`, for sufficiently large
`β`. Its source counterpart is LF-BASE-KF0 Part F, (F.1)–(F.13); that note explicitly leaves the bad/minus-sheet complement and full Root-F normalization open. No complex-source or all-sector identity is stated.

**NOT YET USABLE BECAUSE — OPEN.** `Correlations/C1StarLimits.lean:c1Star_remainder_limit_criterion` and `c1Star_truncated_limit_criterion` are Tannery criteria requiring per-scale limits, a summable majorant, and (for truncation) `Jf→∞`;
`inv_betaR_sub_le` is the real P9 (4.18) inequality under `SeqHyp`. No declaration in this file concludes a field of `C1Star`. Its example only supplies synthetic `u,v,b`. The physical F3 summands, limits, majorant and truncation horizon remain
producers to build.

## H. Conditional-premise census

**PROVED. Census rule.** The 48 declarations with `_of_` in their name in the frozen A–G files were found by `rg` and checked at their heads. Each row below lists names → non-source proof premise → producer. Pure algebraic/geometric premises are
labelled “local”; they are not missing physical inputs. This is a statement census, not a proof-body audit.

| Names with `_of_` | Proof premise → producer/status |
|---|---|
| `tower_core_rates_of_at_least`, `tower_core_rates_at_least_of_ren`, `hullRate_ge_of_le` | Rate lower bounds → landed numerical constructors; local arithmetic. |
| `renDec_sharp_scale_of_tower`, `expSourceChart_scale_of_fromTower`, `renLocC1_scale_of_tower` | Tower/scale or `FlCore` data → `exists_stepTowerRen`, `StepTower.scale`, `StepTower.core` landed. |
| `stepActivityBound_zeroClass_source_of_directTerms_exposed`, `stepActivityBound_zeroClass_source_of_directTerms_shared`, `stepActivityBoundC_of_activityBound_exposed` | Direct terms, equal domains, exponent a.e. equality → `sourceDirectTerms_scale_fromTower` and ray transport landed at central datum; chart-wide producer open. |
| `detTerm_sym_of_formula`, `detTerm_rot_of_formula`, `detCollarHull_cubeAct_of_collar`, `aligned_add_of_dvd` | Formula, symmetry/collar/divisibility → `detPackage_fromTower` and local geometry landed. |
| `exists_mem_resSites_of_mem_renC1Reads`, `renC1Ag_of_rawAgree`, `rowSite_iff_of_potentials` | Read-set and row agreements → local geometry/data equalities landed. |
| `renEdat_decHyp_of_bgBounds`, `renEdat_strictDataM_of_bgBounds`, `renDec_data_bounds_of_flCore`, `renMass_field_le_of_flCore`, `renEdat_decHyp_of_flCore`, `renEdat_strictDataM_of_flCore`, `renMargins_exists_r₀_of_flCore` | Background/`FlCore` bounds and margins → `StepTowerRen.core` and `renMargins_exists_r₀_of_flCore` landed in its scale range. |
| `renLocC1_zero_of_le`, `renLocC1_scale_of_tower_of_le`, `renPertClass_CB_of_quotient_le`, `renPertClass_of_sharp` | Existing loc principle or sharp solution and coefficient comparison → `renLocC1_zero_at`, `renDec_sharp`, `renCK_mul_ge` landed; shared instantiation open. |
| `gdef_eq_zero_of_unit`, `DecHyp.toU_of_unit`, `decFixed_true_of_false`, `renDec_one_unique_of_fixed` | Unit base field, mode-P fixed point, `IsRenSol`, `rho4≤c6` → first three local; `IsRenSol` generic landed; `hball` open. |
| `analyticOnNhd_physV_of_chart`, `markReal_hdomT_of_hreal`, `markReal_hdomT_of_disc`, `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_disc`, `markReal_fderiv_mask_eq_of_hasDerivAt` | Chart analyticity, radius/derivative hypotheses → `markedEv_joint_physV`, `markReal_disc_slice`, `MarkRealRegular` landed conditionally. |
| `obsRemainder_of_clauses`, `obsRemainder_of_sharpHat`, `obsMarkHalves_of_sharpHat`, `obsMarks_of_tilt` | Sharp-hat expansion, activity `A`, `hW` → sharp-hat input landed only where specified; physical common activity open. |
| `isAnimal_image_blockOf_of_nnConnected`, `clip_of_le`, `f1SiteHaloClip_eq_of_cutoff`, `f1BondHaloClip_eq_of_cutoff`, `blockActivity_eq_zero_of_not_isAnimal`, `allPlus_gas_of_weighted`, `abs_le_of_tendsto_tori` | Geometry/cutoff, weighted gas bounds or limit → local lemmas and `f1_weighted_small` landed within the restricted sector. |

**PROVED. Additional, unmarked conditional headlines.** `sourceActivityC_scale_fromTower` consumes `StepScaleData` (landed by `StepTower.scale` in range); `detGrouped_chart_family_fromTower` consumes tower chart hypotheses (landed from tower);
`markedEv_joint_physV` consumes `CovSetup`, `BlockMargin`, zero tree length (witness at whole torus); `paramMarkFamily_common` consumes all mark regularity (physical producer open); `obsMarks_of_tilt` consumes `hW`, `holt`, `holσ` (physical
producer open); `renDec_sharp` consumes margins (tower-ren producer landed); `renDec_pertClass` consumes `hCB` (numerical producer landed, shared application open); `renDec_one_unique` consumes `IsRenSol` and `hball` (generic existence landed,
`hball` open); `allPlus_gas` consumes weighted halo hypotheses (landed from `f1_weighted_small`); both `c1Star_*_criterion` consume physical convergence/majorant premises (open). The unmarked names are a naming warning, not unsoundness.

## I. Non-vacuity and five repairs

**PROVED. New structures/bundles.** `StepTower`, `StepTowerRen`, `StepOutputConsts` have `exists_stepTower`, `exists_stepTowerRen`, `stepOutput_consts_exists_ge`; `StepScaleData` and `LevelCovers` have `StepTower.scale` plus `scale_instance`
(`ν=0`) and positive-mass instances from the universal scale theorem. `MarkedBlockExpansionDecPair` and `MarkedEvJointPhysV` have `markedEv_joint_physV`/`markedEvJoint_instance`, with nonempty `physV` and mark bidisc but whole-torus `X₁`.
`ObsRemFields`, `ObsMarkHalf`, `ObsRayIdentity` have conditional producers `obsRemainder_of_sharpHat`, `obsMarkHalves_of_sharpHat`, `obsMarks_of_tilt`; no independent physical all-root instance was located. `RenC1Ag` is a local relation, with
reflexive witnesses in `renLocC1_zero_at`, not a physical existence theorem.

**REFUTED. Degenerate-instance overread.** `renC1Cut_levelPair`, `renC1_local_cut_levelPair`, `renDec_row_agree_levelPair`, `renLoc_fibre_levelPair`, and `renDomainParams_levelPair` exercise a whole-torus `X₁` and empty `RenLabel`; none tests a
nonempty cut. `renLocC1_nonempty_scale_one` repairs this *for locC1* at `N₁=18`, `ν=0`. `markedCommonLabels_nonempty` is zero activity/zero mark with a whole-torus base label; `markReal_disc_slice_nonempty` uses `x=0,ν=0`; `detPackage_instance`
uses `β=0,ν=0`; `allPlus_gas_instance` uses `src=0` and omits every heavy/minus sector. Each is a legitimate satisfiability check, not evidence for the stronger physical contribution.

| Order | Bounded repair (each ≤300 Lean lines) | Starting inputs |
|---|---|---|
| 1 | Prove `rho4≤c6` for the chosen tower or restate endpoint uniqueness with a common smaller ball; then instantiate `renDec_one_unique` at `StepTowerRen`. | `RenormEndpoint`, `StepTowerRen`, `RenormExpLemma35`; **OPEN**. |
| 2 | Prove the missing `Jr.W1`/background `physVal` match and combine it with `W2_eq_physVal_sub` and shared labels into one chart `hW` leaf. | `SourcePhysValBridge`, `sourceActivityC_scale_fromTower`, `DirectTermsFamilyOn`; **OPEN**. |
| 3 | Build one nonzero, proper-root mark at a physical chart datum, with the `hF`, `holG`, `contG` fields required by `paramMarkFamily_common`. | `MarkedEvJointPhysV`, `markReal_disc_slice`, `MarkedCommonLabels`; **OPEN**. |
| 4 | Re-run the renormalization cut/row/loc fibre witness at `N₁=18` with two distinct cuts and a proper `X₁`; record a nontrivial term or derivative. | `renLabel_card_ge`, `renYs_second_element`, `renLocC1_nonempty_scale_one`; **OPEN**. |
| 5 | State one exact finite-halo residual object for the clipped all-plus reference and prove its `DepOn` and integrated bound on a fixed proper halo; keep the full-sector identity as a later leaf. | `allPlus_gas`, LF-BASE-KF0 Part F/G; **OPEN**. |

**PROVED. Closeout limit.** All seven groups received a statement-level verdict and the named conditional bundles were traced to their producers or an open input. The refutation pass rejected overreads of label order, complex rotation, `locC1`'s
`M`, mode-P continuation, and one-sector gas closure. Proof bodies were sampled only at these points of use; no fresh Lean build, full theorem proof audit, or class/root closure certification is claimed.
