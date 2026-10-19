# SPINE-PLAN — the remaining work over the Root-F spine (W1127, 2026-10-19; notes only)

Read at main `6fe02c98`: `SPINE.md` (every section), `SPINE-AUDIT.md`, `SPINE-AUDIT-2.md`, `SUBSPINE-AUDIT.md`, `ROOTASM2.md` §3, `PLAN-B.md`
(rulings R7′, R9 pending), `docs/BLOCKERS.md`, `Balaban/Spine/*.lean`. Every name below was checked by `grep`; nothing was built. In flight and not
counted as done: W1126 (Gaussian duplicates of `Base/BasePhysicalDensity.lean`), W1128 (piece-data domain facts, A4-2ab (a)). (?) = not verified to the end.

**Legend.** st: P proved; Rd reduced (assembly proved, named parts open); O open. cov: rough share of the needed Lean that is landed, with the
names that justify it. rem: remaining Lean lines (SPINE.md's sizes where it has them, otherwise mine). R: risk, H = new mathematics or an unresolved
source question. deps: ids below, rulings R7′/R9, Bn = blocker n of `docs/BLOCKERS.md`, G = generalization (§2a), Φ/ΦE = provider maps (§2b). ★ = critical path.

## 1. The tree of open obligations

| id | obligation | st | source | cov — landed | rem | R | deps |
|---|---|---|---|---|--:|:-:|---|
| RF | `rootF_of_spine` | P | frozen Root-F | 100% | 0 | – | the seven inputs |
| A1 | `PrefixInput` | P | LFR §I.1.4 | 100% — `prefixInput_exists` (all `d ≥ 3`, `L ≥ 3`) | 0 | – | – |
| A1′ | the provider's constants `T, P6, C7, PB, cs₀, M1, c, rH, ϱ` (functions of `κ, c₉`) meeting every sub-input: the chain asks `7 ≤ C.m₀`, `3^{m₀} ∣ N₁`, `ϱ = rhoSep m₁`; `prefixInput_exists` takes `m₀ = 1`; `T.m₀ = 1` of `StepTowerG` vs `C.m₀` (?) | O | LFR rows 0–15 | 60% — `prefixInput_exists`, `flowRateInput_of_prefix`, `exists_classConsts_eps_one` | 400 | L | all; last |
| A3 | `BaseStepInput` | Rd | LFR Thm II.7.10 | `baseStepInput_of_parts`; `∫ρ₁ = Z(g)` (`integralIsZ_firstDensity`) | – | – | A3-1, A3-2, A4-2 |
| A3-1 | `BasePreStepInput` (`k₀ ≥ 1`, `ρ₁ ∈ ℛ^pre_1`) | O | Prop. II.7.9; P4 (2.42)–(2.54) | 35% — `Base/` (rows below) | 4,700 | H | R7′, R9, B1, B2 |
| (a) | small-field part at scale 1: first fluctuation integral (the engine's `XSetting` asks `a_k ∈ [1/2,2]` and `FlCore.hPmp` a lower generating set, neither exists at `k = 0`); ν-free system; (H.5), (H.6) at 1; `ℛ^{(1)}_m`; `ℬ^{(1)}` | O | Prop. II.7.9; P5 Prop. 3.2 | 25% — `baseCovX_bound`, `baseDGSetting_exists`, `baseActivity_LabelAct` | 1,800 | H | B2 |
| (b) | base kernels `K̃⁰e^{b₀}` in the R7 carrier (D4 cross-witness identity) and (II.7.5) with the gain `κ^{(0)}`; margin across `∂Ω″` (`bondCross`) | O | Lemmas II.7.7–8; P5 (1.31) | 40% — `baseKC_eq_baseK0_mul_exp`, `baseFirst_operator_majorant_of_fiveShares`, `baseCutoffTransfer` | 1,000 | H | R7′, B1 |
| (c) | transform relation `D1PreForm2` for `firstDensity` | O | BASECARRIER item T | 30% — `baseRho1_eq_sum_firstP`, `baseRetained_disintegrate` | 800 | M | (b), (d) |
| (d) | carrier frame at the class's `M ≥ 14`, `K ≥ 2` (now `M = K = 1`) | O | ruling R7′ | 70% — `BaseSmallFieldInput`, `baseStepData_of_input` | 400 | L | R7′ |
| (e) | (H6′)^pre at scale 1, truncated counter (base case Lemma II.7.2 (e)) | O | LF-2 (i) | 60% — `Rep.budgetFlat_of_LF2_trunc` (model), `BudgetSetupTo` | 300 | L | (d) |
| (f) | (D8) of `K₀, b₀, ℬ^{(1)}` | O | Thm II.7.10 (d) | 40% — `bgLocPiece_twoTorus`, `quietKernel_twoTorus` (model) | 400 | M | (b) |
| (g) | `β₀ = β`, `ν₀ = ν` | O | construction | – | 20 | L | (a) |
| A3-2 | `BaseFlatStepInput` (`k₀ = 0`): A3-1 (a)–(f) at complete backgrounds with P4's system; (H6♭) at 1 by `Rep.budgetFlat_of_LF2_trunc`; `ν₁ ≤ 9/10` from the bound of `ξ^{(0)}` | O | Thm II.7.10 (B), (D9♭) | 35% — as A3-1, `exists_good_lamHat`, `hLam_window` | 800 | M | A3-1, R9 |
| A4 | `ClassStepInput` | Rd | LFR Thm IV.3.2 | `classStepInput_of_parts` | – | – | A4-1, A4-2, A4-3 |
| A4-3 | `FlowRateInput` | P | Thm IV.3.2 (d) | `flowRateInput_of_prefix` | 0 | – | – |
| A4-1 | `SFStepInput` | Rd | Thm IV.1.1 | `sfStepInput_of_parts` (`sfSucc_clauses`, `integralStep_stepDensity`) | – | – | ★ A4-1a–i, Φ, ΦE |
| A4-1a | `SFInheritInput` | O | I-9; R6 | 90% — `liftOldTermsFam`, `oldTorusEquiv` | 50 | L | Φ |
| A4-1b | `SFNewLevelInput` | O | P3 (4.44)–(4.47); P4 Prop. 4.1; R8 | 40% — `e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot`, `localClass_newLevel_of_expansion_cast`, `newLabels_castInputs_of_localFamily`; W1144: route R-LOC for (iii) (SPINE.md "A4-1b (iii)"); W1147: R-LOC L2 done; W1146: R-LOC L3 done | 6,150 | M | ★ G, Φ |
| (i) | the cast theorem's conjunction ⇒ `SFTermClauses` of `newLevelTerms` (`birthXiDom_dom_self` at the top level) | O | – | 80% | 150 | L | – |
| (ii) | the chain's premises at the composed data: `hEbd`/`Bτ` of `irrelTorus`, `hchart`, analyticity of the old densities along the path, `hεnum` | O | P1 (3.128), Lemma 2.1 | 50% — `irrelTorus`, `norm_filed_le_power` | 600 | M | G |
| (iii) | (A1)–(A5) on `𝔹_{k+1}(Y⁺(T′))`, route R-LOC (W1144; SPINE.md "A4-1b (iii)"): the chain returns its family as the formula `newLevelCoeffBg`, `f` is the formula on `Gb(T′)`. (B4): the read datum lies in the local chart only at `K_loc ε` (necessary ≥ 2ε, `collarBond`), but only the identities (A3), (A5) see it, at absolute smallness; (A1), (A2), (A4) are on the local chart of radius `ε_{k+1}` with the step's room. L1 (formula, base layer `StepTowerG.e0CoeffFamily_class_agree_rot_formula`), L1′ (gate radius, determinant half of (A5)), L1″ (determinant clauses without `HatConn`), L2 (a)–(d) **P** (W1147: the formula is forwarded through the chain as `NewLevelFormula`/`NewLevelSystem`, `Inhabited/NewLevelSystem.lean`), L3 **P** (W1146: replacement of every activity and mark at the read datum; (A5) reduced to the determinant part, `newLevelCoeffBg_class_canon_eq_of_det`; for the system, `NewLevelSystem.coeff_eq_coeffBg_canon_of_det`, with the locality of the marks a field of the system, `NewLevelSystem.G_dep`); open: L4 Lemma 4.2 at `Gb` (3,800), L5 assembly (300) | Rd | ruling R8 | 45% — R8 objects (W1129, W1138, W1139), W1141 castG cores, W1144 L1–L1″, L2 (a); W1147 L2 (b)–(d); W1146 L3 | 4,100 | M | ★ L4 Opus |
| (iv) | castG versions of `LocalPairDepth`, `LocalPairLevelInner`, `localHatLift_eq_hatPsiF_localB`, `localB_collar_margin`, `localB_tauExt_*` | D | – | 100% — W1141: cores for an arbitrary generating set `Gl` (landed `localB` statements are instances), `Balaban/Fluctuation/LocalPairCast.lean` verifies SupSep/CubeAligned/top-layer/drop/collar-margin/`tauExt_eq_one`/chart restriction for `castG hc (localB …)` | 0 | – | – |
| (v) | the step on every Def-6 torus `N₁ ≥ 1` (`D2SF2`, `SFFlat2`); the chain has `3 ∣ N₁`, `5 < N₁`, `3^{m₀} ∣ N₁` | O | – | 0% | 600 | M | R-N₁ (§2a) removes it |
| A4-1c | `SFRenormInput`: (H.6) at `k+1` (~150); (H.5) with `D_E = ℰ''₀(θ_ξ) + oldE + C₁ + C₂ − vac` (`oldE` of a general class, physical `locC2`, `locDφ`, `renE0_fibre`); `D_M`, `T_M` beyond the zero class | O | P4 (4.14)–(4.22), (5.28) | 40% — `rg_step_infty`, `renLocC1_scale_of_tower`, `renLoc_fields_scale_of_tower_at` (3,3,2) | 1,500 | M | ★ G, Φ |
| A4-1d | `SFDensityInput`: reality of the new level's terms and composites at real data | O | P4 (H.1) | 20% — Lemma IV.1.3's `Δ` real, `IsSF2.density` | 400 | L | Φ |
| A4-1e | `SFRemainderInput`: `RTermsH4 … preFac` for `ℛ^{(k+1)}_n` | O | P5 Props 3.1–3.4; LFR Lemma IV.1.8 | 5% — only `rTermsH4_mono`, `rTermsH4_add` | 1,500 | M | ★ Φ |
| A4-1f | `SFCoherenceInput`: `D8SF` of the new level and `ℛ^{(k+1)}`; W1144: with R-LOC L2 the chain's `e` is the formula `newLevelCoeffBg` (`NewLevelFormula`), so the obstruction of W1090 becomes two-torus agreement of each object of the formula: `AC`, `G₁` from D8 of the inherited levels and W1089's `decSol`/`evDec`, the core objects by W1089 | O | Thm IV.1.1 (h); D-IV.9 | 30% — `e0CoeffFamily_value_fromTowerG_core_twoTorus`, `coreE0_unique`, `liftOldTermsFam_M_eq_of_d8`; L1 (`…_agree_rot_formula`) | 700 | M | ★ R-LOC L2, A4-1e |
| A4-1g | `SFVacuumInput`: `|ΦE| ≤ C_b(log β′_{k+1} + 1)` from `|g_k| ≤ A log β_k + B` and the step normalization `s` (the tie is W1125's `vacExt`; `s` is a free output of A4-1h) | O | P4 (2.1), (2.41), (2.63); R5, R5′ | 95% — W1132: `vacMap` (= Gaussian increment `Γ_k`, `e₀` into `s`), `sfVacuumInput_of_inherit_renorm` (premises: A4-1a, A4-1c, ranges `p ≥ 1`, `Cb ≥ vacConst`); remaining: confirm the `e₀`-into-`s` convention | 30 | L | – |
| A4-1h | `LFStepInput` | Rd | LF-3 (b)–(d), (h); P5, P6 §§2–3 | W1136: `lfStepInput_of_parts` (`Spine/LFStep.lean`) on the step map `Λ : LFStepMap` (`LFStepRaw`: histories, kernels, `ℬ^{(k+1)}`, `s`); `cs'`, `P'` (`succOpConsts`, `succBudgetConsts`) and the kept data `succKD` defined, their clauses proved; `IsRepPre2`, (D7) v2, the tie assembled; SF→LF interface not needed (SPINE.md) | 6,750 | H | Φ, R9, R10, B2, B3 |
| (c) | `LFHistInput`: the histories of `Λ` complete up to `k+1` | O | LF-3 (c); Def. I.3.1, (R8) | 30% — `exists_isComplete` | 300 | L | – |
| (g1) | `LFStepDataInput`: `∃ StepData` at `cs'` with `ker = Λ.ker`, tied to `vacExt rec.Ev k ΦE`; non-quiet kernels P5 (2.47)·P6 (3.2) with local backgrounds; at the old steps the tie is the A4-2v estimate | O | Lemmas II.5.14, IV.1.3, 4, 6; (S0); R5, R5′ | 25% — `quietStepData'`, `StepData.retie`, `norm_stepVacuumTerm_le_of_stepData` | 1,700 | H | R9, R10 |
| (g1′) | kept data (S3): `succKD` = `KeptData.upTo` of the input's | P | (S3) | 100% — `KeptData.upTo`, `chiDomAt_congr` | 0 | – | – |
| (g2) | `LFBdryInput`: `D7Bdry` of `ℬ^{(k+1)}` at the physical field, `B_st`, `3κ/2`; old terms across a new hole | Rd | Lemma IV.1.5; P6 p. 34 | 40% — W1140: `lfBdryInput_of_parts` (`Spine/LFBdry.lean`; parts `LFBdryNewInput`, `LFBdryDeltaInput`, `LFBdryOldInput` on the split `LFBdrySplit`), `norm_sum_le_of_transfer`; blocker 3 located (π′-shape of hole sites) and its piece proved under R11 (`Def7.exists_transfer_fineValidFinAt`, `transfer_patches`, `Spine/LFBdryHole.lean`); leaves O2, O4 and the cube part of O3 proved (`d7Pull_OmegaCube_succ_subset`, `le_d7SizeAt_of_reach`, `FineValidFinAt.dmodOmega`); open O1 (analytic re-expansion), O5 (entropy, after R11), parts (i), (ii) (SPINE.md) | 1,000 | M (after R11) | R11, B3 |
| (g3) | `LFFormInput`: `D1PreForm2` for `stepDensity … Λ.s ρ` with every `vc'` of `D1CorrLim` | O | P5 (2.1)–(2.48), §3, (1.8); P6 §2, (3.3) | 20% — `stepDensity`, `integral_stepKernel_mul`, `preOpTop_congr` | 1,200 | M | (g1), Φ |
| (g3′) | `LFOpBoundInput` (`D5Bound`) | P | Lemma II.6.3 (a) | 100% — `lfOpBoundInput_of_signs` from `LFSignInput` | 0 | – | – |
| (z) | `LFSignInput`: `z_j > 0`, `1 ≤ j ≤ k+1` | P | P1 (1.11), P4 (4.1) | 100% — W1142: carrier field `zpos` on `RepRec`/`PreRec`, `lfSignInput_of_inherit` from `SFInheritInput` | 0 | – | – |
| (g4) | `LFPinInput` (`D4Pin (k+1)`: the histories of `Λ` restrict to those of `rec`, whose pins and kept data they keep) | O | (D4); LF-3 (c) | 10% | 300 | L | (c) |
| (g4′) | `LFBudgetInput` (`D6Pre` with (I.2) to `k+1`) | P | LF-2 (i) | 100% — `lfBudgetInput_of_pin` (prefix, `Rep.budgetPre_of_LF2_trunc`) | 0 | – | – |
| (g5) | `LFBdrySrcInput`: `D7BdryBall` (complex `h'` of the pinned ball): the activity bound on the transverse source radius | O | blocker 2 leaf 5; Q13-YM §§2, 5 | 50% — R2 objects (three masses, `chiY`, `KerBoundSrc`) | 600 | H | B2 |
| (h) | `LFCoherenceInput`: `LFCoherent` of the successor | O | LF-3 (h), D-IV.9 | 30% — (D8) of `rec`, `quietKernel_twoTorus`, `bgLocPiece_twoTorus` | 1,000 | M | (g1), (g2) |
| (h′) | `LFCorrInput`: `∃ St' vc', D1CorrLim` of the image | O | P1 (3.106)–(3.110); P5 (1.8) | 10% — `wD1Corr` | 400 | M | Φ |
| A4-1i | `StepIntegrableInput`: a (D1) sum is integrable, from (D5) and Gaussian decay | O | P1 (1.11) | 20% — `baseRho1_integrable` (first density only) | 300 | L | – |
| A4-2 | `RInput` | Rd | Thm III.10.8; Lemma III.8.4 | `rInput_of_parts` | – | – | A4-2v, A4-2ab |
| A4-2v | `RVacuumInput` = `rVacuumInput_of_b0`; open `RVacuumB0Input` (`RecB0Bound`): vacuum-region volumes against `|Z_{k+1}∖Z_k|`, `|δ″_k|, |δ‴_k| = O(log β_k)` | Rd | P4 (2.1), (2.41), (2.63), (4.21) | 30% — R10 LANDED (W1148): region 1 is now `(Z_{k+1}∖Z_k)∖Ω`, excess 1 is gone; open: geometry `|Ω_{k+1}∩Z_k| ≲ |Z_{k+1}∖Z_k|`. Was OBSTRUCTED (W1134): `stepVacuumTerm`'s first region `(Z_k)ᶜ ∖ Ω` is a complement in the whole fine torus (records are intersected with `Z'`, the complement is not), so it contains the fine set of `Z'ᶜ` and `RecB0Bound` is not derivable (`compl_fineSet_subset_vacuumRegion`, `norm_vacuumTerm_le_of_b0Bound`); needs Scott's ruling: region 1 := `(Z_k)ᶜ ∩ Z_{k+1} ∖ Ω` (then excess 1 is empty), then geometry of `Ω ∩ Z_k`. Also `PreRec.retie`, `stepVacuumVolume_eq_add_excess` | 400 | M | |
| A4-2ab | `RKeptGasInput` | O | P7 (3.1)–(3.29); R4 | 50% (rows below; (a): piece domain at small radius proved for every piece of the window family, ancestors included (W1150), and the premises hS, three XiCOneReal families, InDomainR delta_l derived from it under the size conditions; W1153: hret dropped (removed window component), hS and the XiCOneReal/InDomainR families in the delta-regime at the radii pieceRadiusWin, c1 (window_domain_clauses_of_regime); open: InDomainR 0 delta_u Du (W1060), hnamedC.1 as output of the Du sum theorem (hp7, hwdec), hunit for KerBound over all hv, the mass condition 2 mu_act L^(2(j+1)) < radius^2 as a choice of nu) | 5,900 | H | B4, A4-2v |
| (a) | window bound: `hnamedC.1` (W1123 `windowSideConds_exists`; W1135: `hnamedC` over `K ≠ 0` points, `window_pieces_hS`, `exists_window_decomp` (`hwt1`/`hcells`); W1143: the chain takes `K·wt ≠ 0` (`wt` = the to-R weight `t s z w`), `chiDomAt_of_locOp_kernel_ne_zero`, `deltaRun_le_epsSeq` (δ-regime `C δ_j ≤ ε_{j+1}` for λ̂₀ large); left: R1/R2 at radius ≤ min(δ_l, ε_{j+1}/(2K₁+2)) at the data sites of `G_i` outside `nbhd 1 Z` at scale `m'+1` — reached by no factor of the removed-kernel integrand (`F`), only by the post weight (`χ_Y`, retained `ChiDomAt`, D1), so `hnamedC` needs a post-weight support premise (orchestrator decision) — then the transfer locGen datum = `parentPsi` on the shell and the layer matching inside `Z'`; `Du` R1, the closure inequalities), Q-part of `hnamedC.2` at the physical collar | O | P7 Step 1; COLLAR-FIX 1.2 | 80% — `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du_consts`, `removedKernel_kerBound_of_hid_action_cl`, `genSet_stability_core`, `window_pieces_hS` | 450 | M | W1135 |
| (b) | (3.10″) for the actual removed operators; (H-op): hole closure, two PE inequalities, product measure; `hosc`; `OutT ↔ BlockField` | O | P7 (3.7)–(3.10) | 50% — `lf4R_removed`, `r4HeavyActivity_bound`, `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel` | 1,500 | H | (a) |
| (c) | `ℬ′`: an explicit construction (P7 fixes only aggregates) and its tie to `Rep.B` | O | P7 (3.22)–(3.25) | 40% — `RopC`, `rhoSigma`, `gasR4DecorOp_eq`, `r4Fresh_aggregate_of_localization` | 1,000 | M | (b) |
| (d)(e) | vacuum cancellation with `VacuumTied`; integrability of the normalizations | O | P7 (1.7) | 70% — `R_normalizationPhysical`, `StepData.VacuumTie.removed_weight_shift` | 400 | L | A4-2v |
| (f) | (D8) of `ℬ′` and `ℛ''` (`D8SF.R_eq` from the input `LFCoherent`) | O | D-IV.9 | 20% | 500 | M | (c) |
| kept | `ϰ₄`, `ϰ₅` (`hquot`); `D4Pin`, `D5Bound` (`locOp` at ripe components), `D6Budget` (strict `k < t*`), OPEN-R-HISTORY-ENUM | O | Thm III.8.9 (a), (b) | 50% — `keptKernel_one/two/three_kerBound`, `isComplete_succ_of_enum`, `pin_succ_of_pin` | 1,000 | M | – |
| gas | `RTermsH4` of `ℛ''` (OPEN-R-RM-H4); `D1Form2` of `ρ'`; `D7Bdry2Post` (OPEN-R-D7-PHYSICAL) | O | P7 (3.26)–(3.29) | 40% — `d7Post_bound_of_avoid_of_gas`, `isRep2_of_isRepPre2_of_fields` | 1,000 | M | (b), (c) |
| A4t | `TransferInput` | P | Lemma IV.2.1 | `transferInput_of_prefix` | 0 | – | – |
| A4f | `FrozenStepInput` | Rd | Thm IV.2.2 | `frozenStepInput_of_parts` ((I.2), `ν_{k+1} ≤ 9/10` inside) | – | – | ★ A4f-1 |
| A4f-1 | `FrozenSFStepInput`, not yet split: (1) a sub-spine on maps `Φ♭`, `ΦE♭` reusing `sfSucc_clauses` (~300); (2) A4-1a–g, i at complete backgrounds; (3) the switch at `k = k₀` (FLUCTUATION Lemma 2.9); (4) frozen large-field data (no hull, no `R`; `B_st ≤ B₀ − 1`; (H6♭) by `Rep.budgetFlat_of_LF2_trunc`) | O | Thm IV.2.2; P4 Thm 1 | 25% (A4-1's pieces, when generic in the regime) | 3,000 | M | ★ A4-1, R9, B2 |
| A6 | `LastIntegralInput` | Rd | Thms IV.4.1, IV.5.3 | `lastIntegralInput_of_parts` | – | – | A6-1–4 |
| A6-1/2 | `InheritedBoundInput`, `InheritedAgreeInput` | P | Thm IV.5.3 items 2, 4, 5, 7 | `inheritedBoundInput_of_prefix`, `inheritedAgreeInput` | 0 | – | – |
| A6-3 | `FinalSmallFieldInput` | O | P4 §6; P7 (4.1)–(4.9), (4.15)–(4.17) | 45% (rows below) | 3,000 | H | B5, B7 |
| (a) | `sfIntegral` as the cut expansion: massive final problem, Gaussian change of variables, `det(U+E)/det(U)·J`, `F_{k_f} = Σ_{j ≤ k} Edens`, the block datum in the class chart (`hθ`), the datum lemma beyond `k₀` | O | P7 (4.3)–(4.6); FINALPHYS3 §8 | 50% — `cutoffInteraction_final_class_polydisc_local`, `norm_coef_cutoff_class_le_levels_of_large`, `abstract_expansion_taggedCfin_final`, `finalSelectedDatum_inDomainR` (`k ≤ k₀`) | 1,200 | M | – |
| (b) | the source part `⟨g, φ̄_k⟩ − ⟨g, h⟩` and the change of `ℳ^{(j)}` as scale-`(k+1)` terms | O | ROOTFFAM §3 | 30% — `Green/FinalCrossTerm`, `Green/FinalHessian` | 500 | M | (a) |
| (c) | regrouping `Y ↦ Ȳ`; cells to fine sites | O | ROOTFFAM target 4 | 50% — `rootF_sites_of_cellClause`, `sitesOf_isPolymer` | 300 | L | – |
| (d) | exact two-torus agreement of `a`: complete localization, the winding remainder on winding polymers | O | P6 p. 3; SPINE-AUDIT-2 (d) | 25% — closeness only: `finalCoef_close_quarterBox_weighted`, `resum_lastScale_limit` | 800 | H | B7 |
| (e) | amplitude `c₉/4` | O | prefix ties | 60% — `betaK_inv_sq_le`, `norm_kf0Deriv_le_two` | 200 | L | (a) |
| A6-4 | `FinalLargeFieldInput` | O | P7 (4.9)–(4.14); Lemma IV.4.2 | 35% (rows below) | 3,000 | H | B5 |
| (a)(b) | define `𝕋'_{k+1}(Z′, 𝔸′)`; `∫ρ = Σ_{Z′} 𝕋′(Z′)[…]`; the completion (4.11): the empty history gives `Ξ^sf` | O | P7 (4.7)–(4.11); P5 (3.18) | 20% | 1,000 | M | – |
| (c) | (IV.4.1) for the weights (`H^fin`, frozen threshold); couplings `ℬ''` on cells meeting `Z` (gap L4, item 18); the linked-gas hypotheses | O | Lemma IV.4.2; item 18 | 40% — `gasLinked_activity_bound`, `final_tail_gas_bound`, `final_large_integral_eq_gasXi_of_factorization` | 1,200 | H | (a)(b) |
| (d) | exponentiation (PE-L), regrouping, agreement (PE (f) with `LFCoherent`, `D8SF`), amplitude (Λ32) | O | P7 (4.12)–(4.14) | 50% — `gas_eq`, `pe_PY_bound`, `gasLinked_coverage_activity_bound` | 800 | M | (c) |
| A7 | `KfZeroInput` | Rd | Prop. IV.4.3; LF-BASE-KF0 | `kfZeroInput_of_parts` | – | – | A7-1, A7-2, thr |
| thr | the provider's `thr` with `0 < thr ≤ √2`, as a premise of `kfZeroInput_of_parts` (SUBSPINE defect 3b) | O | KF0-INFL | `not_kf0GoodSectorInput_of_thr_nonpos`, `kf0BadSectorInput_of_two_lt` | 50 | L | – |
| A7-1 | `KF0GoodSectorInput`: (a) the physical threshold is not local in `ψ`, so the good sites with a large Gaussian variable must be expanded (400, H); (b)–(e) complex source, clipped walk terms, regrouping with exact two-torus agreement, amplitude (F.13) (800, M) | O | LF-BASE-KF0 F.2, E.4, Thm F.1 | 75% — (b)–(e) done (W1145, `kf0GoodSectorInput_of_threshold`); only (a) `KF0ThresholdInput` open | 400 | H | B1 |
| A7-2 | `KF0BadSectorInput`: (a)–(c) `CompleteHeavyLocality`, the integrated linked hard-chart estimate (KF0-LINK §5), reversed spins as a linked gas (KF0B Thms B.1, B.7) (1,500, H); (d) exponentiation with exact lifts, amplitude (500, M) | O | LF-BASE-KF0 D, E, G; P7 (4.11) | 30% — `kf0SectorLint_le_peierls`, `kf0BadFactor_le_gas_charge`, `kwOp_inv_sub_trunc_hasSum`, `gasOp_pe_hole` | 2,000 | H | B1; A6-4 (c) |
| RC | Root-C beyond the spine: `C1Star` at `(κ_*, 1)` (F1 running `ξ`, continuity at `ν = 0`; F2; F3) | O | Thm IV.5.4; OBS 3.1, 5.2 | 40% (?) — `rootC_of_spine`, `C1StarFromStep*` | 3,000 (?) | M | A4; Roland's β question |

## 2. Cross-cutting work

**(a) G, the generalization of the class chain** from `StepTower`/`StepSetting 3 3 N₁ … 2`/`StepClass 3 3 …` to `StepTowerG d L N`. Fixed at `(3,3,2)`:
45 files of the class chain (by a name filter), 15,392 lines (`Inhabited/StepTower{Collar,Chain,Beta0,Rot,Ren}*`, `Fluctuation/LocalClassDensity{Irrel,Family,Val}*`,
`Inhabited/Renorm{E1,M0}SiteRecord`); 125 fixed files (40,050 lines) in all; 160 files (73,233 lines) already mention `StepTowerG`. Method: cores
at `StepTowerG`, the `(3,3,2)` theorems their instances (no copies). Needed by A4-1b, A4-1c, A4-1f and, through them, A4f-1; not by A3 (`Base/` is general
in `d, L`), A4-2 (general `Setting`), A6 (`Green/` is general in `3 ≤ d′`, `3 ≤ L`, `N`), A7. Root-F is stated for every `d ≥ 3`, `N ≥ 2`, so G is
mandatory, and every new class-chain line written at `(3,3,2)` adds to it. The R8 objects are already general (`StepSetting d L …`),
so G runs in parallel with R8, and (A1)–(A5) are written once, at `StepTowerG`. Size ≈ 6,000 (4,000–9,000;
GENDN: 6,000–12,000 for all 50 endpoint files), 10–14 Sonnet tasks, M (numerals `c1 3 3`, collar 327, centred collar for odd `L`, GENDN).
*The Def-6 torus index (ruling candidate R-N₁, not asked).* `D2SF2.sfClass`, `SFFlat2.torus` and the sub-inputs quantify over every `N₁ ≥ 1`, while
`RepFam` reads only `sfIdx L m₀ n k = L^{m₀} n_k` (`sideDiv_eq_sfIdx`), on which the chain's `3 ∣ N₁`, `5 < N₁`, `3^{m₀} ∣ N₁` hold at `L = 3`
(and `L ∣ N₁`, `L^{m₀} ∣ N₁` in general). Restricting the two clauses to `N₁ ∈ L^{m₀}ℕ₊` (11 files use `D2SF2`/`SFFlat2`) removes A4-1b (v) and the
small-torus cases where the non-winding hypotheses fail. Recommended: ask it.

*Order of G: bottom-up by import depth (W1130, W1133).* The collar chain `StepTowerCollar{Base,Core,X}` cannot be generalized first: its proofs call about 50 declarations of the lower `Inhabited/StepTower*` layers, which are fixed at `StepTower`/`StepSetting 3 3 … 2`/`rhoSep`. G therefore runs from the bottom of the chain's import order. Layers (fixed = still at `d = L = 3`): 0 `SourceDirectTermsFromTower`, `StepTowerCollarBgSet`, `StepTowerCollarTower`; 1 `SourceActivityFromTower`; 2 `MarksNumericsFromTower`, `SourceExponentFamily`; 3 `ActivityFamilyAnalytic`; 4 `ZeroSourceActivityCommon`; 5 `StepTowerBeta0Marks`; 6 `E1MarkParamCommon`, `StepTowerBeta0Amp`; 7 `OffFibreE1Marks`; 8 `OffFibreE1Compare`, `StepTowerRotZero`; 9 `E1CoeffFamily`, `OffFibreE1Value`, `StepTowerBeta0Zero`; 10 `OffFibreE1CoeffSum`; 11 `OffFibreE1Activity`, `OffFibreE1Family`; 12 `OffFibreE1CoeffValue`, `StepTowerRotClass`, `StepTowerRotFields`; 13 `StepTowerBeta0Class`, `StepTowerBeta0Fields`; 14 `StepTowerRotLabels`; 15 `StepTowerBeta0Labels`; 16 `StepTowerRotFamilies`; 17 `StepTowerBeta0Families`; 18 `StepTowerBeta0Red`; 19 `StepTowerCollarCore`; 20 `StepTowerBeta0IrrelCore`, `StepTowerCollarX`; 21 `StepTowerBeta0IrrelX`, `StepTowerCollarBase`; 22 `StepTowerBeta0IrrelBase`, `StepTowerCollarScales`, `StepTowerCollarStruct`; 23 `StepTowerBeta0Struct`, `StepTowerCollarStep`; 24 `StepTowerBeta0Step`, `StepTowerCollarUniform`; 25 `StepTowerCollarClass`; 26 `StepTowerRotChain`, `StepTowerRotChainRen`. Already general: `StepTowerBeta0{Core,Margin,Scale,Src}`, `StepTowerRotOld`, `E1CoeffFamilyG*`, `E1MarkParamCommonG`, `OffFibreE1ActivityG`, `ZeroSourceActivityCommonCore`. Check of W1133: layers 0 to 3 (`SourceDirectTermsFromTower`, `SourceActivityFromTower`, `MarksNumericsFromTower`, `SourceExponentFamily`, `ActivityFamilyAnalytic`) already hold their cores at `StepTowerG`/`StepScaleDataG`/`rhoSepG` (`…_fromTowerG_*`, `StepTowerG.exists_beta0_marks`, `activityFamilyAnalytic_of_witnessG_rho`), and the `(3,3,2)` theorems are their instances through `T.toG`, `StepTower.scaleDataG_of_fixed`, `rhoSepG_three`; the next work is layer 4 and up. The `Beta0*` corollaries (`Beta0Irrel{Base,Core,X}`, `Beta0Struct`, `Beta0Step`, `Beta0Class`, `Beta0Labels`, `Beta0Fields`, `Beta0Zero`, the non-phi `Beta0Families`/`Beta0Red`) are (3,3) corollaries, left fixed by design (they reach G cores through instances).

**(b) The provider constructions the sub-spines take as data.**
* `Φ` (A4-1): the small-field step map `SFData k → SFData (k+1)`: the data of `sf` at `j ≤ k` with `liftOldTermsFam`; `β′ = β_k L^{d−2}/(1+ξ₃)`,
  `ν′ = ν_k L²(1+ξ₃)/(1+ξ₂)`, `a′ = compWeight`, `z′`; `Tm′` the splice of the inherited levels with the new level (the labels recomputed on
  `𝔹_{k+1}(Y⁺(T′))` and regrouped on `𝒟^{(m₀)}_{k+1}`, plus `D_E`, `D_M`); `Rt′` the `ℛ^{(k+1)}_n` of P5 Props 3.1–3.4. Rule 4: `ξ^{(k)}` is "the
  unique solution", so its `∃!` (existence: `rg_step_infty`) and a characterization land first. A total function (the same formula off the class).
  ≈ 1,200 + an independent audit; after G, A4-1b (iii); M. ★
* `ΦE`: DONE (W1132): `vacMap` = the Gaussian increment `Γ_k` of the step (`Spine/SFVacuum.lean`); the forward flow `L^d E_k − e₀/|T|` is the normalization `s`.
* `Φ♭, ΦE♭` (A4f-1): the same at complete backgrounds; inside A4f-1's 3,000.
* The first density: landed (`firstDensity` reads `baseRho1`; `integral_firstDensityAt`).
* `thr` (A7): `δ_β = A log(βa)/√(βν)` — DONE (W1142): `kf0Thr A a β ν`, `kf0Thr_range` (range `0 < · ≤ √2` in the regime `7/8 < νL²`, `β ≥ β₀`), `kfZeroInput_of_parts_kf0Thr`. The constants `A > 0`, `a > 1`: A1′.
* Not provider data: the outputs `lf′` (A4-1h), `lf₁, ℬ′, ℛ″, ρ′` (A4-2ab), `a, E, b` (A6-3/4, A7) are existentials built inside the proofs.

**(c) Non-vacuity at the used configurations (rule 10), blocked on R9.** `RepRec`, `PreRec`, `FlatRep` at `kf ≥ 1`, `K = kf + 1 ≥ 2`, with `K` up to
`log_9(27β)`: zero terms, histories up to `K`, `QuietStepInput'` on every torus `nK` (its `real_euclid` fails for `nK ≥ 2` until R9: W1124),
`LFCoherent` of the quiet family (`quietKernel_twoTorus`, landed), `D4Pin`, `D6Flat` at `k̂ = kf`, the zero flow (`vacuumFlowTo_zero`). ≈ 1,200, M,
plus the R9 change itself (`sides` = 1 above `K`, `hsub` weakened in `History/ImageHist{,Book}.lean`, `Inhabited/QuietImage.lean`; `sides` is in 148
files (PLAN-B); repairs ≈ 300–800 (?)); without R9 the rewrite along `HistImage` orbits is ≈ 1,200. Do it early: an empty class at the used configurations makes every
`∀ ρ ∈ class` input vacuous, and the witness is the check that the carriers are consistent at `K ≥ 2`.

## 3. Order of work (waves of ≤ 3: 1 Opus + 2 Sonnet), critical path ★

R7′ and R9 are with Scott; R-N₁ should be asked now. Wave 1 starts as W1126 and W1128 land.
* **Wave 1.** Opus ★ R8, part 1: generic `decMarkG`, `decMarkCorr`, `decMarkCorrTerm`, `e1MarkGParamG` over an explicit background generating set,
  the current objects their `S.G'` instances (definitionally), the first lemma layer, an audit packet (~600). Sonnet ★ G slice 1:
  `StepTowerCollar{Base,Core,X}` (1,909 lines) as cores at `StepTowerG d L N` (~600). Sonnet: the R9 change if approved; otherwise A4-1i and `thr`.
* **Wave 2.** Opus (DONE, W1136): split A4-1h (`Spine/LFStep.lean`, `lfStepInput_of_parts` from (g1)–(g5), (h), each with statement, source, coverage, size; decide the
  SF→LF interface watch item) (~600). Sonnet ★ G slice 2: `StepTowerCollar{Struct,Step,Class,Uniform}`, `StepTowerChain*`. Sonnet: the `K ≥ 2`
  witnesses of §2c (after R9); otherwise A4-1g with `ΦE`.
* **Waves 3–30, Opus lane** (one task per wave, H items as early as their inputs allow, so that one that fails does so early): 3 ★ R8 part 2
  (`DetExpansionLocC`, `DirectTerms`, `physParam`/`physV`); 4 (g2), blocker 3; 5 A4-2ab (b), (3.10″); 6 A6-4 (c), L4; 7 A7-2 (a)–(c), first pass;
  8 (g5), blocker 2 leaf 5; 9 A3-1 (b) (after R7′); 10 ★ `Φ` with the `∃!` of `ξ^{(k)}` (after G and (A1)–(A5)); 11 A6-3 (d); 12 A7-2 second pass;
  13–14 A3-1 (a); 15 `ℬ′` (A4-2ab (c)); 16 A7-1 (a); 17 audits of the R8 objects and `Φ`; 18–19 ★ the split of A4f-1 on `Φ♭`, the switch at `k₀`;
  20 audits of `ℬ′`, `𝕋′`; 21–30 second passes on the H items that need them, then A3-1 (c)–(g), A3-2, A1′ and ★ the provider of
  `Provider/LogPartitionMultiscale.lean`, closing Root-F by `exact rootF_of_spine …`.
* **Waves 3–30, Sonnet lanes** (two tasks per wave, in this order): 3–6 ★ G slices 3–5 (irrelevant-part chain, family and value towers,
  `renLoc*`), ★ A4-1b (iv) and (A1)–(A5) of (iii), A4-1g with `ΦE` or the witnesses (whichever wave 2 left), A4-2v `RecB0Bound`, A4-2ab (a) after
  W1128; 7–16 ★ the rest of G, A4-1b (i), (ii), (v) unless R-N₁, then (after `Φ`) A4-1a, c, d, e, f, (g4), and A4-1i, `thr` if wave 1 did not; 17–22 ★ (g1), (g3), (h), A4-2ab kept,
  gas, (c)–(f): milestone `ClassStepInput` at general `d, N`; 23–26 A6-3 (a), (b), (c), (e), A6-4 (a)(b), (d); 27–30 ★ A4f-1 (2), (4), A7-1 (b)–(e),
  A7-2 (d).

**Re-estimate (2026-10-19, evening).** Landed today ≈ 14,000 net Lean lines (G for everything the spine cites, ≈ 6,000; R8 parts 1–2; `ΦE`/A4-1g; the LFStep and LFBdry sub-spines; signs and `thr`; window pieces). A4-1b grew from 3,150 to ≈ 8,850 (W1144: the chain proves its coefficients exist, so the route returns them as a formula); rulings R10 and R11 add ≈ 900 of repairs. Net remaining: **≈ 47,000 lines (range 40,000–75,000)**, of which the new mathematics is unchanged at ≈ 10,000.

**Overall estimate.** The tree: ≈ 38,500 lines; cross-cutting: G 6,000, `Φ`/`ΦE` 1,400, witnesses 1,200, R9 repairs ≈ 500: ≈ 9,100. Total
**≈ 48,000 lines (range 40,000–75,000**; the sub-spines of `ClassStepInput` came to about twice SPINE.md's first ~10,000), Root-C's `C1Star` (≈ 3,000 (?)) not
included. **New mathematics** (the H rows, ≈ 10,000 lines): A3-1 (a) the first step's small field and (b) the first components' gain (B1, B2);
A4-1h (g2) old terms across a new hole (B3) and (g5) the transverse source radius (B2 leaf 5); A4-2ab (b) the small factor (3.10″) (B4); A6-3 (d)
exact two-torus agreement at the last scale (B7); A6-4 (c) the couplings across a large set (L4, B5); A7-1 (a) and A7-2 (a)–(c), the case with no
step (B1). **Engineering:** ≈ 38,000 lines, led by G, R8, `Φ`, LFStepInput's (g1), (g3), (h) and RKeptGasInput's kept and gas outputs. At ≈ 600 landed
lines per task, 3 per wave: ≈ 27 waves of capacity; with dependency stalls and false starts on the H items, **≈ 30 waves (25–40)**. The dependency chain
alone (R8 → (A1)–(A5) → `Φ` → A4-1b–f → (g1), (g3), (h) → A4 → A4f-1 → A1′ → provider, G alongside) is ≈ 15 waves, so the slot cap, not the
order, sets the length.

(W1144) A4-1b (iii) is revised from 1,300 to ≈ 7,000 (route R-LOC: the formula forwarded through the chain, the replacement of each object, Lemma 4.2 at the local sets) and A4-1f from 800 to ≈ 700 (after R-LOC L2): the total rises by ≈ 5,600, to ≈ 53,600.
