# SPINE — Root-F from a finite list of source-level inputs (W1094, 2026-10-18)

**PROVED.** `Balaban.RootFSpine.rootF_of_spine` (`Balaban/Spine/RootF.lean`) has as conclusion the body of the frozen
`Balaban.logPartition_multiscale`, copied verbatim. Its hypotheses are the seven `def … : Prop` of `Balaban/Spine/RootFInputs.lean`,
taken at constants that the provider chooses as functions of `(κ, c₉)`: `δ`, `Ty` (typing constants), `P6` (Def-6), `C7`,
`PB` (budget), `cs₀` (non-running operator constants), `M1, c` (geometry), `rH, ϱ`. There is no `sorry`, and the axioms are
`propext, Classical.choice, Quot.sound`. In a scratch file, `type_of% (logPartition_multiscale d N hd hN)` is accepted for its
conclusion. The match is definitional: the elaborated `NormedSpace ℂ` instance path differs, as it already does for the landed
copy `Correlations.RootFStatement`. The provider closes Root-F by
`exact rootF_of_spine d N hd hN δ hδ Ty P6 C7 PB cs₀ M1 c rH ϱ hA1 hA3 hA4 hA4t hA4f hA6 hA7`. Root-C is `rootC_of_spine`
(`Spine/RootC.lean`, see the last section).

**Proved inside (these are not inputs):**
* the order of the constants (A1): `δ`; `L = Ty.L` and `M = Ty.M`; one `β₀`, the maximum of the thresholds of the inputs and 2;
  `kf = k̂_f`, the least `k` with `ν L^{2k+2} ≥ 1` (`IsHorizon`, `exists_isHorizon`, `IsHorizon.scale`); and `k₀ ≤ k̂_f`
  (`kZero_le_of_isHorizon`);
* A5, the flow induction (LFR Theorem IV.3.2 (b), (c)): `class_flow` for `ℛ_k`, `k < k₀`; the transfer; `frozen_flow` for `ℛ♭_k`;
  the normalization `∫ρ_k = c Z(g)` (`IntegralIsZ.step`); and the stop by the horizon. The stop (`stop_of_flatClassAt`) follows
  from (H.6) of the class (`CoeffBounds.flow`), from `ν_0 = ν`, and from `c₈ q/(1-q) ≤ 1/20` (the former tie input, now proved);
* A8 and the conversion (F3): the exponential identity of `Z(g)/Z(0)` (`ratio_eq_exp`), the principal logarithm
  (`log_partition_eq_multiscale_of_exp`), and the terms `T_j(x,X;g)_i = ∫₀¹ ∂_{g_i(x)} p_j(X;tg) dt` (`activityTerm`). The bound
  (`norm_kf0Deriv_le_two`), analyticity, locality and agreement are in `rootFClauses_of_activities` (`Spine/Activities.lean`,
  the multi-scale form of `kf0Term`);
* A12: the transport from the family torus `M n_K L^K` to Root-F's `ℓ` (`sideOf_eq`), and the two regimes `ν ≤ 7/8 L⁻²` (the
  flow) and `ν > 7/8 L⁻²` (A7).

**A0 is not used.** The classes carry a general unit field `hv` and the source ball `l1Ball` of radius 1 (`D1Form2`), so the
inputs are stated at every unit `h`. Route A (`e₀` at radius `√N`, UNITH) does not fit `D1Form2`. Rotation covariance of the
class (W1083) is a sub-input of A3–A6 if they are proved at `e₀` first.

## Carriers

`RepClassAt … k ρ ν_k`: `ρ ∈ ℛ_k` is `IsRep2` (LFR Def. II.6.2 v2; it contains `IsSFFamily2` as (D2)). It is taken at the a priori
setting `𝒮[d, T, β, a]`, whose `λ̂_j = log(βa) + 1 + jθ` is what `Coh.lam_eq` forces. The other parameters are
`k₀ = kZero d L β ν`, the horizon `K = k̂_f + 1`, `M = Ty.M`, and the outer constants `P6, C7`. The constants `cs, P, geo` are
existential, but their outer fields (`aKer, Cpsi, Cb, aw`; `c1, c2, H0`; `M1, c`) are fixed. The running constants are those of
`F.sf`, through `Coh`. Two clauses are added: `ν_0 = ν`, and `ν_k` is exposed. `FlatClassAt` is the same with `IsRepFlat2`
(`ℛ♭_k`, horizon `k̂ = k̂_f`). `IntegralIsZ` is `∫ρ_k dψ_k = c Z(g)`, with `c > 0` per torus, on the unit ball. `IntegralStep` is
`∫ρ' = c ∫ρ`. The integrals are Lebesgue integrals over the `k`-block fields (`MeasureSpace.pi`). `ObservableActivities … J kf p`
says, on every admissible torus: `p_j(X;g) = 0` unless `1 ≤ j ≤ J` and `IsPolymer d ℓ (M L^j) X`; `p_j` is analytic on the unit
`ℓ¹` ball; it is local in `g|_X`; `‖p_j‖ ≤ (c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(ML^j)^d}`; and the two-torus agreement holds on the
quarter box.

## The inputs

Each item below gives: the statement; the source; the landed theorems; the open sub-inputs; where the landed theorems live
(`3,3,2` = only `d = L = 3`, `N = 2`); and a size estimate in lines (rough, mine).

1. **`PrefixInput` (A1).** For every `κ, c₉ > 0`: `2 ≤ L`, `1 ≤ M`, and `20 c₈ q ≤ 1 - q` with `q = L^{-2γ}`. Source: LFR §I.1.4
   rows 3 and 6, and (I.2) (Thm IV.3.2 (d)). Landed: `exists_rootParams_consts_all` (every `d ≥ 3`, `L = 7`, admissible `Consts`;
   its witness has `c₈ = 1`, which is too large at `L = 7`, `γ ≤ 1/4`, but `c₈` is free). Open: the provider must define `Ty, P6, C7,
   PB, cs₀, M1, c, rH, ϱ` as the full prefix (rows 0–15, `λ_*` with (Λ0)–(Λ32)). The truth of every other input depends on this
   choice; PrefixInput records only what the spine uses. The landed chain uses `L = 3` and A1 uses `L = 7`, and nothing reconciles
   them yet. ~800 (the prefix as definitions plus its inequalities).
2. **`BaseStepInput` (A3, LF-6).** For `β ≥ β₀`, `0 < ν ≤ 7/8 L⁻²` and `kf = k̂_f`, `ρ₁ = S⁽⁰⁾T⁽⁰⁾ρ₀` has a representation in
   `ℛ₁` (`k₀ ≥ 1`) or in `ℛ♭₁` (`k₀ = 0`), with `ν_0 = ν` and `∫ρ₁ = c Z(g)`. Source: LFR Thm II.7.10 (a), (b); P4 (2.42)–(2.54),
   pp. 691–694; P5 p. 487. Landed (`LargeField/Base/`, general `d, L`):
   * `baseFirst_partition_integral`, `baseFirstCut_integral_of_posDef`, `baseFirstRecord_localRestriction_weighted_count`;
   * `baseCovX_bound`, `baseSectorDatum_inDomainR_c7`, `baseActivity_LabelAct(_parametrix)`;
   * `partitionFunction_eq_sum_kf0Sector`.

   Open: the carrier `BaseSmallFieldInput` (ruling R7: `Kphys` and its audit; `baseStepData_nonempty` is not OUT-1);
   BASEPLAN OUT-1 (a)–(d); blocker 1 (`P₁ ≠ ∅`) and blocker 2 (R1, R2); the output in `IsRep2` form (no theorem produces
   `IsRep2 … 1` or an integral identity). ~5000.
3. **`ClassStepInput` (A4, LF-3 + LF-4).** For `1 ≤ k < k₀`, every `ρ ∈ ℛ_k` has `ρ' = R S T ρ ∈ ℛ_{k+1}` with `∫ρ' = c∫ρ`.
   Source: LFR Thm IV.1.1 (P5 Thm 1, P6 Thm 1, P5 p. 499), then Thm III.10.8 (P7 Thm 2, (1.3)–(1.7), pp. 497–529). LF-3 and LF-4 are
   one input: LF-4's hypothesis "rep produced by LF-3" has no Lean statement. For the same reason the small-field part (P4 Thm 1
   for `IsSFFamily2`, GENCLASS T3) is not split off: no landed operator relates the two small-field data.

   Landed, small-field part (`3,3,2`, over `StepClass`/`SFTermClauses`, not `IsSFFamily2`):
   `e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot`, `e0CoeffFamily_class_fromTower_of_irrelBounds_X`,
   `classOldDec_expansion_cover_birth_run`, `newLabels_castInputs_of_localFamily`, `irrelTorus`, `norm_filed_le_power`.

   Landed, large-field part (general `Setting`):
   * `lf4R_removed` (named inputs `hrip`, `hCR0`, `hwin`, `hτ`), `hrip_of_counter`, `hcount_of_flow`;
   * `gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel`, `removedKernel_kerBound_of_hid_action`;
   * `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` (about 60 numeric side conditions), `keptKernel_one/two/three_kerBound`.

   Open sub-inputs:
   * the chain's premises: the composed step data lies in the term domain and `Ψ·Ψ ∈ slitPlane` (the hchart type); the per-label
     irrelevant bounds `Bτ` (P1 (3.128), the hEbd type); the old densities are analytic along the path;
   * R8 (local generating sets, blocker 6) and the counterterms;
   * blockers 2, 3 and 4: R4 (gas representation, ℬ′), the kept bounds (ϰ₄, ϰ₅ need `hquot`), and the vacuum bound;
   * a bridge chain ⇒ `IsSFFamily2` at `k+1`, and the step theorem itself;
   * moving the chain from `StepTower` to `StepTowerG`.

   ~10000.
4. **`TransferInput` (A4, Lemma IV.2.1).** If `k₀ ≥ 1`, `ℛ_{k₀} ⊂ ℛ♭_{k₀}`, with the same `ρ` and `ν_{k₀}`. Source: LFR Lemma IV.2.1;
   P5 p. 490; LF-2 (iv). Landed: `IsRep2.toFlat`, with `D2SF2.toFlat2`, `D9Coeff.toFlat` and `Rep.budgetFlat_of_LF2`.
   **Mismatch:** `IsRep2.toFlat` needs the horizon `K ≤ k₀ + 1` (the pin `D4Pin (k+1)` of LF-2's counter history), while the
   spine's family has `K = k̂_f + 1`. Open: (H6′)⇒(H6♭) for `K > k₀ + 1`, plus `S.Good`, `BudgetSetup`, and (H-λ) (`hH1`, `hH2`, LFR
   Lemma IV.3.3 (c)) from the prefix. ~400.
5. **`FrozenStepInput` (A4, LF-5).** For `max(k₀,1) ≤ k < k̂_f` and `ρ ∈ ℛ♭_k` with `ν_k ≤ 7/8 L⁻²`, `ρ' = S T ρ ∈ ℛ♭_{k+1}` with
   `∫ρ' = c∫ρ`. Source: LFR Thm IV.2.2 (P5/P6 Thm 4 repaired, P6 p. 21); the switch at `k₀` (FLUCTUATION Lemma 2.9, D-IV.5).
   Landed: the small-field pieces as in item 3, and `Rep.budgetFlat_of_LF2`. Open: the step theorem; blocker 2 (the switch); the
   vacuum region R5′ (W1092); blocker 6. ~3000 beyond item 3.
6. **`LastIntegralInput` (A6, LF-8 (a) in observable form).** For `1 ≤ k ≤ k̂_f` and `ρ ∈ ℛ♭_k` with `ν_k > 7/8 L⁻²`,
   `∫ρ = exp(E + ⟨g,h⟩ + Σ_{j≤k+1} Σ_X p_j(X;g))` on every torus of the family, with `ObservableActivities … (k+1)`. Here `p_j` is
   `Σ_{x∈X}⟨g(x), ℳ^{(j)}(x,X;h,h,g)⟩` for `j ≤ k`. For `j = k+1` it collects `ℳ_0^{(k+1)}`, `ℛ_n` and `𝒫`, regrouped by `Ȳ`.
   Source: LFR Thm IV.4.1 (P7 (4.9)–(4.17), pp. 529–533; P9 (4.4)–(4.7), p. 516); Def. IV.5.2; Thm IV.5.3 items 2, 3, 5 and 7.
   This input includes A9, A10 and A11 for the activities. Separate inputs are impossible: the activities are produced by the last
   integral and have no landed definition. Landed (`Green/`, general `3 ≤ d'`, `3 ≤ L`, `N`):
   * `cutoffInteraction_final_class_polydisc_local`, `norm_coef_cutoff_class_le_levels_of_large`, `final_tail_gas_bound`, and the
     `FinalLarge*` linked Mayer expansion;
   * A9: `rootRate_of_sizeJ`, `rootBound_of_perTerm`, `betaK_inv_sq_le`, `mObs_rootF_of_obsBound`;
   * A10: `sitesOf_isPolymer`, `rootF_sites_of_cellClause`, `obsCubeFamily_sourceBall_fromTowerG_rho`;
   * A11: `towerGapScale_resum_fromTowerG`, `resum_lastScale_rootF_weighted_of_block_large`, `finalCoef_close_quarterBox_weighted`,
     `fibre_hcoef_of_quarterBox_weighted`, `e0CoeffFamily_value_fromTowerG_core_twoTorus`, `coreE0_unique`;
   * A8 at one gap scale: `towerGapScale_rootFClause`.

   Open:
   * blocker 5: the identification of `F` with the class energy terms (FINALPHYS3 §8); the real gap L4; the linked gas of P7 (4.11);
     the joins; the activity `det-ratio × J`;
   * the reindexing from cells to fine sites (ROOTFFAM target 4); the rate and amplitude conversion with the regrouping entropy
     (Thm IV.5.3 item 5);
   * blocker 7: the gap scales `j ≤ k_f` for the class (item 24); the inherited terms across steps (W1090); `hFclose`; TORUSCOH2.

   The landed `Green/` and `TwoTorus*` theorems are not stated over `IsRepFlat2`. ~6000.
7. **`KfZeroInput` (A7, LF-8 (b)).** For `7/8 L⁻² < ν ≤ 1` and `kf = k̂_f ∈ {0,1}`, on every admissible torus
   `Z(g) = exp(E_ℓ + ⟨g,h⟩ + Σ_X p_1(X;g))`, with `ObservableActivities … 1`. Source: LFR Prop. IV.4.3, superseded by LF-BASE-KF0.md;
   no paper treats this case. Landed: the one-scale input of `rootF_kf0_partial_of_oneScaleInput` has the same shape (amplitude
   `4√N B`, `δ = 1/8`); also `KF0AllGoodGas.lean`, `KF0AllPlusGas.lean`, `Green/KF0CovarianceAtoms`. Open: the reversed-spin sector
   (blocker 1) and `CompleteHeavyLocality`. ~2500.

**Non-vacuity.** Items 3–6 are `∀ ρ ∈ class`. They are non-vacuous once the class at the provider's constants is inhabited.
Item 2 forces that: it asserts a member of `ℛ₁`/`ℛ♭₁` whose integral is `c Z(g) ≠ 0`. Items 3–5 then produce members at every
later scale, and the stop lemma produces the massive member that item 6 needs. The existence statements (2, 7) cannot hold
vacuously, because they contain the physical `Z(g)`. A direct check: exhibit members at the prefix constants. The landed witnesses
`wIsRep2` and `wIsRepFlat2` (`Def7v2Inhabited*`, `d = L = 3`, `N = 2`, `K = k = 1`, zero terms) inhabit `IsRep2`/`IsRepFlat2` but
not yet `RepClassAt`/`FlatClassAt` (constants and `ν_0 = ν` to be matched; ~150). Rule 10: the seven inputs are named obligations,
and their `Nonempty` is the open work itself, so an exemption must be recorded in the ledger.

**Plausibility.** The inputs follow LFR's proof of Thm IV.5.3, read with the carriers above. They are true for the LFR prefix only if
the landed definitions mean their sources. Defects found in the carriers (e.g. CRotE, now being repaired by W1091) would carry into
items 2–6. Nothing in the spine required changing a landed definition.

## Root-C

`rootC_of_rootFAndC1Star` needs `RootFAndC1Star d N hN`. Beyond Root-F, that adds:
1. `3 ≤ L` at `(κ_*, 1)`, where `κ_* = kappaStar d` (LFR row 3);
2. `Nonempty (C1Star d N L M hN)` for the same `L, M`.

`C1Star` contains:
* the constants `a` (free flow), `γ₀`, `c_*`, `c_ξ`, `c'`, `ρ₀`, `ρ₁`, `β_*`;
* per `β`: `J(ν) = k_f + 1`; `(F1)` (running coefficients `ξ`, with bounds and continuity at `ν = 0`, LF-7 (d), (e)); `(F2)` (the
  one-point function `blockM = magJ + em`); `(F3)` (the two-point decomposition, its bounds and the limits along tori and in `ν`).
  Sources: LFR Thm IV.5.4, Prop. IV.4.4, OBS Thms 3.1, 5.2.

`rootFAndC1Star_of_spine` and `rootC_of_spine` (`Spine/RootC.lean`) prove `RootFAndC1Star` and `RootCStatement` from the spine
inputs together with these two hypotheses.
