# BASE-RG1: the renormalization at scale 1 (what of A4-1c applies at k = 0)

Reading note (C3, Q19). Everything below was read in the tree at origin/main (b8a6a5ae); "not found" means a grep
of `Balaban/` found nothing. Sources: P4 (4.1), (4.14)-(4.22), (5.28); `SMALLFIELD.md` §3.1-3.7.

## 0. A correction to the Q18 note

`expo2_one_eq_firstAction` is an identity for whatever constants are plugged into `β 1`, `a 1`, `Rg.ν 1`. With the
class's own (renormalized) constants it compares the class term with the physical action at the renormalized
parameters, at the datum `ψ₁`. The remaining difference to `β A₁(e_{z₁ψ₁}; z₁ψ₁)` is NOT inexpressible: it is
Lemma 3.5 (i), landed as `Fluctuation/RenormIdentity.lean`: `lemma35_i_complete` (any `G` with `IsLevel G n`, EL pairs
`(φ,α)` at `(ν,D)` and `(φu,αu)` at `(νu,Du)`, `Du = ((1+ζ)Ψ, h)`, `ν(1+ξ₂) = νu(1+ξ₃)`):
`β(1+ξ₃) actionC(νu,Du,φu) = β actionC(ν,D,φ) + β (renormC1 … D φ − renormC2 … αu φ φu)`, and `lemma35_i_complete_bg`
(`φ = bgFieldC` at `(ν,D)`, `φu = bgFieldC`, `αu = bgMultC` at `(νu,Du)`; needs `InUnionDomainC` of both data). `C₁`
is explicit at the old background (`blockPair`, `bondPair`, `massPair` terms, linear in `ξ₃, ζ, ν ξ₂`);
`C₂ = ½(1+ξ₃) ⟨δφ, H_u δφ⟩` with `δφ = φu − φ`, quadratic in the perturbation. The `ν`-free form is
`lemma35_i_nuFree(_bg)` (with `renormC3`). My `baseFirst_block_scale` is the fixed-spin part of `C₁`.

## 1. How the general step defines the new constants and the counterterms

Unknown `ξ = (ξ₁,ξ₂,ξ₃) ∈ ℂ³` (sup norm), `ξ₁ = ζ/ε_{k+1}`, `ξ₂ = e/β`, `ξ₃ = b/β` (`Flow/RGEquations.lean`).
* Constants: `Flow.betaSeq` (`β_{k+1} = β_k L^{d−2}/(1+ξ₃)`), `Flow.nuSeq` (`ν_{k+1} = ν_k L²(1+ξ₃)/(1+ξ₂)`),
  `a_{k+1}` by the free flow (`compWeight`, `aIdeal`; `SMALLFIELD.md` §3.1), `z_{k+1} = 1 + ζ(ξ)`,
  `renZeta ε ξ = ε ξ₀` (`Fluctuation/RenormThetaDatum.lean`, `renThetaDatum ε D ξ = ((1+ζ)Ψ, h)`).
  `E_{k+1}` is the additive constant of the first condition (A4-1g, `Spine/SFVacuum.lean`, not part of `ξ`).
* (H.6) is `Def6.CoeffBounds d L k P β ν a`: `∃ ξ β₀ ν₀`, `‖ξ n‖ ≤ (c₈/4) rate^{n+1}`, `β n = betaSeq …`, `ν n = nuSeq …`
  for `n ≤ k`, and `B L^{k(d−2)} < β k`, `0 < ν k ≤ ν̄`, the window of `a k`. Products/limits: `Flow/RunningCoefficients.lean`
  (`betaSeq_eq`, `nuSeq_eq`, `norm_gammaSeq_le`, `exists_gamma_infty`).
* Counterterms: `renC1On`, `renC2On` (`Fluctuation/RenormExpG.lean` imports), `renMassU`, `renormC1/2/3` (above); the
  perturbation `δφ` is the solution map `F` of `IsRenSol` (`RenormStrictData`, `RenormPertClass`, `RenormEndpoint`:
  `renDec_one_unique`). New energy density at the renormalized datum: `D_E = ℰ''₀(θ_ξ) + oldE + C₁ + C₂ − vac`
  (`SPINE-PLAN.md` A4-1c), with `ℰ''₀(θ_ξ)` = `renE0θ_det` + the marked terms (`RenormThetaDatum`; determinant part only).
* The system: `A(ξ,p) ξ + c̃(ξ,p) = f̃(ξ,p)`, `A = Flow.matrixInfty a v τ c₁ c₂ ε` (complete backgrounds,
  `triangularBounds_matrixInfty` = Lemma 3.1), `Flow.matrixSel` selects the `ν`-free matrix for `k < k₀`
  (`matrixSel_of_lt/_of_ge`). Solution: `Flow.rg_step_infty` (existence, uniqueness in the polydisc of radius
  `rgRadius (42κ) c₁₀`, analyticity, bound `rgCxi B α₀ (β⁻¹ q^{k+1})`, reality when the data are conjugation symmetric);
  `Flow.exists_rg_solution_triangular_param`, `rg_solution_real` (`RGParam`); numerical closing:
  `physical_step_contraction_condition`, `physical_rg_step_of_large_beta` (`PhysicalStepThreshold`);
  chart: `TriangularChart`. Hypotheses (B1) of `SMALLFIELD.md` §3.2: `c, f` analytic and bounded on the polydisc, from the
  localized expansions `thm31g_C1/C2/Eu_of_input`, `thm31h_of_input` (`RenormExpG`), the `…_on` forms with a sub-domain
  `Dom` (`RenormExpInputOn`).
* (H.5) is `Def6.RenormCondAlong m₀ k νk Tm j idx hidx` with fields `val` (constant, `E_{k+1}`), `dpsi` (derivative in the
  field scale, equation (E1), fixes `ζ`), `dh` (derivative in `h`, (E2), fixes `e`), `moment` (limit of `momentSum` along
  tori, (E3), fixes `b`). `Spine/SFStep.lean`: `SFRenormQ = CoeffBounds (k+1) ∧ RenormCondAlong … (k+1)`;
  `SFRenormInput` is the open A4-1c. **Not found:** any theorem deriving `RenormCondAlong` at `k+1` from a solution `ξ⁰`
  of the system (the only users of `RenormCond*` are the inherited levels, `Fluctuation/OldTermsLift*Renorm*`, and
  inhabitation files). That bridge (~1,500 in `SPINE-PLAN.md`) is the open part. Its inputs exist in pieces: the
  equations (E1)-(E3) are the stationarity of `D_E` in `ξ`; Lemma 3.5 supplies `C₁, C₂`.

## 2. Generic in the level, and what is k ≥ 1 only

Generic (stated for any `G : GeneratingSet d L N₀ k ϱ` or any `k`; apply at `k = 0` with the first step's local terms):
`Flow/*` (all); `CoeffBounds`, `RenormCondAlong`, `SFRenormQ`; `RenormIdentity` (`IsLevel G n`); `RenormThetaDatum`;
`RenormStrictData`, `RenormPertClass`, `RenormEndpoint` (data-side, any `G`); `RenormExpG` / `RenormExpInputOn`
(`RenormExpInput` has fields `locC1, locC2, expE0, expOld, locDφ, expM0, expOldM`); `RenormInputZero`
(`renormExpInput_zero_of_fields`, `thm31g_*_zero_of_fields_on`, `thm31h_zero_of_fields_on`: the class whose old terms
vanish, which is exactly `k = 0`: `Spine/BaseSF.lean` `bareSF` has `ℰ = ℳ = 0`, fact `BaseSFBareInput`);
`RenormLocC1Zero` (`renLocC1_zero_at`, abstract `FlCore`, `HatConn`, `IsLevel Gp (k+1)`; `RenormSharedClass`
`renLocC1_zero_of_le`, `renCK`).
Consequence at `k = 0`: `expOld`, `expOldM`, `oldE`, `oldM` are zero (`isLocExp_zero_cover`); the inherited-level
conditions (`OldTermsLiftRenorm*`) are vacuous (no levels `1..0`).

k ≥ 1 only (hypothesis `hk : 1 ≤ k`, or built on the tower): `StepTowerG.flCore_scale_mono`
(`Inhabited/StepTowerCoreMono.lean`: `FlCore` of the pair `(lvTopG, lvLowG)` from the tower core with `hk`),
`renLocC1_scale_of_towerG_of_le_at`, `renLocC2_/renLocDphi_scale_of_tower_at`, `renLoc_fields_scale_of_tower_at`
(also fixes `d=3, L=3, N=2`, `3 ∣ N₁`), `exists_isRenSol_scale_of_towerG_at` (`Inhabited/RenormRadiusLoc.lean`).
The reason is the two-level pair: at `k ≥ 1` the lower level `lvLow` is nonempty and `FlCore` is the decoupling of that
pair. At `k = 0` the decoupled background is the cover of `Base/BaseBackgroundIdent*.lean`
(`decBg_one_eq_bgField_of_inDomainR`, `Dec2.coverBase_self`, `BaseBackgroundIdent2`), so the three localization
principles for the first step need `FlCore`-type input for the base cover; I did not verify that `renLocC1_zero_at`
accepts it as stated (its `FlCore` is stated with `Gp`, `Hm` of the same level `k+1`). The old-term system
(`GeneralRenormInput`: `IsLocExp.sub_at_zero`, `exists_oldDiff_locExp_of_coeffFamily`, `renormExpInputOn_class_of_fields`) is
k ≥ 1 content, vacuous at `k = 0`. `StepSetting`/`XSetting` carry the fluctuation integral of the general step; the
first step uses the chart route of `Base/` instead, so none of their consumers is used.

## 3. Regime (B), k = 0: statements needed for `SFRenormQ` (CoeffBounds at 1, RenormCondAlong at 1)

Regime (B) (`β ν L^d > 1`, `k₀ = 0`): complete backgrounds from the start, `Pc = massOne P6`, matrix `matrixInfty`
(`matrixSel_of_ge`), the guard `0 < nuIdeal` in `dh` is satisfied. Sizes are Lean-line estimates.
1. **Lemma 3.5 at the base** (~250): `IsLevel (single 1) 1`, `InUnionDomainC` of `D(ψ)` and `D(θ_ξ)`, then
   `lemma35_i_complete_bg` and `expo2_one_eq_firstAction`. Gives `β_u A_u(θ,φ_u) = β A(ψ,φ) + β(C₁ − C₂)` in class form.
2. **Perturbation `δφ` at the base** (~600): `IsRenSol` and `RenormPertClass` for `single` at `k = 0`, `lemma35_ii_bound`
   (`‖δφ‖ ≤ K₂ B |ξ|`), via `RenormStrictData`, `RenormEndpoint` (generic) plus `BaseBackgroundIdent2` for the base cover.
3. **`locC1, locC2, locDφ` for the base cover** (~900 each family if `FlCore` for the base pair is not available;
   ~200 if it is): the principles `HasLocPrinciple … renC1On / renC2On / F` on `XiCOneReal`, from the local background
   substitution of `BASE-ORCHC.md` §4c and the 𝔹₁(X̂) sets (blocker 6).
4. **`expE0`** (~1,500): `ℰ''₀(z)(θ_ξ)` as `IsLocExp` on the polydisc `r₀` from the first step's local terms: cluster
   `Pst`, determinant (`BaseDet*`, `BaseDefectLogDet`), defect walks (`BaseDefectWalks`, `BaseHull`), plus the chart
   inclusion for `ξ ≠ 0` (`RenormThetaDatum` states it is not proved; the scaled datum must stay in `XiCData`).
5. **`expM0`** (~600): the source term `β^{-1/2} ℳ''₀(x)(θ_ξ)`, same pattern as 4 for the observable `ℳ`.
6. **Assemble `RenormExpInput` with the zero class** (~150): `renormExpInput_zero_of_fields` with items 3-5, then
   `thm31g_C1/C2/Eu` and `thm31h` give (B1): analytic and bounded `c, f`.
7. **The system at `k = 0`** (~400): bounds (5.24), (5.25) by Cauchy from item 6 (`hcb`, `hfb` of `rg_step_infty`), the
   bound `η ≤ B(2/α₀²) β⁻¹ q` ((5.29), trivial at `k = 0` since `γ₀ = 1`), `hcond` by `physical_step_contraction_condition`
   for `β ≥ β*`, `TriangularBounds` of `matrixInfty` at `(a₁,u, ν L², …)` (`triangularBounds_matrixInfty`, range check
   `InftyRange` for `a ∈ (1,3/2)`, `ν L² ≤ 7/32`), `TriangularChart` for the open chart, reality (`rg_solution_real`, data
   real by `h` real and `ψ` real). Output `ξ⁰` with `‖ξ⁰‖ ≤ rgCxi B α₀ β⁻¹ q`.
8. **`CoeffBounds` at 1** (~200): set `ξ 0 := ξ⁰`, `ξ n := 0` for `n ≥ 1`; `β 0 = β`, `ν 0 = ν` (`BaseSFBareInput`),
   `betaSeq`/`nuSeq` at `n = 0, 1` unfold to the stated formulas; `β 1 > B L^{d−2}` from `β ≥ β*`, `ν 1 > 0`, `ν 1 ≤ ν̄`,
   `a 1` window from the free flow. The `c₈` rate condition `c₈ rate ≤ 1 − rate` is a constant check.
9. **`RenormCondAlong` at 1** (~1,500, the open A4-1c bridge): `val`: define `E₁` (constant) so `ElocInf` of the unit
   constant field vanishes; `dpsi`, `dh`: (E1), (E2) are `∂ D_E = 0` at `ξ⁰`, in the `ElocInf` form with `constInf`;
   `moment`: (E3) as a limit of `momentSum` along tori `idx n → ∞`, which needs the torus independence of the new level
   (`TorusIndep`, `BaseTwoTorus*`, A4-1f) and the two-torus agreement of the first step's terms; at `k = 0` the inherited
   part of `ElocInf` is zero, so only the new level enters.
10. **The `ν`-free system is not needed** in regime (B); in regime (A) (`k₀ ≥ 1`) the matrix is `matrixSel_of_lt` and the
   `ν`-free Lemma 3.5 (`lemma35_i_nuFree_bg`, `renormC3`) is used (blocker 2, not treated here).

Order of work: 1, 2, 7, 8 do not depend on the local terms and can be written now; 3-6 depend on blocker 6 and the
cluster/determinant output; 9 is the single large bridge and is shared with the general step (it should be proved once
for a generic `Terms` and instantiated at `k = 0`).
