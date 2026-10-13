/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.PhysicalTerms
public import Balaban.Fluctuation.SharpVF
public import Balaban.Fluctuation.SharpENu
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp assembly of the physical expansion (package 5 of `SHARPLOC.md`)

The landed assembler `interaction_expansion_hat_dm` obtains, for each of its five summands (the
potential part, the old terms, the source sites, the observable terms and the mass variation), a
localized expansion whose locality relation is the thickened agreement `AgHatF` of the hat
variable, and combines them with `LocIntDm.assemble` and `LocIntDm.addLift`.  Those combinators
are generic in the agreement relation of the hat variable, so the same proof, run with the sharp
summands (`vpart_locInt_hat_dir_dm`, `eterms_locInt_hat_dm_dir`, `fsite_base_locInt_hat_dir_dm`,
`mterms_locInt_hat_dm_dir`, `nupart_locInt_bound_hat_dm_dir`), produces the same expansion with the
sharp agreement `AgHatFDir` (equality of the hat variables at the unit points of the sites of the
label `Y` itself).  The summands are local in the raw datum for agreement on `Y` itself (they come
from the `…_rawY` expansions), and the combinators are generic in that relation too: the assembled
terms read the raw datum and the source only on `Y`.

* `interaction_expansion_hat_dm_core_dir`: the assembled expansion with the sharp relation (the
  statement of `interaction_expansion_hat_dm` with `AgHatF` replaced by `AgHatFDir`).
* `interaction_expansion_hat_dm_dir`: one pair `(𝒴, T)` that is a `PhysExpansion` (the thick
  legacy locality: raw datum on `thickSet Y`, hat variables on the block thickening; obtained from
  the sharp one because the thick relations imply the sharp ones) and satisfies `PhysicalSharpLoc`
  (raw datum and source on `Y`, hat variables at the unit points of `Y`).
* `physical_directTerms`: a `DirectTerms` instance for the physical expansion, unconditionally;
  its relation `physAgΘ` is agreement of the raw datum and the source on `Y` itself.
* `stepActivityBound_zeroClass_direct`: the step activity bound of the zero class with the rate
  `κ_H = 2 κ_dec - 1` and prefactor `R_σ ε_U`, without the halo conversion of the rate.
* `stepActivityBound_zeroClass_direct_rate`: the arithmetic at `d = L = 3`.

What is proved: for the zero class, one fluctuation step preserves the decay rate of the label
activity (the output rate `2 κ_dec - 1` of the activity is the rate of the terms of the expansion
itself, not the rate divided by the halo constant), under the listed hypotheses.  What is not
proved: the general class (old terms and observable terms enter `T1`, `T2` but the activity
bounds are those of the zero class only), the output terms of the class, and the smallness
`(DA)` for the physical prefactor in the regime of the papers (`SHARPLOC.md` §2).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section SharpAssemble

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- The potential part with the resummed bound, for the sharp agreement `AgHatFDir` of the hat
variables and raw data agreeing on `Y` itself. -/
theorem hat_vpart_bound_dm_dir {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) T
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (interactionOne hG hG' le_rfl a₁ ν eps)) taylorWeight x₀ w σ Θ)
        (fun Y => (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the potential part, with its labels
  obtain ⟨TV, hLV0⟩ := vpart_locInt_hat_dir_dm (m₀ := fun _ => m₀) (j := jV) (X := XV) (𝒦X := 𝒦XV)
    (X₁f := X₁V) hC hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum'
    hreal hcovV hX₁V hconn hrow hoptV hΔV hκ₀ hκdec hκ h1 hlogV hZV hmarV continuous_taylorWeight
    hR₁ (analyticOnNhd_taylorWeight _) (Mω := 1 / 2) (by norm_num)
    (fun t ht => norm_taylorWeight_le t ht) hr (Rσ := Rσ)
  have hLV := (hLV0.mono_P (P' := IsDj m₀ (k + 1)) fun Y hY => hY.elim fun _ h => h).mono_XW (hatRaysO_subset (N := N) (Gp := Gp) cψ R₁ Rσ r)
  have hbV : ∀ Y ∈ Finset.univ.biUnion
      (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)),
      (∑ z, if Y ∈ polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z) then
        (1 / 2 : ℝ) * (6 * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3) else 0) ≤
      (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by
    intro Y hY
    obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
    have hMD := polyDom_isMultiDom (hcovV z₀) hd (hoptV z₀) hz₀
    have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁V z) m₀ (jV z)
        (𝒦XV z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
      refine card_blocks_filter_le hG' le_rfl (hcovV z₀).hN hMD _ (fun z hz => ?_)
      have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
      rw [← hX₁V z] at h1'
      intro x hx
      exact h1' (hZV z ⟨x, Finset.mem_coe.1 hx, Or.inl rfl⟩)
    have ht0 := treeLenCov_nonneg Gp m₀ Y
    set Eb := ‖energyBd d L N (compWeight L a₁) ν k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ with hEb
    have hv : 0 ≤ (1 / 2 : ℝ) * (6 * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3) := by positivity
    refine (sum_ite_card_le _ hv hcard).trans ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← hEb,
      ← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
    have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
    have hCV : 0 ≤ 3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * Eb / r ^ 3 := by positivity
    calc c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          ((1 / 2 : ℝ) * (6 * (Eb * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r ^ 3))
        = (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * Eb / r ^ 3) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key hCV
  have hLV' := hLV.mono_on hbV
  exact ⟨_, hLV'⟩

/-- **Ray-differentiable form of `hat_eparts_bound_dm_dir`.**  The statement of `hat_eparts_bound_dm_dir` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`. -/
theorem hat_eparts_bound_dm_dir_ray {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ}
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ}
    (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯E.biUnion fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)) T
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
            (fun _ => (1 : ℂ)) x₀ w σ Θ else 0)
        (fun Y => (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => T Y (z • ψ) (z • ψ) 1 Θ) (ball (0 : ℂ) (3 / 2))) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the old terms
  obtain ⟨TE, hLE0, hrayE⟩ := eterms_locInt_hat_dm_dir_ray (m₀ := fun _ => m₀) (j := jE) (X := XE) (𝒦X := 𝒦XE)
    (X₁f := X₁E) 𝒯E hBE hFE hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ hcovE hX₁E hconn hrow hoptE hκ₀
    hκdec hκ h1 hlogE hEbE hEanE hEbdE (ω := fun _ => (1 : ℂ)) continuous_const hR₁
    analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  have hbE : ∀ Y ∈ 𝒯E.biUnion (fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)),
      (∑ τ ∈ 𝒯E, if Y ∈ polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ) then
        1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ)
          (XE τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r) else 0) ≤
      (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by
    intro Y hY
    obtain ⟨τ₀, hτ₀, hz₀⟩ := Finset.mem_biUnion.1 hY
    have hMD := polyDom_isMultiDom (hcovE τ₀ hτ₀) hd (hoptE τ₀ hτ₀) hz₀
    have hnc := ncard_le_of_isMultiDom hG' (hcovE τ₀ hτ₀).hN hMD
    have ht0 := treeLenCov_nonneg Gp m₀ Y
    set w : τι → ℝ := fun τ => EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) with hw
    have hw0 : ∀ τ ∈ 𝒯E, 0 ≤ w τ := fun τ hτ => mul_nonneg (hEbE τ hτ) (Real.exp_pos _).le
    have hs := sum_roots_le 𝒯E w hw0 rE Y hρE
    have hq : 0 ≤ Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r := by positivity
    have e1 : ∀ τ ∈ 𝒯E, (if Y ∈ polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ) then
        1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ)
          (XE τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r) else 0) ≤
        (if rE τ ∈ Y then w τ else 0) * (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
      intro τ hτ
      by_cases hYτ : Y ∈ polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)
      · have hin : rE τ ∈ Y := by
          have h1' := subset_polyDom hYτ
          rw [← hX₁E τ hτ] at h1'
          exact h1' (Finset.mem_coe.2 (hrE τ hτ))
        simp only [hYτ, hin, ite_true, hw, one_mul]
        refine le_of_eq ?_
        rw [sub_eq_add_neg, show -κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) +
          -(2 * κdec * treeLenCov Gp m₀ Y) = -κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) +
          (-2 * κdec * treeLenCov Gp m₀ Y) by ring, Real.exp_add]
        ring
      · simp only [hYτ, ite_false]
        split_ifs
        · exact mul_nonneg (hw0 τ hτ) hq
        · simp
    calc _ ≤ ∑ τ ∈ 𝒯E, (if rE τ ∈ Y then w τ else 0) *
            (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := Finset.sum_le_sum e1
      _ = (∑ τ ∈ 𝒯E, (if rE τ ∈ Y then w τ else 0)) *
            (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by rw [Finset.sum_mul]
      _ ≤ (ρE * (c1 d L * ((L : ℝ) ^ (k + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            (1 + treeLenCov Gp m₀ Y))) *
            (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
          refine mul_le_mul_of_nonneg_right (hs.trans ?_) hq
          exact mul_le_mul_of_nonneg_left hnc hρE0
      _ = (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
            ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
      _ ≤ _ := by
          rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
          exact mul_le_mul_of_nonneg_left (one_add_mul_exp_le _ κdec) (by positivity)
  have hLE' := (hLE0.mono_P (P' := IsDj m₀ (k + 1)) fun Y hY => by
    obtain ⟨_, _, h⟩ := hY; exact h).mono_on hbE
  exact ⟨_, hLE', hrayE⟩

/-- The old terms with the resummed bound (sharp hat version; raw data agreeing on `Y` itself). -/
theorem hat_eparts_bound_dm_dir {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ}
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ}
    (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯E.biUnion fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)) T
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
            (fun _ => (1 : ℂ)) x₀ w σ Θ else 0)
        (fun Y => (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (hat_eparts_bound_dm_dir_ray (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ (m₀ := m₀) (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE rE hrE (ρE := ρE) hρE0 hρE).imp fun _ h => h.1

/-- The source sites with the resummed bound (sharp hat version; raw datum and source agreeing on
`Y` itself: the site of each source weight lies in every domain that carries its term). -/
theorem hat_fparts_bound_dm_dir {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ}
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun s => polymerDomains
          (fun i : ParIdx Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ (jF s) (𝒦XF s))) T
        (fun x w σ p => ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x w σ p.1)
        (fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x) (AgHatFDir hG') := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the sites of the source
  have hexF := fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
    fsite_base_locInt_hat_dir_dm hC hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ (hcovF s) (hX₁F s) hconn hrow
      (hoptF s) (hΔF s) hκ₀ hκdec hκ h1 (hlogF s) s.1 (hyF s) s.2 (ω := fun _ => (1 : ℂ))
      continuous_const hR₁ analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr
      (Rσ := Rσ)
  choose EvF hEvF using hexF
  have hLF := LocIntDm.wsum (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N))
    (𝒴 := fun s => polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s)) (fun s _ => hEvF s)
    (SG := l1Ball d L N₁ m₁ (k + 1) N) (amp := fun s g => g s.1 s.2)
    (fun s _ => (analyticOnNhd_coord s.1 s.2).mono (Set.subset_univ _))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (fun s _ Y hY g _ g' _ hag => by
      have h1' := subset_polyDom hY
      rw [← hX₁F s] at h1'
      exact congrFun (hag s.1 (h1' (Finset.mem_coe.2 (hyF s)))) s.2)
    (B := fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
    (fun Y _ g hg => by
      have ht0 := treeLenCov_nonneg Gp m₀ Y
      rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
      set β := 1 * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r) with hβ
      have hβ0 : 0 ≤ β := by positivity
      have hβle : β ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y) := by
        rw [hβ, one_mul, mul_div_right_comm]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
      have hsum : ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ‖g s.1 s.2‖ ≤ 1 := by
        rw [Fintype.sum_prod_type]; exact le_of_lt hg
      calc ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (if Y ∈ polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s) then
            ‖g s.1 s.2‖ * β else 0) ≤ ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ‖g s.1 s.2‖ * β :=
            Finset.sum_le_sum fun s _ => by
              split_ifs
              · exact le_rfl
              · exact mul_nonneg (norm_nonneg _) hβ0
        _ = (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ‖g s.1 s.2‖) * β := by rw [Finset.sum_mul]
        _ ≤ 1 * β := mul_le_mul_of_nonneg_right hsum hβ0
        _ ≤ _ := by rw [one_mul]; exact hβle)
  exact ⟨_, hLF⟩

/-- The observable terms with the resummed bound (sharp hat version; raw datum and source
agreeing on `Y` itself). -/
theorem hat_mparts_bound_dm_dir {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ}
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)} {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯M.biUnion fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) T
        (fun x w σ p => ∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x w σ p.1 else 0)
        (fun Y => (ρM / r) * Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x) (AgHatFDir hG') := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the observable terms
  have hexM : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯M →
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯M then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBM τ h) (hFM τ h) (EM τ)))
            (fun _ => (1 : ℂ)) x₀ w σ Θ else 0)
        (fun Y => 1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ)
          (XM τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯M
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat_dm_dir (hBM τ hτ) (hFM τ hτ) hk hG hG' cc hcψ hMX hdm hα hsmX
        hδ₁ (hcovM τ hτ) (hX₁M τ hτ) hconn hrow (hoptM τ hτ) hκ₀ hκdec hκ h1 (hlogM τ hτ)
        (hEbM τ hτ) (hEanM τ hτ) (hEbdM τ hτ) (ω := fun _ => (1 : ℂ)) continuous_const hR₁
        analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose EvM hEvM using hexM
  have hLM := LocIntDm.wsum 𝒯M (𝒴 := fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ))
    (fun τ hτ => hEvM τ hτ) (SG := l1Ball d L N₁ m₁ (k + 1) N) (amp := fun τ g => g (ys τ) (is τ))
    (fun τ _ => (analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (fun τ hτ Y hY g _ g' _ hag => by
      have h1' := subset_polyDom hY
      rw [← hX₁M τ hτ] at h1'
      exact congrFun (hag (ys τ) (h1' (Finset.mem_coe.2 (hys τ hτ)))) (is τ))
    (B := fun Y => (ρM / r) * Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
    (fun Y _ g hg => by
      classical
      have ht0 := treeLenCov_nonneg Gp m₀ Y
      rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
      set w : μι → ℝ := fun τ => EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) with hw
      have hw0 : ∀ τ ∈ 𝒯M, 0 ≤ w τ := fun τ hτ => mul_nonneg (hEbM τ hτ) (Real.exp_pos _).le
      have hq : 0 ≤ Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r := by positivity
      have hws := sum_weighted_le 𝒯M w (fun τ => (ys τ, is τ))
        (fun p : CTorus d L N₁ m₁ (k + 1) × Fin N => ‖g p.1 p.2‖) (fun p => norm_nonneg _)
        (by rw [Fintype.sum_prod_type]; exact le_of_lt hg) hρM0 hρM
      calc ∑ τ ∈ 𝒯M, (if Y ∈ polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ) then
            ‖g (ys τ) (is τ)‖ * (1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ)
              (XM τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r)) else 0)
          ≤ ∑ τ ∈ 𝒯M, (‖g (ys τ) (is τ)‖ * w τ) *
              (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
            refine Finset.sum_le_sum fun τ hτ => ?_
            split_ifs
            · refine le_of_eq ?_
              simp only [hw, one_mul]
              rw [sub_eq_add_neg, show -κ₀ * treeLenCovOne m₀ (jM τ) (XM τ) +
                -(2 * κdec * treeLenCov Gp m₀ Y) = -κ₀ * treeLenCovOne m₀ (jM τ) (XM τ) +
                (-2 * κdec * treeLenCov Gp m₀ Y) by ring, Real.exp_add]
              ring
            · exact mul_nonneg (mul_nonneg (norm_nonneg _) (hw0 τ hτ)) hq
        _ = (∑ τ ∈ 𝒯M, ‖g (ys τ) (is τ)‖ * w τ) *
              (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by rw [Finset.sum_mul]
        _ ≤ ρM * (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) :=
            mul_le_mul_of_nonneg_right hws hq
        _ ≤ ρM * (Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y) / r) := by
            refine mul_le_mul_of_nonneg_left ?_ hρM0
            exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hr.le
        _ = _ := by ring)
  have hLM' := hLM.congr_val (val' := fun x w σ p => ∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
      p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
        (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x w σ p.1 else 0)
    (fun xw _ σ _ p _ => Finset.sum_congr rfl fun τ hτ => by simp [hτ])
  exact ⟨_, hLM'⟩

/-- **The four parts in the variable `ψ̂` with the sharp agreement relations, without the mass
variation** (the sharp version of `interaction_expansion_hat_bound_dm`): the terms are local for
raw data and sources agreeing on `Y` itself and hat variables agreeing at the unit points of `Y`. -/
theorem interaction_expansion_hat_bound_dm_dir {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts Gp × Fin N → ℂ => (ψ, ψ))
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0))
        (fun Y => prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  obtain ⟨TV, hV⟩ := hat_vpart_bound_dm_dir hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX hdm
    hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV hX₁V hoptV hΔV hlogV hZV hmarV
    (Rσ := Rσ)
  obtain ⟨TE, hE⟩ := hat_eparts_bound_dm_dir hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE rE hrE hρE0 hρE
    (Rσ := Rσ)
  obtain ⟨TF, hF⟩ := hat_fparts_bound_dm_dir hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ hcovF hX₁F hoptF hΔF hlogF hyF (Rσ := Rσ)
  obtain ⟨TM, hM⟩ := hat_mparts_bound_dm_dir hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hρM0 hρM
    (Rσ := Rσ)
  have hnV : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d *
      ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnF : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnM : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (ρM / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  obtain ⟨𝒴, T, b, hb, hL0'⟩ := LocIntDm.assemble
    (AgΘ := fun Y Θ Θ' => agreeOn Y Θ Θ')
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    hV hE hF hM (-cβ) cβ cβ cβ hnV hnE hnF hnM
  refine ⟨𝒴, T, (hL0'.mono_XW (XW' := {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r})
    (fun xw h => ⟨h.1, h.1, h.2, h.2⟩)).mono fun Y => (hb Y).trans (le_of_eq ?_)⟩
  simp only [norm_neg, prop33Eps]
  ring

/-- **Proposition 3.3 in the variable `ψ̂`, with the sharp agreement relations.**  The statement of
`interaction_expansion_hat_dm` with `AgHatF` replaced by `AgHatFDir` and the raw datum compared on
`Y` instead of `thickSet Y`: the terms are local in the hat variable for equality at the unit
points of the sites of the label `Y` itself, and in the raw datum and the source for equality on
`Y` itself. -/
theorem interaction_expansion_hat_dm_core_dir {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z)) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts Gp × Fin N → ℂ => (ψ, ψ))
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
        (fun Y => prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2) := by
  classical
  have hreal := hreal_level hC hG hG' le_rfl ha₁ H hc7 (by linarith) hsm
  obtain ⟨𝒴, T, hL⟩ := interaction_expansion_hat_bound_dm_dir (Rσ := Rσ) hC cβ hconn hrow hκ₀ hκdec hκ h1
    hR₁ hr hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV
    hX₁V hoptV hΔV hlogV hZV hmarV 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F
    hoptF hΔF hlogF hyF 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM rE hrE hρE0
    hρE hρM0 hρM
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0' : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  -- the `ν`-part
  obtain ⟨Tν, hν⟩ := nupart_locInt_bound_hat_dm_dir (m₀ := m₀) (j := jV) (X := XV) (𝒦X := 𝒦XV)
    (X₁z := X₁V) hC hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ hBh0 hBh hcovV hX₁V hconn hrow hoptV hΔV
    hκ₀ hκdec hκ h1 (hlogV 0) hZν (ω := fun _ => (1 : ℂ)) continuous_const hR₁
    analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  obtain ⟨T', hT'⟩ := LocIntDm.addLift (SG := l1Ball d L N₁ m₁ (k + 1) N) (π := Prod.fst)
    (Rσ := Rσ) (F := unitPts Gp × Fin N → ℂ)
    (F' := (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (AgF' := fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2)
    (fun xw hxw => hxw.1) (fun Y a a' h => h.1) (fun _ => rfl) hν hL cν
  have hEps : 0 ≤ prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM := by
    unfold prop33Eps; positivity
  have hnu0 : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    unfold nuBd
    have : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by linarith
    positivity
  refine ⟨_, _, (hT'.congr_val ?_).mono fun Y => ?_⟩
  · intro xw hxw σ hσ p hp'
    rfl
  · have hb1 : 0 ≤ prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by positivity
    have hb2 : 0 ≤ ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)) := by positivity
    split_ifs <;> simp only [one_mul] at * <;> linarith


end SharpAssemble

end Balaban.Localization

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix Set Metric

section SharpPhysical

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

variable (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z))
    (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hΘ₀ : Θ₀ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
    (hεb : prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)


include hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV hX₁V hoptV hΔV hlogV hZV hmarV hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hrE hρE0 hρE hρM0 hρM hBh0 hBh hZν

/-- **The sharp assembly of the physical expansion** (`T1`).  Under exactly the hypotheses of
`interaction_expansion_hat_dm` there is ONE pair `(𝒴, T)` that is both a localized expansion for
the thick legacy relations (`PhysExpansion`, the conclusion of the landed assembler: raw datum on
`thickSet Y`, hat variables on the block thickening) and local for the sharp relations
(`PhysicalSharpLoc`: raw datum and source on `Y` itself, hat variables at the unit points of `Y`).
The sharp expansion is obtained by running the landed assembly with the sharp summands; the thick
locality follows because the thick relations imply the sharp ones. -/
theorem interaction_expansion_hat_dm_dir :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) →
        ((unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν 𝒴 T ∧
        PhysicalSharpLoc S cψ R₁ Rσ r a₁ ν eps 𝒴 T := by
  obtain ⟨𝒴, T, hD⟩ := interaction_expansion_hat_dm_core_dir (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC cβ hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr hk hG S.hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hsm (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) hcovF hX₁F hoptF hΔF hlogF hyF (μι := μι) 𝒯M (ϱ₁M := ϱ₁M) (ϱ₂M := ϱ₂M) (GkM := GkM) (GjM := GjM) (X₀M := X₀M) (X₁M := X₁M) (jM := jM) (XM := XM) (𝒦XM := 𝒦XM) (EbM := EbM) ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM (EM := EM) hEanM hEbdM rE hrE (ρE := ρE) hρE0 hρE (ρM := ρM) hρM0 hρM (Bh := Bh) hBh0 hBh cν hZν
  refine ⟨𝒴, T, ?_, hD.loc.loc⟩
  exact (hD.mono_Ag (AgΘ' := physAgΘThick S) (fun _ _ _ h => physAgΘ_of_thick S h)
    (fun _ _ _ h => h)).comap
    (F' := (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) id
    (XW' := physXW S cψ R₁ Rσ r) (fun xw h => h) (AgF' := AgFPair S)
    (fun Y a a' h => agFDirPair_of_agFPair S h) (e' := fun ψ => (ψ, ψ)) (fun _ => rfl)

variable (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁)

include hRσ hc hΘ₀ hεb hN hp

/-- **`physical_directTerms` (unconditional).**  Under the hypotheses of the landed assembler
`interaction_expansion_hat_dm` (with `hRσ`, `hc`, `hΘ₀`, the bound `hεb`, the divisibility
`L ^ m₀ ∣ N₁` and `0 < p₁`) the physical expansion is a `DirectTerms` instance for the relation
`physAgΘ` (raw datum and source on `Y`), whose labels and terms `I.𝒴`, `I.T` are a `PhysExpansion`
(the thick legacy record) that is sharply local, and whose bounds are `physB`.  No locality premise
remains: the sharp locality is `interaction_expansion_hat_dm_dir`. -/
theorem physical_directTerms :
    ∃ I : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ₀ (physSΛ S a₁ ν eps)
      (physXW S cψ R₁ Rσ r) (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (physAgΘ S) (AgFDirPair S),
      PhysExpansion (EE := EE) (EM := EM) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) (cψ := cψ) (R₁ := R₁) (Rσ := Rσ) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν I.𝒴 I.T ∧
        PhysicalSharpLoc S cψ R₁ Rσ r a₁ ν eps I.𝒴 I.T ∧
        I.b = physB (N := N) (a₁ := a₁) (ν := ν) (BG := BG) (κ := κ) (eps := eps) (BG₂ := BG₂) (δ₁ := δ₁) (κdec := κdec) (r := r) (m₀ := m₀) (ρE := ρE) (ρM := ρM) (Bh := Bh) cβ cν := by
  obtain ⟨𝒴, T, hD, hS⟩ := interaction_expansion_hat_dm_dir (S := S) (hC := hC) (cβ := cβ) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1) (hR₁ := hR₁) (hr := hr) (hk := hk) (hG := hG) (cc := cc) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := ha₁) (H := H) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE) (hlogE := hlogE) (hEbE := hEbE) (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M) (ys := ys) (is := is) (hys := hys) (hBM := hBM) (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M) (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM) (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE) (hrE := hrE) (hρE0 := hρE0) (hρE := hρE) (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0) (hBh := hBh) (cν := cν) (hZν := hZν)
  exact ⟨physicalDirectTerms_of_sharpLoc (S := S) (cβ := cβ) (hG := hG) (cc := cc) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (cν := cν) (hR₁ := hR₁) (hr := hr) (hRσ := hRσ) (hc := hc) (hΘ₀ := hΘ₀) (hεb := hεb) hN hp 𝒴 T hD hS, hD, hS, rfl⟩

end SharpPhysical

end Balaban.Fluctuation
