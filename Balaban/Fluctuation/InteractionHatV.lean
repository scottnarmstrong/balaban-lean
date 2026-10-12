/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineLocalEngine
public import Balaban.Fluctuation.InteractionVPart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential part of the localized interaction in the variable `ψ̂`

For a datum `D` of `Ξ^c(𝔹_{k+1}; 1, ε)` the fluctuation field attached to a hat variable `ψ̂` of the
unit lattice is `ψ' = liftC (cc • C^{1/2}(1) ψ̂)` (`hatLift`), a *linear* map of `ψ̂`
(`hatLift_add_smul`).  Hence the ray `(σ t) x₀ + τ w` in `ψ̂` is the ray in `ψ'` through
`hatLift (σ t x₀)` with direction `hatLift w`, and the third derivative of the potential along the
`ψ̂`-ray is the third derivative along the `ψ'`-ray (`dirS3_hatFun`).  The block energies expand by
`i5_functional_hat` with terms local in `ψ̂` (`AgHat`); `vpart_locInt_hat` is `vpart_locInt` with
that locality.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section HatLift

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (Gp a₁ ν) in
/-- **The decoupled square root at `s ≡ 1`** at the background `(φ, α)` of the datum `D`:
`C^{1/2}(1)`. -/
noncomputable def hatCovSqrt (D : BgData Gp N) :
    Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ :=
  decCovSqrt Gp (compWeight L a₁) a₁ ν
    (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
    (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)) (unitQ Gp) (unitP Gp)

variable (Gp a₁ ν) in
/-- **The fluctuation field of a hat variable**: `ψ' = liftC (cc • C^{1/2}(1) ψ̂)`. -/
noncomputable def hatLift (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (D : BgData Gp N)
    (ψh : unitPts Gp × Fin N → ℂ) : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  liftC hG' (cc • (hatCovSqrt Gp a₁ ν D *ᵥ ψh))

/-- `ψ̂ ↦ ψ'` is linear. -/
theorem hatLift_add_smul (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (D : BgData Gp N)
    (z w : unitPts Gp × Fin N → ℂ) (τ : ℂ) :
    hatLift Gp a₁ ν hG' cc D (z + τ • w) =
      hatLift Gp a₁ ν hG' cc D z + τ • hatLift Gp a₁ ν hG' cc D w := by
  unfold hatLift
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, map_add]
  congr 1
  rw [smul_comm cc τ, map_smul]

theorem hatLift_smul (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (D : BgData Gp N)
    (z : unitPts Gp × Fin N → ℂ) (t : ℂ) :
    hatLift Gp a₁ ν hG' cc D (t • z) = t • hatLift Gp a₁ ν hG' cc D z := by
  have := hatLift_add_smul (a₁ := a₁) (ν := ν) hG' cc D 0 z t
  simpa [hatLift] using this

theorem isLayerConstant_hatLift (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (D : BgData Gp N) (ψh : unitPts Gp × Fin N → ℂ) :
    IsLayerConstant Hm (hatLift Gp a₁ ν hG' cc D ψh) :=
  isLayerConstant_liftC hG hG' _

section Mem

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The fluctuation of a bounded hat variable lies in the ball** (the `s ≡ 1` case of
`hatPsiF_mem_flBallLC`, with `ψ'(1) = liftC (cc • C^{1/2}(1) ψ̂)` identified through
Theorem I-4b (v)). -/
theorem hatLift_mem_flBallLC (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    hatLift Gp a₁ ν hG' cc D ψh ∈ FlBallLC Hm δ₁ := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  obtain ⟨F₁, -, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by simpa using hE1
  have hmem := hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hs hD hψh
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hFeq : F₁ ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)), rawOf D) = (φ, α) := hF₁ _ D hs hU φ α hI
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  have heq : hatPsiF Gp a₁ ν hG' cc F₁ (fun _ => 1) (rawOf D) ψh =
      hatLift Gp a₁ ν hG' cc D ψh := by
    unfold hatPsiF hatSqrtF hatLift hatCovSqrt
    rw [hFeq, extS_one, hφ1, hα1]
    rfl
  rw [← heq]; exact hmem

end Mem

open Classical in
/-- **A function of the fluctuation, as a function of the raw data and the hat variable**
(`0` for unrealizable data): `f(Θ, ψ̂) = f(Θ, ψ'(Θ, ψ̂))`, `ψ' = hatLift Θ ψ̂`. -/
noncomputable def hatFun (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a₁ ν eps : ℝ)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (f : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) : ℂ :=
  if h : ∃ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D ∧ u.1 = rawOf D then
    f (u.1, hatLift Gp a₁ ν hG' cc h.choose u.2)
  else 0

theorem hatFun_rawOf (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {eps : ℝ}
    (f : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (ψh : unitPts Gp × Fin N → ℂ) :
    hatFun Gp a₁ ν eps hG' cc f (rawOf D, ψh) = f (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) := by
  classical
  have h : ∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' ∧
      rawOf D = rawOf D' := ⟨D, hD, rfl⟩
  unfold hatFun
  simp only [h, dite_true]
  have := BgData.eq_of_raw h.choose_spec.2
  rw [← this]

theorem hatFun_line (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {eps : ℝ}
    (f : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (z w : unitPts Gp × Fin N → ℂ) (τ : ℂ) :
    hatFun Gp a₁ ν eps hG' cc f (rawOf D, z + τ • w) =
      f (rawOf D, hatLift Gp a₁ ν hG' cc D z + τ • hatLift Gp a₁ ν hG' cc D w) := by
  rw [hatFun_rawOf hG' cc f hD, hatLift_add_smul]

/-- **The third derivative along a hat ray is that along the lifted ray.** -/
theorem dirS3_hatFun (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {eps : ℝ}
    (f : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (z w : unitPts Gp × Fin N → ℂ) :
    dirS3 (hatFun Gp a₁ ν eps hG' cc f) w (rawOf D) z =
      dirS3 f (hatLift Gp a₁ ν hG' cc D w) (rawOf D) (hatLift Gp a₁ ν hG' cc D z) := by
  unfold dirS3
  have : (fun τ : ℂ => hatFun Gp a₁ ν eps hG' cc f (rawOf D, z + τ • w)) =
      fun τ : ℂ => f (rawOf D, hatLift Gp a₁ ν hG' cc D z + τ • hatLift Gp a₁ ν hG' cc D w) :=
    funext fun τ => hatFun_line hG' cc f hD z w τ
  rw [this]

end HatLift

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block energy expands over the domains `Y ⊃ X₁`, with terms local in `ψ̂`** (the hat
version of `vblock_expansion`; `i5_functional_hat` for the chord-energy functional). -/
theorem vblock_expansion_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ k :=
    (hC.HBp.weights k hk (by omega)).1.trans' (by norm_num)
  have hEb := energyBd_nonneg (d := d) (L := L) (N := N) ha hC.HBp.mass hV hC.δ₁_pos.le hρ
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁
    hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
    ((blockEnergyFun_analytic _ ν k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using blockEnergyFun_bound hC hk le_rfl z ht)
    (Z := readSites Hm k z) (Zα := ↑(blockSites d L N₁ m₁ (k + 1) k z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local _ ν k z hα hδ hψ)
  refine ⟨Ev, fun D hD ψh hψh => ?_, h2', fun Y u hu => ?_, h4'⟩
  · rw [hatFun_rawOf hG' cc _ hD, blockEnergyOne_rawOf hD k z]
    exact h1' D hD ψh hψh
  · have := h3' Y u hu
    rw [hΔ] at this
    simpa using this

end Block

section LocHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

variable (Gp) in
/-- **Agreement of two hat variables on the thickening of `Y`**: equal at the unit points of the
sites of `blockThick Y`. -/
def AgHatF (hG' : IsLevel Gp (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (z z' : unitPts Gp × Fin N → ℂ) : Prop :=
  ∀ y ∈ blockThick Y, ∀ i, z (unitPt hG' y, i) = z' (unitPt hG' y, i)

variable (Gp) in
/-- The admissible rays in the hat variable: `(σ t) x₀ + τ w` stays in the ball `|ψ̂| ≤ cψ`. -/
def HatRays (cψ : ℝ) (R₁ Rσ r : ℝ) :
    Set ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) :=
  {xw | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
    (σ * t) • xw.1 + τ • xw.2 ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}}

/-- **The potential part of the localized interaction, one block, in the variable `ψ̂`.** -/
theorem vblock_locInt_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := vblock_expansion_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ hmar
  refine ⟨Ev, hsum, hanY, ?_⟩
  refine locInt_dir3 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (f := hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) _ hR₁ hω hωc hMω
    hωb hr hanY (fun Y u hu => hbd Y u hu) ?_ ?_ ?_
  · intro Y a a' b b' p q ha hb y hy i
    simp [ha y hy i, hb y hy i]
  · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
    exact hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ ⟨h1', h2'⟩
  · intro Θ hΘ ψh hψh
    obtain ⟨D, hD, rfl⟩ := hΘ
    exact hsum D hD ψh hψh

end LocHat

section VPartHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The potential part of the localized interaction in the variable `ψ̂`** (Proposition 3.3,
the `V`-part, hat version of `vpart_locInt`): for the exact interaction potential `V^{(k)}` of
Lemma 2.3 (b), as a function of the raw data `Θ` and the hat variable `ψ̂`
(`ψ' = liftC (cc • C^{1/2}(1) ψ̂)`), `σ ∫₀¹ ω(t') ∂_w³ V(σ t' x₀) dt'` along the `ψ̂`-ray is a
localized expansion over the domains `Y ⊃ X₁`: the terms are analytic in `(Θ, σ)`, bounded by
`|σ| M_ω 6 E e^{-2 κ d̃^{cov}_{k+1}(Y)} / r³`, vanish at `σ = 0`, and depend on `Θ` through
`thickSet Y` and on `(x₀, w)` through their values at the unit points of the sites of
`blockThick Y`. -/
theorem vpart_locInt_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
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
    {m₀ j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup Gp (m₀ z) (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ z) (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne (m₀ z) (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L (m₀ z) m₁ (j z)) E₀ = treeLenCovOne (m₀ z) (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne (m₀ z) (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZ : ∀ z, readSites Hm k z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
        Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ 𝒴 z then T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (interactionOne hG hG' le_rfl a₁ ν eps)) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ 𝒴 z then Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  have hex : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ),
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := fun z =>
    vblock_locInt_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ (hcov z) (hX₁ z) hconn hrow (hopt z)
      (hΔ z) hκ₀ hκdec hκ h1 (hlog z) z (hZ z) (hmar z) hωc hR₁ hω hMω hωb hr
  choose Ev hEvsum hEvan hEv using hex
  refine ⟨fun z => polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)),
    fun z Y x₀ w σ Θ => rayTerm (dl3 (Ev z Y) w) ω x₀ σ Θ, ?_⟩
  refine (LocInt.finsum Finset.univ (fun z _ => hEv z)).congr_val ?_
  rintro ⟨x₀, w⟩ hxw σ hσ Θ ⟨D', hD, rfl⟩
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hdisc : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} :=
    fun t ht τ hτ => hxw σ hσ t (hreal1 t ht) τ hτ
  have hsum' : ∀ z, ∀ Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps,
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (Θ, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) =>
          i.1.1) Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)), Ev z Y (Θ, ψh) := by
    intro z Θ hΘ ψh hψh
    obtain ⟨D'', hD'', rfl⟩ := hΘ
    exact hEvsum z D'' hD'' ψh hψh
  have hint : ∀ z, IntervalIntegrable (fun t : ℝ => ω (t : ℂ) * dirS3
      (hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) w (rawOf D')
      ((σ * (t : ℂ)) • x₀)) MeasureTheory.volume 0 1 := fun z =>
    raySrc3_intervalIntegrable (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
      (B := {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) _ (Evs := Ev z)
      (fun Y => hEvan z Y) (hsum' z) hωc ⟨D', hD, rfl⟩ hr hdisc
  have hψmem : ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
      hatLift Gp a₁ ν hG' cc D' ψh ∈ FlBall Hm δ₁ := fun ψh hψh =>
    (hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh).1
  unfold raySrc3
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun z _ => hint z)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only
  rw [← Finset.mul_sum]
  congr 1
  rw [dirS3_hatFun hG' cc _ hD]
  have hs : ∀ z, dirS3 (hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) w
      (rawOf D') ((σ * (t : ℂ)) • x₀) =
      dirS3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (hatLift Gp a₁ ν hG' cc D' w) (rawOf D')
        (hatLift Gp a₁ ν hG' cc D' ((σ * (t : ℂ)) • x₀)) := fun z =>
    dirS3_hatFun hG' cc _ hD _ _
  simp only [hs]
  refine dirS3_interactionOne hC hG hG' le_rfl ha₁ H hc7 hR hRs hsmall hnum hnum' hD
    (hreal D' hD) (isLayerConstant_hatLift hG hG' cc D' _) (isLayerConstant_hatLift hG hG' cc D' _)
    hr (fun τ hτ => ?_) ?_
  · rw [← hatLift_add_smul]
    exact hψmem _ (hdisc t ht τ hτ.le)
  · intro z
    have hcd := contDiffAt_line_of_sum (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
      (B := {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) _ (Evs := Ev z)
      (fun Y => hEvan z Y) (hsum' z) ⟨D', hD, rfl⟩ (z := (σ * (t : ℂ)) • x₀) (w := w) hr
      (fun τ hτ => hdisc t ht τ hτ)
    have e : (fun τ : ℂ => blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z
        (rawOf D', hatLift Gp a₁ ν hG' cc D' ((σ * (t : ℂ)) • x₀) +
          τ • hatLift Gp a₁ ν hG' cc D' w)) =
        fun τ : ℂ => hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)
          (rawOf D', (σ * (t : ℂ)) • x₀ + τ • w) :=
      funext fun τ => (hatFun_line hG' cc _ hD _ _ τ).symm
    rw [e]; exact hcd

end VPartHat

end Balaban.Localization
