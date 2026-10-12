/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Field
public import Balaban.Localization.DecoupledSolve

/-!
# Theorem I-4a (a), (c): existence, uniqueness and bounds for a cover `C` and an operator `H`

The fixed point equation `δα = 𝒩_s(δα)` for the family `α ↦ G_s(α)` of the cover `C` and the
operator `H`.  The hypotheses `DecHyp H a ν ...` only involve the operator; the cover enters through
`FamSpec` (`decGreenFamily`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- The standing hypotheses of the localization setting give the hypotheses of the Green's
function bounds of BACKGROUND.md §1. -/
theorem OpSetting.toGreen (S : OpSetting H a ν) : GreenSetting H a ν where
  hd := S.hd
  hL := S.hL
  mass := S.mass
  massLe := S.massLe
  weights := S.weights
  sep := by
    have hε : 0 < agmonRate d := agmonRate_pos (by have := S.hd; omega)
    have h1 := S.one_lt_rho
    have h := S.sep
    have : agmonRate d / 16 * (ϱ - 1) ≤ agmonRate d / 2 / 2 * (ϱ - 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

/-- The Green family of `G_s`: `α ↦ G_s(α)`, with the parameters `s` extended by `1`. -/
noncomputable def decG (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (s : DecParams C) : (H.Ω 1 → ℂ) → Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  fun α => Gs C H a ν α (extS C s)

variable (C H a ν) in
/-- The fixed point equation of Theorem I-4a: `δα = 𝒩_s(δα)`, with
`δφ(δα) = G_s(α₀ + δα)(F_s - δα φ₀)`. -/
def DecFixed (s : DecParams C) (ιU : Bool) (α₀ : H.Ω 1 → ℂ)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) : Prop :=
  Nmap H (dirichletOperator H a ν α₀) ιU φ₀ Fs (dphi H (decG C H a ν s) α₀ φ₀ Fs δα) = δα

/-- **Theorem I-4a (a), (c) for one parameter `s`**: existence, uniqueness in the ball
`|δα|₂ ≤ c₆` and the bounds, in both modes.  The family `G_s` is the decoupled Green's operator;
the constants are `famConst d L B_G κ₁`. -/
theorem i4a_exists_unique {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) :
    ∀ {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : DecParams C}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {ιU : Bool} {α₀ : H.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
        {f₁ : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ},
      DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁ →
      δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) →
      δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) →
      ∃ δα : H.Ω 1 → ℂ,
        DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα ∧
        Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small H δα (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα)
          (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : H.Ω 1 → ℂ, Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα' → δα' = δα) ∧
        (ιU = false → δΨ = 0 → f₁ = 0 → δα = 0 ∧
          dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα = 0) := by
  obtain ⟨-, hBG, Hfam⟩ := hF
  intro N₁ m₁ K N _ ϱ C H a ν S κ hκ hM s hs ιU α₀ φ₀ δΨ f₁ δ₀ δ₁ Hh hδ₀ hδ₁
  obtain ⟨⟨hfam, hsup⟩, -⟩ := Hfam C H S hκ hM hs N
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB1 : 1 ≤ B := famConst_ge_one hBG κ hd0
  have hB0 : 0 ≤ B := by linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  obtain ⟨δα, hsmall, hfix, hsb, hstar, huniq⟩ := prop51_core hfam Hh.setup hC
  have hsb' := selfBound'_le (d := d) (L := L) (N := N) hB0 Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  have hcN := cN'_pos (d := d) (L := L) (N := N) hB0
  have hF := Balaban.Background.cF_pos d L
  have hδ1 := Hh.δ₁_nn
  have hr2 : δ₀ + 2 * coreBound N B (commKConst d L N) (2 * d + 8) δ₀ (cF d L * δ₁) (5 * δ₁) ≤ Γ := by
    linarith [hC.poly, hC.self, hC.ρ_nn]
  have hcb : coreBound N B (commKConst d L N) (2 * d + 8) δ₀ (cF d L * δ₁) (5 * δ₁) ≤ cN' d L N B * δ₁ :=
    hsb'
  have hK : 2 * cN' d L N B * δ₁ ≤ cK2' d L N B * δ₁ := by
    unfold cK2'
    nlinarith [mul_nonneg (by linarith : 0 ≤ B + 1) (mul_nonneg hF.le hδ1),
      mul_nonneg hcN.le hδ1, mul_nonneg (mul_nonneg (by linarith : 0 ≤ B + 1) hcN.le) hδ1]
  have hsmall2 : Small H δα (cK2' d L N B * δ₁) := fun x => by
    refine (hsb x).trans ?_
    nlinarith
  have hdp : SupBounds H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα)
      (cK2' d L N B * δ₁) := by
    have hFs := Fsrc_bd Hh.setup hsb
    have hX : 0 ≤ cF d L * δ₁ + 3 / 2 * (2 * coreBound N B (commKConst d L N) (2 * d + 8) δ₀
        (cF d L * δ₁) (5 * δ₁)) := by
      have := coreBound_nonneg (N := N) hB0 Hh.setup.Kc_nn Hh.setup.Rc_nn Hh.δ₀_nn Hh.setup.Fb_nn
        Hh.setup.Gb_nn
      have := Hh.setup.Fb_nn
      positivity
    have := hsup (α := α₀ + δα) (Hh.setup.poly hsb hr2) _ hX hFs
    refine this.mono ?_
    unfold cK2'
    calc B * (cF d L * δ₁ + 3 / 2 * (2 * coreBound N B (commKConst d L N) (2 * d + 8) δ₀
          (cF d L * δ₁) (5 * δ₁)))
        ≤ (B + 1) * (cF d L * δ₁ + 3 * (cN' d L N B * δ₁)) := by
          refine mul_le_mul (by linarith) (by linarith) hX (by linarith)
      _ ≤ _ := by nlinarith [mul_nonneg hcN.le hδ1, mul_nonneg hF.le hδ1,
            mul_nonneg (mul_nonneg hcN.le hδ1) hB0]
  refine ⟨δα, hfix, hsmall, hsmall2, hdp, fun δα' hs' hf' => huniq δα' hs' hf', ?_⟩
  intro hι hΨ hf
  subst hι hΨ hf
  rw [pertSource_zero] at *
  -- zero is a fixed point in the ball
  have hz : Small H (0 : H.Ω 1 → ℂ) (c6' d L N B Γ) := by
    intro x; have := (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le; simp [this]
  have h0 : DecFixed C H a ν s false α₀ φ₀ 0 0 := by
    unfold DecFixed dphi
    have : Fsrc φ₀ (0 : H.Ω 1 × Fin N → ℂ) (0 : H.Ω 1 → ℂ) = 0 := by
      funext p; simp [Fsrc]
    rw [this, Matrix.mulVec_zero]
    exact Nmap_zero_zero H _ φ₀
  have e0 : δα = 0 := (huniq 0 hz h0).symm
  refine ⟨e0, ?_⟩
  subst e0
  unfold dphi
  have : Fsrc φ₀ (0 : H.Ω 1 × Fin N → ℂ) (0 : H.Ω 1 → ℂ) = 0 := by
    funext p; simp [Fsrc]
  rw [this, Matrix.mulVec_zero]

end Balaban.Localization.Dec2
