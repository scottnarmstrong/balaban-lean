/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledHolder
public import Balaban.Localization.DecoupledFieldClose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-4a (c): the Hölder part for `δφ(s)` (LOCALIZATION.md §3.2)

* `HolSpec`: the conclusion of `dg2_holder` (Hölder seminorm of `∂ G_s(A) f`) with constants
  `(c, B_H)`;
* `holder_liftOp`: from the scalar Hölder bound to the components of `liftOp N M g`;
* `i4a_holder`: for the solution `δα` of Theorem I-4a, every component of
  `δφ(s) = G_s(α₀ + δα)(F_s - δα φ₀)` has Hölder seminorm
  `|∂ δφ(s)|_{(θ),2-θ} ≤ (B_H e^{N₀κ₁}/θ)(C_F δ₁ + 3/2 K₂ δ₁)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Spec

variable {d L : ℕ} [NeZero L]

/-- The conclusion of `dg2_holder` with the constants `(c, B_H)`. -/
def HolSpec (d L : ℕ) [NeZero L] (cstar BH : ℝ) : Prop :=
  0 ≤ cstar ∧ 0 ≤ BH ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      HolderSeminormLE G (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f)) θ (2 - θ)
        (BH * Real.exp (N0 d L * κ) / θ * C)

theorem HolSpec.mono {c c' BH BH' : ℝ} (h : HolSpec d L c BH) (hc : c ≤ c') (hB : BH ≤ BH') :
    HolSpec d L c' BH' := by
  refine ⟨h.1.trans hc, h.2.1.trans hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hM s hs θ hθ0 hθ1 f C hC hf
  have hM' : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM
  intro x hx x' hx' hne z hz ν'
  refine (h.2.2 G S hα hκ hM' hs hθ0 hθ1 f hC hf x hx x' hx' hne z hz ν').trans ?_
  have : BH * Real.exp (N0 d L * κ) / θ * C ≤ BH' * Real.exp (N0 d L * κ) / θ * C := by
    have := (Real.exp_pos (N0 d L * κ)).le
    gcongr
  exact this

theorem holSpec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) : ∃ c BH : ℝ, HolSpec d L c BH := by
  obtain ⟨c, B, hc, hB, H⟩ := dg2_holder (d := d) (L := L) hd hL
  refine ⟨c, B, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hM s hs θ hθ0 hθ1 f C hC hf
  exact H G S hα hκ hM hs hθ0 hθ1 f hC hf

end Spec

section Vec

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **From the scalar Hölder bound to the components of `liftOp N M g`.** -/
theorem holder_liftOp {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {θ b : ℝ}
    (h : ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      HolderSeminormLE G (zeroExt (G.Ω 1) (M *ᵥ f)) θ (2 - θ) (b * C))
    (g : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C) (hg : SrcBound G g C) (i : Fin N) :
    HolderSeminormLE G (fun y => svec G (liftOp N M *ᵥ g) y i) θ (2 - θ) (b * C) := by
  have := h (comp G g i) hC (fun x => hg x i)
  intro x hx x' hx' hne z hz ν'
  simp only [svec_liftOp]
  exact this x hx x' hx' hne z hz ν'

/-- **Theorem I-4a (c), Hölder part.**  Under the hypotheses of `i4a_exists_unique` (smallness
`δ₀, δ₁ ≤ δ_*`), every solution `δα` of the fixed point equation with `|δα|₂ ≤ c₆` and
`|δα|₂ ≤ K₂ δ₁` gives a field `δφ(s)` whose components have
`|∂ δφᵢ|_{(θ),2-θ} ≤ (B_H e^{N₀κ₁}/θ) (C_F δ₁ + (3/2) K₂ δ₁)`. -/
theorem i4a_holder {cstar BG BH : ℝ} (hF : FamSpec d L cstar BG) (hH : HolSpec d L cstar BH)
    (S : DGSetting G a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {δα : G.Ω 1 → ℂ}
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hsm2 : Small G δα (cK2' d L N (famConst d L BG κ) * δ₁))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (i : Fin N) :
    HolderSeminormLE G
      (fun y => svec G (dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα) y i) θ (2 - θ)
      (BH * Real.exp (N0 d L * κ) / θ *
        (cF d L * δ₁ + 3 / 2 * (cK2' d L N (famConst d L BG κ) * δ₁))) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hBG : 0 ≤ BG := hF.2.1
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB1 : 1 ≤ B := famConst_ge_one hBG κ hd0
  have hB0 : 0 ≤ B := by linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hc6a : c6' d L N B Γ ≤ Γ / 4 := min_le_left _ _
  have hs2 : deltaStar' d L N B Γ ≤ Γ / 4 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hpoly : Small G (α₀ + δα) Γ := H.setup.poly hsm (by linarith [hδ₀.trans hs2])
  have hadm : AdmPot G (α₀ + δα) := admPot_of_small hd0 hpoly
  have hFs := Fsrc_bd H.setup hsm2
  have hCnn : 0 ≤ cF d L * δ₁ + 3 / 2 * (cK2' d L N B * δ₁) := by
    have h1 := Balaban.Background.cF_pos d L
    have h2 := H.δ₁_nn
    have h3 : 0 ≤ cK2' d L N B := by
      unfold cK2'
      have := cN'_pos (d := d) (L := L) (N := N) hB0
      have := Balaban.Background.cF_pos d L
      positivity
    positivity
  have hs' := extS_norm_le (G := G) hκ hs
  have key := holder_liftOp (G := G) (M := Gs G a ν (α₀ + δα) (extS G s)) (θ := θ)
    (b := BH * Real.exp (N0 d L * κ) / θ)
    (fun f C hC hf => hH.2.2 G S hadm hκ hM hs' hθ0 hθ1 f hC hf)
    (Fsrc φ₀ (pertSource G a δΨ f₁) δα) hCnn hFs i
  exact key

end Vec

end Balaban.Localization
