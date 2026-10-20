/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KfZeroFR
public import Balaban.Spine.KfZeroFRTyping
public import Balaban.LargeField.Base.KF0FRCount
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KfZeroInput` by route FR

`notes/phase1/KF0-FR.md`. Under the typing condition of route FR (the block side `M L` is at least
`kf0FRs0 d N L κ`, a lower bound depending on `d, N, L, κ` only), the spine input `KfZeroInput`
holds (`kfZeroInput_of_typing`). At fixed `κ, c₉` the parameters are the functions of the block
side of `KfZeroFRTyping`, the source radius is `G = c_G √β`, `β₀` is chosen by `frBeta_large`, and
the activities are those of `kf0FR_observable` (`kf0FR_fixed`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Polymer Balaban.Green MeasureTheory Balaban.LargeField.SphereChart
  Balaban.LargeField.KF0FR

noncomputable section

variable {d N : ℕ}

/-- The lower bound of the constant of the Jacobian, uniformly in the mass. -/
def frC0Star (d L : ℕ) : ℝ := frNuStar L / (2 * d + 1) * (Real.sqrt (2 * d + 1))⁻¹

theorem frC0Star_pos (d : ℕ) {L : ℕ} (hL : 1 ≤ L) : 0 < frC0Star d L := by
  unfold frC0Star; have := frNuStar_pos hL; positivity

theorem frC0Star_le {L : ℕ} (hL : 1 ≤ L) {ν : ℝ} (hν1 : frNuStar L ≤ ν) (hν : ν ≤ 1) :
    frC0Star d L ≤ (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ := by
  have hs := frNuStar_pos hL
  have hνp : 0 < ν := lt_of_lt_of_le hs hν1
  unfold frC0Star
  have e : 1 - 2 * (d : ℝ) / (2 * d + ν) = ν / (2 * d + ν) := by field_simp; ring
  rw [e]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · exact inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt (by linarith))

/-- `e^{1/4} ≤ 2`. -/
theorem exp_quarter_le_two : Real.exp (1 / 4) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 1 = Real.exp (1 / 4) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)).1
    (by rw [← e]; norm_num at h ⊢; linarith)

/-! ### The parameters of the block side -/

theorem frP_pos (d N : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) : 0 < frP d N κ s := by
  unfold frP
  refine Real.sqrt_pos.2 (mul_pos (by norm_num) (Real.log_pos ?_))
  have h1 := frEta_pos d κ hs
  have h2 := frEta_le_one d hκ hs
  rw [lt_div_iff₀ h1]
  have : (1 : ℝ) ≤ 2 ^ (N - 1) := one_le_pow₀ (by norm_num)
  linarith

theorem frTau_mul_frS1 (d : ℕ) (κ : ℝ) (s : ℕ) : frTau d κ s * frS1 d s = frBs d κ s / 4 := by
  have hne : (frS1 d s : ℝ) ≠ 0 := by
    have := one_le_frS1 d s
    exact_mod_cast (by omega : frS1 d s ≠ 0)
  unfold frTau
  field_simp

theorem frEta_mul (d : ℕ) (κ : ℝ) (s : ℕ) :
    (8 : ℝ) ^ frKk d s * Real.exp 1 * frEta d κ s = frTau d κ s ^ (2 * frKk d s) := by
  unfold frEta
  field_simp

/-- The constant of the block gas: `(1+d) 3^d s^d b_* e^{(κ₀+κ₁) 3^d} = 1/16`. -/
theorem frH0_eq (d : ℕ) (κ : ℝ) {s : ℕ} (hs : 1 ≤ s) :
    (1 + d) * 3 ^ d * (s : ℝ) ^ d * frBs d κ s *
      Real.exp ((kf0K0 d + (κ + kf0K0 d + 5 / 2)) * 3 ^ d) = 1 / 16 := by
  have : (0 : ℝ) < s := by exact_mod_cast hs
  unfold frBs frD
  rw [Real.exp_neg]
  field_simp

theorem frSmall_le (d : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) {s : ℕ} (hs : 1 ≤ s) :
    ((1 + d) * 3 ^ d * (s : ℝ) ^ d) * frBs d κ s ≤ 1 / 2 := by
  have h := frH0_eq d κ hs
  have he : 1 ≤ Real.exp ((kf0K0 d + (κ + kf0K0 d + 5 / 2)) * 3 ^ d) :=
    Real.one_le_exp (frD_nonneg d hκ)
  have h0 : 0 ≤ ((1 + d) * 3 ^ d * (s : ℝ) ^ d) * frBs d κ s := by
    have := frBs_pos d κ hs
    positivity
  nlinarith

theorem frNuStar_le_of {L : ℕ} (hL : 1 ≤ L) {ν : ℝ} (hν : 7 / 8 < ν * (L : ℝ) ^ 2) :
    frNuStar L ≤ ν := by
  unfold frNuStar
  have : (0 : ℝ) < L := by exact_mod_cast hL
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The source radius constant `c_G` of route FR and its three constraints. -/
theorem frCG_facts {p bs ns k s₁ cG : ℝ} (hp : 0 < p) (hbs : 0 < bs) (hns : 0 < ns) (hk : 0 < k)
    (hs₁ : 0 < s₁) (hcG : cG = min (bs * Real.sqrt ns / (96 * p))
      (min (Real.sqrt ns / (8 * p * k * s₁)) (p * Real.sqrt ns / 16))) :
    0 < cG ∧ 2 * cG / Real.sqrt ns * p * (k * s₁) ≤ 1 / 4 ∧ 2 * cG / Real.sqrt ns ≤ p / 8 ∧
      2 * cG * p / Real.sqrt ns ≤ bs / 48 := by
  have hsq : 0 < Real.sqrt ns := Real.sqrt_pos.2 hns
  have hcG1 : cG ≤ bs * Real.sqrt ns / (96 * p) := by rw [hcG]; exact min_le_left _ _
  have hcG2 : cG ≤ Real.sqrt ns / (8 * p * k * s₁) := by
    rw [hcG]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hcG3 : cG ≤ p * Real.sqrt ns / 16 := by
    rw [hcG]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨by rw [hcG]; positivity, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at hcG2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hsq]
    linarith
  · rw [le_div_iff₀ (by norm_num)] at hcG3
    rw [div_le_iff₀ hsq]
    linarith
  · rw [le_div_iff₀ (by positivity)] at hcG1
    rw [div_le_iff₀ hsq]
    linarith

/-! ### The conditions at large `β` -/

/-- **The ordinary bounds at large `β`**: `ρ ≤ 1/2`, the bracket of (O5) is at most `1`, and every
ordinary bound is at most `b_*/4`. -/
theorem frOrd_facts {β ν ns p bs cG θ ρ G : ℝ} (hns : 0 < ns) (hνs : ns ≤ ν) (hβ : 0 < β)
    (hp : 0 < p) (hcG : 0 < cG) (hbs1 : bs ≤ 1)
    (hθ1 : θ ≤ bs / (24 * p ^ 2)) (hGρ : 2 * cG * p / Real.sqrt ns ≤ bs / 48)
    (B2 : p ^ 2 / (β * ns) ≤ bs / 48)
    (B3 : p ^ 4 / (2 * β * ns) ≤ bs / 48) (B4 : p ^ 4 / (2 * β * ns ^ 2) ≤ bs / 4)
    (hρ : ρ = (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p)) (hG : G = cG * Real.sqrt β) :
    ρ ≤ 1 / 2 ∧ β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2 ≤ 1 ∧
      ∀ {ℓ : ℕ} (t : FRTerm d ℓ), frEps β ν ρ G θ p t ≤ bs / 4 := by
  have hν0 : 0 < ν := lt_of_lt_of_le hns hνs
  have hβν : β * ns ≤ β * ν := mul_le_mul_of_nonneg_left hνs hβ.le
  have hsq : 0 < Real.sqrt ns := Real.sqrt_pos.2 hns
  have hsνs : Real.sqrt ns ≤ Real.sqrt ν := Real.sqrt_le_sqrt hνs
  have hρsq : ρ ^ 2 = p ^ 2 / (β * ν) := by
    rw [hρ, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hβ.le, Real.sq_sqrt hν0.le]
    field_simp
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hpβ : p ^ 2 / (β * ν) ≤ p ^ 2 / (β * ns) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hβν
  have hT0 : ρ ^ 2 ≤ bs / 48 := by rw [hρsq]; exact hpβ.trans B2
  have hρ2 : ρ ≤ 1 / 2 := (pow_le_pow_iff_left₀ hρ0 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)).1
    (by linarith)
  have hT1 : β * ν / 2 * ρ ^ 4 ≤ bs / 48 := by
    have e : β * ν / 2 * ρ ^ 4 = p ^ 4 / (2 * β * ν) := by
      rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρsq]; field_simp
    rw [e]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)) B3
  have hT2 : 2 * G * ρ ≤ bs / 48 := by
    have e : 2 * G * ρ = 2 * cG * p / Real.sqrt ν := by rw [hG, hρ]; field_simp
    rw [e]
    exact le_trans (div_le_div_of_nonneg_left (by positivity) hsq hsνs) hGρ
  have hT3 : θ * p ^ 2 / 2 ≤ bs / 48 := by
    rw [le_div_iff₀ (by positivity)] at hθ1; linarith
  have hT4 : β * ρ ^ 4 / 2 ≤ bs / 4 := by
    have e : β * ρ ^ 4 / 2 = p ^ 4 / (2 * β * ν ^ 2) := by
      rw [show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρsq]; field_simp
    rw [e]
    have : ns ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ hns.le hνs 2
    have h2 : 2 * β * ns ^ 2 ≤ 2 * β * ν ^ 2 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    exact le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity) h2) B4
  refine ⟨hρ2, by linarith, fun {ℓ} t => ?_⟩
  rcases t with x | x
  · simp only [frEps]; linarith
  · simp only [frEps]; exact hT4

/-- **The heavy conditions at large `β`**: the hypotheses `hJord`, `hη1`–`hη3` of the product bound
`norm_integral_prod_frF_le`, uniformly in `7/8 L⁻² < ν ≤ 1`. -/
theorem frHeavy_facts {L : ℕ} (hL : 1 ≤ L) {β ν ns p cG aS η M0 Γ Wc c0 G ε : ℝ}
    (hns : ns = frNuStar L) (hνs : ns ≤ ν) (hν1 : ν ≤ 1) (hβ1 : 1 ≤ β) (hcG : 0 < cG)
    (haS : aS = 2 * cG / Real.sqrt ns)
    (hpt : (2 : ℝ) ^ (N - 1) * Real.exp (-p ^ 2 / 8) = η / 4)
    (hM0 : M0 = 2 ^ (N - 1) * Real.exp (2 * aS ^ 2))
    (hΓ : Γ = (2 * Real.pi) ^ (-((N - 1 : ℕ) : ℝ) / 2)) (hWc0 : 0 ≤ Wc)
    (hc0 : c0 = (frC0Star d L)⁻¹ ^ (N - 1) * Real.exp (aS ^ 2))
    (hG : G = cG * Real.sqrt β) (hε : ε = Real.exp (-(β * ν)))
    (B5 : 2 * cG * Real.sqrt β ≤ ns * β / 4) (B6 : 2 * M0 * Real.exp (-(ns / 4 * β)) ≤ η / 2)
    (B7 : M0 * Real.exp (-(ns * β)) ≤ η / 4)
    (B8 : Γ * 2 * Wc * c0 * β ^ (N - 1) * Real.exp (-(ns / 128 * β)) ≤ η)
    (B9 : Γ * Wc * c0 * β ^ (N - 1) * Real.exp (-(ns / 128 * β)) ≤ 1) :
    (2 * Real.pi) ^ (-((N - 1 : ℕ) : ℝ) / 2) * Real.exp (-(β * ν / 128)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ 1 ∧
    2 * (2 ^ (N - 1) * Real.exp (-p ^ 2 / 8)) +
      2 * Real.exp (-(β * ν / 2) + 2 * G) * (2 ^ (N - 1) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η ∧
    2 ^ (N - 1) * Real.exp (-p ^ 2 / 8) +
      ε * (2 ^ (N - 1) * Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η ∧
    (2 * Real.pi) ^ (-((N - 1 : ℕ) : ℝ) / 2) *
      Real.exp ((2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2) *
        (Real.exp (-(β * ν / 128)) + Real.exp (-(β * ν / 2) + 2 * G)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ η := by
  have hns0 : 0 < ns := by rw [hns]; exact frNuStar_pos hL
  have hνs' : frNuStar L ≤ ν := hns ▸ hνs
  have hβ0 : 0 < β := by linarith
  have hν0 : 0 < ν := lt_of_lt_of_le hns0 hνs
  have hβν : β * ns ≤ β * ν := mul_le_mul_of_nonneg_left hνs hβ0.le
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν0
  have hsq : 0 < Real.sqrt ns := Real.sqrt_pos.2 hns0
  have hsνs : Real.sqrt ns ≤ Real.sqrt ν := Real.sqrt_le_sqrt hνs
  have hη0 : 0 < η := by
    have : 0 < (2 : ℝ) ^ (N - 1) * Real.exp (-p ^ 2 / 8) := by positivity
    linarith
  have ha : 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ = 2 * cG / Real.sqrt ν := by
    rw [hG]; field_simp
  have haS' : 2 * cG / Real.sqrt ν ≤ aS := by
    rw [haS]; exact div_le_div_of_nonneg_left (by positivity) hsq hsνs
  have ha0 : 0 ≤ 2 * cG / Real.sqrt ν := by positivity
  obtain ⟨cν, hcν⟩ : ∃ cν : ℝ, cν = (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ :=
    ⟨_, rfl⟩
  have hcs := frC0Star_pos d hL
  have hcle : frC0Star d L ≤ cν := by rw [hcν]; exact frC0Star_le hL hνs' hν1
  have hcν0 : 0 < cν := lt_of_lt_of_le hcs hcle
  have hsβ1 : 1 ≤ Real.sqrt β := Real.one_le_sqrt.2 hβ1
  have hsββ : Real.sqrt β ≤ β := by
    have := mul_le_mul_of_nonneg_left hsβ1 hsβ.le
    rwa [mul_one, Real.mul_self_sqrt hβ0.le] at this
  have hJ : ((Real.sqrt β)⁻¹ * cν)⁻¹ ^ (N - 1) ≤ β ^ (N - 1) * (frC0Star d L)⁻¹ ^ (N - 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (inv_nonneg.2 (by positivity)) ?_ _
    rw [mul_inv, inv_inv]
    exact mul_le_mul hsββ (inv_anti₀ hcs hcle) (by positivity) hβ0.le
  have hJ0 : 0 ≤ ((Real.sqrt β)⁻¹ * cν)⁻¹ ^ (N - 1) := by positivity
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hE1 : Real.exp (-(β * ν / 128)) ≤ Real.exp (-(ns / 128 * β)) :=
    Real.exp_le_exp.2 (by linarith)
  have hE2 : Real.exp (-(β * ν / 2) + 2 * G) ≤ Real.exp (-(ns / 4 * β)) :=
    Real.exp_le_exp.2 (by rw [hG]; linarith)
  have hE3 : Real.exp (-(ns / 4 * β)) ≤ Real.exp (-(ns / 128 * β)) :=
    Real.exp_le_exp.2 (by have := mul_pos hns0 hβ0; linarith)
  have hE4 : ε ≤ Real.exp (-(ns * β)) := by rw [hε]; exact Real.exp_le_exp.2 (by linarith)
  have hM : (2 : ℝ) ^ (N - 1) * Real.exp (2 * (2 * cG / Real.sqrt ν) ^ 2) ≤ M0 := by
    rw [hM0]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by have := pow_le_pow_left₀ ha0 haS' 2; linarith)) (by positivity)
  have hc0' : (frC0Star d L)⁻¹ ^ (N - 1) ≤ c0 := by
    rw [hc0]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  rw [← hΓ, ← hcν, ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Γ * Real.exp (-(β * ν / 128)) * (((Real.sqrt β)⁻¹ * cν)⁻¹ ^ (N - 1) * Wc)
        ≤ Γ * Real.exp (-(ns / 128 * β)) * ((β ^ (N - 1) * (frC0Star d L)⁻¹ ^ (N - 1)) * Wc) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hE1 hΓ0) (mul_le_mul_of_nonneg_right hJ hWc0)
            (mul_nonneg hJ0 hWc0) (by positivity)
      _ ≤ Γ * Real.exp (-(ns / 128 * β)) * ((β ^ (N - 1) * c0) * Wc) := by gcongr
      _ = Γ * Wc * c0 * β ^ (N - 1) * Real.exp (-(ns / 128 * β)) := by ring
      _ ≤ 1 := B9
  · rw [hpt]
    have h1 := mul_le_mul hE2 hM (by positivity) (Real.exp_pos _).le
    linarith
  · rw [hpt]
    have h1 := mul_le_mul hE4 hM (by positivity) (Real.exp_pos _).le
    linarith
  · have e1 : Real.exp ((2 * cG / Real.sqrt ν) ^ 2) ≤ Real.exp (aS ^ 2) :=
      Real.exp_le_exp.2 (pow_le_pow_left₀ ha0 haS' 2)
    have e2 : Real.exp (-(β * ν / 128)) + Real.exp (-(β * ν / 2) + 2 * G) ≤
        2 * Real.exp (-(ns / 128 * β)) := by linarith
    calc Γ * Real.exp ((2 * cG / Real.sqrt ν) ^ 2) *
          (Real.exp (-(β * ν / 128)) + Real.exp (-(β * ν / 2) + 2 * G)) *
          (((Real.sqrt β)⁻¹ * cν)⁻¹ ^ (N - 1) * Wc)
        ≤ Γ * Real.exp (aS ^ 2) * (2 * Real.exp (-(ns / 128 * β))) *
          ((β ^ (N - 1) * (frC0Star d L)⁻¹ ^ (N - 1)) * Wc) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left e1 hΓ0) e2 (by positivity)
            (by positivity)) (mul_le_mul_of_nonneg_right hJ hWc0) (mul_nonneg hJ0 hWc0)
            (by positivity)
      _ = Γ * 2 * Wc * c0 * β ^ (N - 1) * Real.exp (-(ns / 128 * β)) := by rw [hc0]; ring
      _ ≤ η := B8

/-- **The source and the cutoff at large `β`**: the coefficient of the linear Gaussian exponent is
at most `p/8`, and `K₀^{k s₁} ≤ e`. -/
theorem frK_facts {β ν ns p cG aS θ G : ℝ} {k s₁ : ℕ} (hns : 0 < ns) (hνs : ns ≤ ν) (hβ : 0 < β)
    (hp : 0 < p) (hcG : 0 < cG) (haS : aS = 2 * cG / Real.sqrt ns)
    (haS1 : aS * p * (k * s₁) ≤ 1 / 4) (haS2 : aS ≤ p / 8)
    (hθ2 : θ ≤ 1 / (2 * p ^ 2 * k * s₁)) (hk : 1 ≤ k) (hs₁ : 1 ≤ s₁)
    (hG : G = cG * Real.sqrt β) :
    2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ ≤ p / 8 ∧
    Real.exp (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ * p + θ / 2 * p ^ 2) ^ (k * s₁) ≤
      Real.exp 1 := by
  have hν0 : 0 < ν := lt_of_lt_of_le hns hνs
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν0
  have hsq : 0 < Real.sqrt ns := Real.sqrt_pos.2 hns
  have ha : 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ = 2 * cG / Real.sqrt ν := by
    rw [hG]; field_simp
  have haS' : 2 * cG / Real.sqrt ν ≤ aS := by
    rw [haS]; exact div_le_div_of_nonneg_left (by positivity) hsq (Real.sqrt_le_sqrt hνs)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs₁R : (1 : ℝ) ≤ s₁ := by exact_mod_cast hs₁
  refine ⟨by rw [ha]; linarith, ?_⟩
  rw [← Real.exp_nat_mul, Real.exp_le_exp, ha]
  have h1 : 2 * cG / Real.sqrt ν * p ≤ aS * p := mul_le_mul_of_nonneg_right haS' hp.le
  have h2 : θ * (2 * p ^ 2 * k * s₁) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hθ2; exact hθ2
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (k : ℝ) * s₁)
  push_cast
  linarith

/-- **The weights of route FR are at most `b_*`.** -/
theorem frWeight_le {τ bs e : ℝ} {k s₁ c : ℕ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hk : 1 ≤ k)
    (hc : c ≤ s₁) (hτs : τ * s₁ = bs / 4) (hbs1 : bs ≤ 1) (he0 : 0 ≤ e) (he : e ≤ bs / 4) :
    (1 + τ ^ k) ^ c * (e + τ * c) ≤ bs := by
  have hcR : (c : ℝ) ≤ s₁ := by exact_mod_cast hc
  have hτk : τ ^ k ≤ τ := pow_le_of_le_one hτ0.le hτ1 (by omega)
  have h1 : (1 + τ ^ k) ^ c ≤ 2 := by
    calc (1 + τ ^ k) ^ c ≤ Real.exp (τ ^ k) ^ c := by
          gcongr; linarith [Real.add_one_le_exp (τ ^ k)]
      _ = Real.exp (c * τ ^ k) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 4) := by
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul hcR hτk (by positivity) (by positivity : (0 : ℝ) ≤ s₁)
          linarith
      _ ≤ 2 := exp_quarter_le_two
  have h2 : e + τ * c ≤ bs / 2 := by
    have := mul_le_mul_of_nonneg_left hcR hτ0.le
    linarith
  have h3 : 0 ≤ e + τ * c := add_nonneg he0 (by positivity)
  calc _ ≤ 2 * (bs / 2) := mul_le_mul h1 h2 h3 (by norm_num)
    _ = bs := by ring

/-! ### Assembly -/

/-- **`KfZeroInput` at fixed `κ, c₉` from the typing condition.** -/
theorem kf0FR_fixed {δ κ c₉ : ℝ} {L M : ℕ} (hd : 1 ≤ d) (hκ : 0 < κ) (hc₉ : 0 < c₉) (hL : 1 ≤ L)
    (htyp : KF0FRTyping d N L κ (M * L)) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 7 / 8 < ν * (L : ℝ) ^ 2 → ν ≤ 1 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon L ν kf →
        ∃ (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
          ObservableActivities d N L M κ c₉ δ 1 kf p ∧
          ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
            ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              partitionFunction d N ℓ β ν h g =
                Complex.exp (E ℓ + ∑ x, ∑ i, g x i * (h i : ℂ) + ∑ X, p ℓ 1 X g) := by
  obtain ⟨hs6, hθtyp⟩ := htyp
  have : NeZero (M * L) := ⟨by omega⟩
  have hs1 : 1 ≤ M * L := by omega
  /- the parameters of the block side -/
  obtain ⟨R, hR⟩ : ∃ R, R = frRr (M * L) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = frKk d (M * L) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = frS1 d (M * L) := ⟨_, rfl⟩
  have hR4 : 4 * R + 3 ≤ M * L := by rw [hR]; unfold frRr; omega
  have hk1 : 1 ≤ k := by rw [hk]; exact one_le_frKk d _
  have hs₁1 : 1 ≤ s₁ := by rw [hs₁]; exact one_le_frS1 d _
  have hkR : (1 + d) * (4 * R + 3) ^ d = k := by rw [hk, hR]; rfl
  have hs₁R : (4 * R + 3) ^ d = s₁ := by rw [hs₁, hR]; rfl
  obtain ⟨bs, hbs⟩ : ∃ bs, bs = frBs d κ (M * L) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = frTau d κ (M * L) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = frEta d κ (M * L) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = frP d N κ (M * L) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = frThetaStar d L R := ⟨_, rfl⟩
  obtain ⟨ns, hns⟩ : ∃ ns, ns = frNuStar L := ⟨_, rfl⟩
  have hns0 : 0 < ns := by rw [hns]; exact frNuStar_pos hL
  have hbs0 : 0 < bs := by rw [hbs]; exact frBs_pos d κ hs1
  have hbs1 : bs ≤ 1 := by rw [hbs]; exact frBs_le_one d hκ.le hs1
  have hτ0 : 0 < τ := by rw [hτ]; exact frTau_pos d κ hs1
  have hτ1 : τ ≤ 1 := by rw [hτ]; exact frTau_le_one d hκ.le hs1
  have hτs : τ * s₁ = bs / 4 := by rw [hτ, hs₁, hbs]; exact frTau_mul_frS1 d κ _
  have hη0 : 0 < η := by rw [hη]; exact frEta_pos d κ hs1
  have hΘ : (8 : ℝ) ^ k * Real.exp 1 * η = τ ^ (2 * k) := by
    rw [hη, hτ, hk]; exact frEta_mul d κ _
  have hpt : (2 : ℝ) ^ (N - 1) * Real.exp (-p ^ 2 / 8) = η / 4 := by
    rw [hp, hη]; exact frP_tail d N hκ.le hs1
  have hp0 : 0 < p := by rw [hp]; exact frP_pos d N hκ.le hs1
  have hθbd : θ ≤ min (1 / 4) (min (bs / (24 * p ^ 2)) (1 / (2 * p ^ 2 * k * s₁))) := by
    rw [hθ, hbs, hp, hk, hs₁, hR]; exact hθtyp
  have hθ14 : θ ≤ 1 / 4 := hθbd.trans (min_le_left _ _)
  have hθ1 : θ ≤ bs / (24 * p ^ 2) := hθbd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ2 : θ ≤ 1 / (2 * p ^ 2 * k * s₁) :=
    hθbd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hθ0 : 0 ≤ θ := by rw [hθ]; unfold frThetaStar frNuStar; positivity
  /- the source radius constant `c_G` -/
  have hkR0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs₁R0 : (0 : ℝ) < s₁ := by exact_mod_cast hs₁1
  obtain ⟨cG, hcG⟩ : ∃ cG : ℝ, cG = min (bs * Real.sqrt ns / (96 * p))
      (min (Real.sqrt ns / (8 * p * k * s₁)) (p * Real.sqrt ns / 16)) := ⟨_, rfl⟩
  obtain ⟨hcG0, haS1, haS2, hGρ⟩ := frCG_facts hp0 hbs0 hns0 hkR0 hs₁R0 hcG
  obtain ⟨aS, haS⟩ : ∃ aS : ℝ, aS = 2 * cG / Real.sqrt ns := ⟨_, rfl⟩
  rw [← haS] at haS1 haS2
  /- the constants of the conditions on `β` -/
  obtain ⟨κ0, hκ0⟩ : ∃ κ0, κ0 = kf0K0 d := ⟨_, rfl⟩
  obtain ⟨κ1, hκ1⟩ : ∃ κ1, κ1 = κ + κ0 + 5 / 2 := ⟨_, rfl⟩
  have hκ0' : Real.log 4 + 1 ≤ κ0 := by rw [hκ0]; exact kf0K0_ge_log d
  have hκ00 : 0 ≤ κ0 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  have hH0v : (1 + d) * 3 ^ d * ((M * L : ℕ) : ℝ) ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d) =
      1 / 16 := by
    rw [hbs, hκ1, hκ0]; exact frH0_eq d κ hs1
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, M0 = 2 ^ (N - 1) * Real.exp (2 * aS ^ 2) := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = (2 * Real.pi) ^ (-((N - 1 : ℕ) : ℝ) / 2) := ⟨_, rfl⟩
  obtain ⟨Wc, hWc⟩ : ∃ Wc : ℝ,
      Wc = ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ).toReal := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = (frC0Star d L)⁻¹ ^ (N - 1) * Real.exp (aS ^ 2) := ⟨_, rfl⟩
  have htgt0 : 0 < c₉ / 2 * (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  obtain ⟨β₀, hβ₀1, hβ₀⟩ := frBeta_large (p := p) (ns := ns) (bs := bs) (cG := cG) (M0 := M0)
    (η := η) (Γ := Γ) (Wc := Wc) (c0 := c0)
    (α := 64 * Real.exp 1 * ((1 + d) * 3 ^ d * ((M * L : ℕ) : ℝ) ^ d * bs *
      Real.exp ((κ0 + κ1) * 3 ^ d)) * Real.exp (-(2 * κ0)))
    (N - 1) hns0 hbs0 hcG0 hη0 htgt0
  refine ⟨β₀, fun β hβ ν hνL hν1 h hh kf _ => ?_⟩
  obtain ⟨-, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11⟩ := hβ₀ β hβ
  /- the couplings -/
  have hβ1 : 1 ≤ β := hβ₀1.trans hβ
  have hβ0 : 0 < β := by linarith
  have hνs' : frNuStar L ≤ ν := frNuStar_le_of hL hνL
  have hνs : ns ≤ ν := by rw [hns]; exact hνs'
  have hν0 : 0 < ν := lt_of_lt_of_le hns0 hνs
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = cG * Real.sqrt β := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = Real.exp (-(β * ν)) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact Real.exp_pos _
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  /- the ordinary and heavy bounds -/
  obtain ⟨hρ2, hZ, hEps⟩ :=
    frOrd_facts (d := d) hns0 hνs hβ0 hp0 hcG0 hbs1 hθ1 hGρ B2 B3 B4 hρ hG
  have hfr : Module.finrank ℝ (perp h) = N - 1 := by
    have := Balaban.LargeField.finrank_perp h hh; omega
  have hWc0 : 0 ≤ Wc := by rw [hWc]; exact ENNReal.toReal_nonneg
  obtain ⟨hJord, hη1, hη2, hη3⟩ := frHeavy_facts (d := d) (N := N) hL hns hνs hν1 hβ1 hcG0 haS
    hpt hM0 hΓ hWc0 hc0 hG hε B5 B6 B7 B8 B9
  obtain ⟨hA, hK⟩ := frK_facts hns0 hνs hβ0 hp0 hcG0 haS haS1 haS2 hθ2 hk1 hs₁1 hG
  have hWc' : ∫⁻ v, ENNReal.ofReal (LargeField.chartWeight h v) ≤ ENNReal.ofReal Wc := by
    rw [lintegral_chartWeight_eq h hh, hWc, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact measure_mono (Set.subset_univ _)
  have hΘ1 : (8 : ℝ) ^ k * Real.exp 1 * η ≤ 1 := by
    rw [hΘ]; exact pow_le_one₀ hτ0.le hτ1
  have hsqΘ : Real.sqrt ((8 : ℝ) ^ k * Real.exp 1 * η) = τ ^ k := by
    rw [hΘ, pow_mul', Real.sqrt_sq (pow_nonneg hτ0.le k)]
  have hΘr : ((8 : ℝ) ^ k * Real.exp 1 * η) ^ ((1 : ℝ) / (2 * k)) = τ := by
    rw [hΘ, ← Real.rpow_natCast, ← Real.rpow_mul hτ0.le]
    have : ((2 * k : ℕ) : ℝ) * (1 / (2 * (k : ℝ))) = 1 := by push_cast; field_simp
    rw [this, Real.rpow_one]
  /- the weights -/
  have hb0 : ∀ (m : ℕ) [NeZero m] (t : FRTerm d (M * L * m)),
      0 ≤ (1 + Real.sqrt ((8 : ℝ) ^ k * Real.exp 1 * η)) ^ (frSupp R t).card *
        (frEps β ν ρ G θ p t +
          ((8 : ℝ) ^ k * Real.exp 1 * η) ^ ((1 : ℝ) / (2 * k)) * (frSupp R t).card) := by
    intro m _ t
    rw [hsqΘ, hΘr]
    exact mul_nonneg (by positivity)
      (add_nonneg (frEps_nonneg (p := p) hβ0.le hν0.le hρ0 hG0 hθ0 t) (by positivity))
  have hbs' : ∀ (m : ℕ) [NeZero m] (t : FRTerm d (M * L * m)),
      (1 + Real.sqrt ((8 : ℝ) ^ k * Real.exp 1 * η)) ^ (frSupp R t).card *
        (frEps β ν ρ G θ p t +
          ((8 : ℝ) ^ k * Real.exp 1 * η) ^ ((1 : ℝ) / (2 * k)) * (frSupp R t).card) ≤ bs := by
    intro m _ t
    rw [hsqΘ, hΘr]
    exact frWeight_le (s₁ := s₁) hτ0 hτ1 hk1 (hs₁R ▸ card_frSupp_le R t) hτs hbs1
      (frEps_nonneg (p := p) hβ0.le hν0.le hρ0 hG0 hθ0 t) (hEps t)
  have hsite : ∀ (m : ℕ) [NeZero m] (g : Torus d (M * L * m) → Fin N → ℂ),
      ∑ x, ∑ i, ‖g x i‖ < G → ∀ C : Finset (FRTerm d (M * L * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε) ∧
      ‖∫ ω, ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1) ∂(Measure.pi fun _ => frSiteMeasure h ε)‖ ≤
        ∏ t ∈ C, ((1 + Real.sqrt ((8 : ℝ) ^ k * Real.exp 1 * η)) ^ (frSupp R t).card *
          (frEps β ν ρ G θ p t +
            ((8 : ℝ) ^ k * Real.exp 1 * η) ^ ((1 : ℝ) / (2 * k)) * (frSupp R t).card)) := by
    intro m _ g hg C
    have hgx : ∀ x, ∑ i, ‖g x i‖ ≤ G := fun x =>
      (Finset.single_le_sum (f := fun y => ∑ i, ‖g y i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x)).trans hg.le
    exact norm_integral_prod_frF_le (k := k) (s₁ := s₁) h hh hβ0 hν0 hε0 hp0.le R g hgx
      (fun x => by rw [hθ]; exact frQ_rowAbs_le_star hd hL hνs' hν1 R x) hθ0 hθ14 hA le_rfl hWc'
      (by rw [hfr]; exact hJord) (by rw [hfr]; exact hη1) (by rw [hfr]; exact hη2)
      (by rw [hfr]; exact hη3) (le_of_eq hρ.symm) hρ2 hZ hk1 C
      (fun x => hkR ▸ card_filter_mem_frSupp_le R x C) (fun x => hs₁R ▸ card_frSupp_le R _) hK
      hΘ1
  /- the activities -/
  obtain ⟨hobs, hid⟩ := kf0FR_observable (L := L) (M := M) (κ := κ) (c₉ := c₉) (δ := δ) (R := R)
    (G := G) (bs := bs) (κ0 := κ0) (κ1 := κ1) hd hs6 hR4 h hh hβ0 hν0 hε0
    (fun m _ x => (frQ_rowAbs_le_star hd hL hνs' hν1 R x).trans (by rw [← hθ]; linarith))
    (by rw [hG]; exact B10)
    (fun m _ t => (1 + Real.sqrt ((8 : ℝ) ^ k * Real.exp 1 * η)) ^ (frSupp R t).card *
      (frEps β ν ρ G θ p t +
        ((8 : ℝ) ^ k * Real.exp 1 * η) ^ ((1 : ℝ) / (2 * k)) * (frSupp R t).card))
    hb0 hbs' hsite (by rw [hbs]; exact frSmall_le d hκ.le hs1)
    (by rw [hκ0]; exact kf0K0_sq d hd) hκ0' hκ.le (by rw [hκ1]; linarith)
    (by rw [hH0v]; have := Real.exp_le_one_iff.2 (neg_nonpos.2 hκ00); linarith)
    (by rw [hG]; exact B11) hc₉.le kf
  exact ⟨_, _, hobs, hid⟩

/-- **`KfZeroInput` by route FR.** If for every `κ, c₉ > 0` the block side `M L` of the typing
`T κ c₉` is at least `kf0FRs0 d N L κ` (a lower bound depending on `d, N, L, κ` only, compatible
with `M = L^n`, `kf0FRs0_le_pow`), the case `k_f = 0` holds. -/
theorem kfZeroInput_of_typing (δ : ℝ) (T : ℝ → ℝ → LargeField.Typing) (hd : 1 ≤ d)
    (hT : ∀ κ c₉ : ℝ, 0 < κ → 0 < c₉ → kf0FRs0 d N (T κ c₉).L κ ≤ (T κ c₉).M * (T κ c₉).L) :
    KfZeroInput d N δ T := by
  intro κ hκ c₉ hc₉
  have hs := hT κ c₉ hκ hc₉
  have h6 := (six_le_kf0FRs0 d N (T κ c₉).L κ).trans hs
  have hL : 1 ≤ (T κ c₉).L := by
    rcases Nat.eq_zero_or_pos (T κ c₉).L with h0 | h0
    · rw [h0, Nat.mul_zero] at h6; omega
    · exact h0
  exact kf0FR_fixed hd hκ hc₉ hL (kF0FRTyping_of_le hd hL hκ.le hs)

end

end Balaban.RootFSpine
