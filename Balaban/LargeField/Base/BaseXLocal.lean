/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXSqrt
public import Balaban.Localization.DecoupledCovClose

/-!
# Locality of the first step's shifted covariance and of its square root

Weighted comparison and exact core agreement of the shifted covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of the first step, uniformly in `x ≥ 0`, and of its Stieltjes
square root.  Everything is an application of the step's weighted closeness of `Z = Ĝ - Π`
(`vecM_decZ_sub_le_cover`) at `x' = 0` and mass `ν + x`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Entry

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- An entry of an operator that is bounded in the weighted block norm decays with the weight. -/
theorem entry_sq_mul_le_of_vecM (M : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) {K ε : ℝ}
    (r : Balaban.Localization.CTorus d L N₁ m₁ (k + 1) → ℝ) (hK : 0 ≤ K)
    (h : ∀ f : G.Ω 1 × Fin N → ℂ, vecM G ε r (M *ᵥ f) ≤ K * vecSrc G 0 (fun _ => 0) f)
    (y z : G.Ω 1 × Fin N) :
    ‖M y z‖ ^ 2 * Real.exp (ε * r y.1) ^ 2 ≤ K * (((L : ℝ) ^ (k + 1)) ^ 2) ^ 2 := by
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 := h (Pi.single z 1)
  have h2 := (sqNorm_le_vecSrc_zero (N := N) (H := G) hL1 (Pi.single z 1 : G.Ω 1 × Fin N → ℂ)).2
  rw [sqNorm_single] at h2
  set u : G.Ω 1 × Fin N → ℂ := M *ᵥ (Pi.single z 1 : G.Ω 1 × Fin N → ℂ) with hu
  have hent : u y = M y z := mulVec_single_entry M y z
  have hsp := spacing_pos (G := G) (x := y.1)
  have hspl := spacing_le (G := G) y.1.2
  have hv : ‖u y‖ ^ 2 ≤ vn (svec G u y.1) ^ 2 := by
    rw [vn_sq]
    have := Finset.single_le_sum (f := fun i => ‖svec G u y.1 i‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ y.2)
    refine le_trans (le_of_eq ?_) this
    simp only [svec]
    rw [zeroExt_mem' _ y.1.2]
  have hw : invSqSpacing G y.1 * (Real.exp (ε * r y.1) * vn (svec G u y.1)) ^ 2 ≤ vecM G ε r u := by
    unfold vecM wsq
    exact Finset.single_le_sum (f := fun x => invSqSpacing G x *
      (Real.exp (ε * r x) * vn (svec G u x)) ^ 2)
      (fun x _ => mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)) (Finset.mem_univ (y.1 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))))
  rw [invSqSpacing_eq G y.1.2] at hw
  have hsq : 0 < G.spacing y.1 ^ 2 := by positivity
  have h3 : ‖u y‖ ^ 2 * Real.exp (ε * r y.1) ^ 2 ≤
      G.spacing y.1 ^ 2 * (K * (((L : ℝ) ^ (k + 1)) ^ 2)) := by
    have e1 : ‖u y‖ ^ 2 * Real.exp (ε * r y.1) ^ 2 ≤
        (Real.exp (ε * r y.1) * vn (svec G u y.1)) ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    have e2 : (Real.exp (ε * r y.1) * vn (svec G u y.1)) ^ 2 ≤
        G.spacing y.1 ^ 2 * (K * (((L : ℝ) ^ (k + 1)) ^ 2)) := by
      have := hw.trans (h1.trans (mul_le_mul_of_nonneg_left h2 hK))
      rw [mul_one] at this
      rw [inv_mul_le_iff₀ hsq] at this
      exact this
    exact e1.trans e2
  rw [hent] at h3
  refine h3.trans ?_
  have : G.spacing y.1 ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 := pow_le_pow_left₀ hsp.le hspl 2
  calc _ ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * (K * (((L : ℝ) ^ (k + 1)) ^ 2)) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by ring

end Entry

section Compare

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx x : ℝ}

theorem zCloseConst_nonneg (d L : ℕ) : 0 ≤ zCloseConst d L := by
  unfold zCloseConst closeConstX gradCloseConstX gradStarConstX valConstX
  have := commXConst_nonneg d L
  positivity

/-- The weighted closeness of `Z_s = Ĝ_{0,s} - Π_{0,s}` (at mass `ν + x`) to `Z_1`, entrywise. -/
theorem decZ_sub_one_entry {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (T : ℝ) (y z : G.Ω 1 × Fin N) :
    ‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ ≤
      Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2) *
        Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) := by
  have D : Dec2.XData (coverOf G) G a aT (ν + x) 0 α κ s Cx := ⟨S, hCx, hα, le_rfl, hκ, hM, hs⟩
  have hd : 0 < d := by have := S.hd; omega
  have hε0 : 0 ≤ xAgmonRate d L := (xAgmonRate_pos hd S.hL).le
  have hK : 0 ≤ zCloseConst d L * Real.exp (N0 d L * κ) ^ 2 :=
    mul_nonneg (zCloseConst_nonneg d L) (sq_nonneg _)
  have h := entry_sq_mul_le_of_vecM (G := G) (N := N)
    (decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) (ε := xAgmonRate d L)
    (truncSetDistR G W T) hK
    (fun f => vecM_decZ_sub_le_cover D hW T hε0 le_rfl hφ hδ hsm f) y z
  set E := Real.exp (xAgmonRate d L * truncSetDistR G W T y.1) with hE
  have hEp : 0 < E := Real.exp_pos _
  have hneg : Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) = E⁻¹ := Real.exp_neg _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h2 : (‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ * E) ^ 2 ≤
      (Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hK]
    calc _ = ‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ ^ 2 *
          E ^ 2 := by ring
      _ ≤ _ := h
      _ = _ := by ring
  have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
  have h4 := h3.2
  have key : ‖(decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z‖ ≤
      Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2) * E⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hEp]
    exact h4
  calc _ ≤ _ := key
    _ = _ := by rw [hneg]

/-- The shifted covariance is `(1 + x)⁻¹ P_e` plus `Z`. -/
theorem baseCovX_eq_add_decZ {α : G.Ω 1 → ℂ} {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} :
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) =
      (1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) + decZ G a aT 0 (ν + x) α s φ :=
  add_sub_assoc _ _ _

/-- **Weighted comparison of the shifted covariance, uniformly in `x ≥ 0`.**  If two parameter
families `s`, `s'` on the discs `‖s_P‖ ≤ e^κ` are `1` on every cube whose interaction cube is not
inside `W`, the entries of the shifted covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` differ by
`B e^{-γ r(y)}`, `r` the path distance from `y` to `W` truncated at any `T`, `γ = xAgmonRate d L`.
The constant `B` depends only on `d, L, κ`; the bound is uniform in `x ≥ 0`, `ν`, `a`, `aT`, `G`. -/
theorem baseCovX_sub_decay {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W)
    (hW' : ∀ z ∈ cubeIdx G, sProd G s' z ≠ 1 → intBox z ⊆ W)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (T : ℝ) (y z : G.Ω 1 × Fin N) :
    ‖((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ) y z -
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) +
          liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s') -
          Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s' φ) y z‖ ≤
      2 * (Real.sqrt (zCloseConst d L * Real.exp (N0 d L * κ) ^ 2) * ((L : ℝ) ^ 2)) *
        Real.exp (-(xAgmonRate d L * truncSetDistR G W T y.1)) := by
  rw [baseCovX_eq_add_decZ, baseCovX_eq_add_decZ]
  have h1 := decZ_sub_one_entry S hCx hκ hM hδ hsm hα hs hW hφ T y z
  have h2 := decZ_sub_one_entry S hCx hκ hM hδ hsm hα hs' hW' hφ T y z
  have e : ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) + decZ G a aT 0 (ν + x) α s φ) y z -
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ) + decZ G a aT 0 (ν + x) α s' φ) y z =
      (decZ G a aT 0 (ν + x) α s φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z -
        (decZ G a aT 0 (ν + x) α s' φ - decZ G a aT 0 (ν + x) α (fun _ => 1) φ) y z := by
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

end Compare

end Balaban.LargeField.Base
