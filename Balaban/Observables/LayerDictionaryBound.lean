/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerSums

/-!
# Lemma 2.2, the bound on the terms `𝓜^{(j)}(x, X)` (OBSERVABLES.md §2.3)

With a localized family `φ_j(x, X; ψ, h)` for the background (P3: `|φ_j(x, X)| ≤ C_φ e^{-κ d_j(X)}`,
the hypothesis `hφ`; the family is not part of Def-6, which has no localization of `φ_j`), the terms
`𝓜^{(j)}(x, X) = β_{j-1}^{-1/2} (M^{(j)}(x, X) - μ_j(x) φ_j(x, X))` satisfy

  `|𝓜^{(j)}(x, X; ψ, h)| ≤ β^{-1/4} ξ_j^{(d-2)/2 + γ - α₁} e^{-κ d_j(X)}`,  `ξ_j = L^{-j}`,

the (H.7) bound with `c₉ = β^{-1/4}`, if `ρ₀ ≥ γ - α₁` (E7) and `β` is large
(`mscript_bound`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

omit [NeZero L] [NeZero N₁] in
theorem vn_smul (c : ℂ) (v : Fin N → ℂ) : vn (c • v) = ‖c‖ * vn v := by
  unfold vn
  show ‖(WithLp.toLp 2 (c • v) : EuclideanSpace ℂ (Fin N))‖ = _
  rw [show (WithLp.toLp 2 (c • v) : EuclideanSpace ℂ (Fin N)) =
    c • (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) from rfl, norm_smul]

omit [NeZero L] [NeZero N₁] in
theorem vn_sub_le (v w : Fin N → ℂ) : vn (v - w) ≤ vn v + vn w := by
  unfold vn
  exact norm_sub_le (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 w)

/-- **Lemma 2.2, the bound on `𝓜^{(j)}(x, X)`.**  Let `phiX` be a localized background with
`vn (phiX j x X ψ h) ≤ C_φ e^{-κ d_j(X)}` on the domains; `ρ₀ ≥ γ - α₁`; and
`√e L^{(d-2)/2} (1 + C_φ) β^{-3/4+ρ₁} ≤ 1`.  Then the terms
`β_{j-1}^{-1/2} (M^{(j)}(x, X) - μ_j(x) φ_j(x, X))` are bounded by
`β^{-1/4} (L^{-j})^{(d-2)/2+γ-α₁} e^{-κ d_j(X)}`. -/
theorem mscript_bound (hL : 2 ≤ L) (hd : 2 ≤ d) {P : Consts} (hP : P.Admissible d L)
    {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
    {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
    (hc : CoeffBounds d L k P β ν a) (hO : IsObs P Q β ν a Tm Ot Gker) (hβ0 : 0 < β 0)
    (hρ₀ : P.γ - P.α₁ ≤ Q.ρ₀) {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (phiX : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Fin N → ℂ)
    (hφ : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      vn (phiX j x X Ψ h) ≤ Cφ * Real.exp (-P.κ * sizeJ P.m₀ j X))
    (hsmall : Real.sqrt (Real.exp 1) * (L : ℝ) ^ (((d : ℝ) - 2) / 2) * (1 + Cφ) *
      (β 0) ^ (-(3 / 4 : ℝ) + Q.ρ₁) ≤ 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k)
    (X : Set (CTorus d L N₁ m₁ k)) (hX : IsPolyDom P.m₀ j X) (hxX : x ∈ X)
    (Ψ h : Fld d L N₁ m₁ k N)
    (hdom : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h) :
    vn (((Real.sqrt (β (j - 1)))⁻¹ : ℂ) • (Ot.M j x X Ψ h - (Ot.μ j x : ℂ) • phiX j x X Ψ h)) ≤
      (β 0) ^ (-(1 / 4 : ℝ)) * (((L : ℝ) ^ j)⁻¹) ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hL0 : 0 < (L : ℝ) := by linarith
  set E := Real.exp (-P.κ * sizeJ P.m₀ j X) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set B := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := Real.rpow_nonneg hβ0.le _
    have : 0 ≤ (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := Real.rpow_nonneg hL0.le _
    positivity
  -- the vector part
  have hM := hO.boundM j hj1 hjk x X hX hxX Ψ h hdom
  have hμ := hO.μ_bound j hj1 hjk x
  have hφ' := hφ j hj1 hjk x X hX hxX Ψ h hdom
  have hvec : vn (Ot.M j x X Ψ h - (Ot.μ j x : ℂ) • phiX j x X Ψ h) ≤ B * (1 + Cφ) * E := by
    calc vn (Ot.M j x X Ψ h - (Ot.μ j x : ℂ) • phiX j x X Ψ h)
        ≤ vn (Ot.M j x X Ψ h) + vn ((Ot.μ j x : ℂ) • phiX j x X Ψ h) := vn_sub_le _ _
      _ = vn (Ot.M j x X Ψ h) + |Ot.μ j x| * vn (phiX j x X Ψ h) := by
          rw [vn_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ B * E + B * (Cφ * E) :=
          add_le_add hM (mul_le_mul hμ hφ' (vn_nonneg _) hB0)
      _ = B * (1 + Cφ) * E := by ring
  -- the coupling
  obtain ⟨hpos, hlow⟩ := beta_pos_lower hL hP hc hβ0 (n := j - 1) (by omega)
  have hLp : (0 : ℝ) < (L : ℝ) ^ ((j - 1) * (d - 2)) := by positivity
  have hsq : Real.sqrt (β 0) * Real.sqrt ((L : ℝ) ^ ((j - 1) * (d - 2))) /
      Real.sqrt (Real.exp 1) ≤ Real.sqrt (β (j - 1)) := by
    rw [← Real.sqrt_mul hβ0.le, ← Real.sqrt_div (by positivity)]
    exact Real.sqrt_le_sqrt hlow
  have hsq0 : 0 < Real.sqrt (β 0) * Real.sqrt ((L : ℝ) ^ ((j - 1) * (d - 2))) /
      Real.sqrt (Real.exp 1) := by
    have := Real.sqrt_pos.2 hβ0
    have := Real.sqrt_pos.2 hLp
    have := Real.sqrt_pos.2 (Real.exp_pos 1)
    positivity
  have hsj : (Real.sqrt (β (j - 1)))⁻¹ ≤ Real.sqrt (Real.exp 1) / Real.sqrt (β 0) *
      (Real.sqrt ((L : ℝ) ^ ((j - 1) * (d - 2))))⁻¹ := by
    calc (Real.sqrt (β (j - 1)))⁻¹ ≤ (Real.sqrt (β 0) * Real.sqrt ((L : ℝ) ^ ((j - 1) * (d - 2))) /
          Real.sqrt (Real.exp 1))⁻¹ := inv_anti₀ hsq0 hsq
      _ = _ := by
          have := Real.sqrt_pos.2 hβ0
          have := Real.sqrt_pos.2 hLp
          have := Real.sqrt_pos.2 (Real.exp_pos 1)
          field_simp
  -- exponent algebra
  set ξ : ℝ := ((L : ℝ) ^ j)⁻¹ with hξ
  have hξ0 : 0 < ξ := by positivity
  have hξ1 : ξ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hLr.le)
  have hxi : ∀ t : ℝ, ξ ^ t = (L : ℝ) ^ (-((j : ℝ) * t)) := by
    intro t
    rw [hξ, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      ← Real.rpow_neg hL0.le]
  have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by push_cast [Nat.cast_sub hd]; ring
  have hLpow : (Real.sqrt ((L : ℝ) ^ ((j - 1) * (d - 2))))⁻¹ =
      (L : ℝ) ^ (((d : ℝ) - 2) / 2) * ξ ^ (((d : ℝ) - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (L : ℝ) ((j - 1) * (d - 2)),
      ← Real.rpow_mul hL0.le, ← Real.rpow_neg hL0.le, hxi, ← Real.rpow_add hL0]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    push_cast [Nat.add_sub_cancel, hd2]
    ring
  have hρL : (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) = ξ ^ Q.ρ₀ := (hxi _).symm
  have hsβ : (Real.sqrt (β 0))⁻¹ * (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) =
      (β 0) ^ (-(3 / 4 : ℝ) + Q.ρ₁) * (β 0) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hβ0.le, ← Real.rpow_add hβ0, ← Real.rpow_add hβ0]
    congr 1; ring
  have hξρ : ξ ^ Q.ρ₀ ≤ ξ ^ (P.γ - P.α₁) :=
    Real.rpow_le_rpow_of_exponent_ge hξ0 hξ1 hρ₀
  have hξadd : ξ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) =
      ξ ^ (((d : ℝ) - 2) / 2) * ξ ^ (P.γ - P.α₁) := by
    rw [← Real.rpow_add hξ0]; congr 1; ring
  have hc0 : 0 ≤ Real.sqrt (Real.exp 1) * (L : ℝ) ^ (((d : ℝ) - 2) / 2) * (1 + Cφ) *
      (β 0) ^ (-(3 / 4 : ℝ) + Q.ρ₁) := by
    have := Real.rpow_nonneg hβ0.le (-(3 / 4 : ℝ) + Q.ρ₁)
    have := Real.rpow_nonneg hL0.le (((d : ℝ) - 2) / 2)
    positivity
  have hnorm : ‖(((Real.sqrt (β (j - 1)))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt (β (j - 1)))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have hxe : 0 ≤ ξ ^ (((d : ℝ) - 2) / 2) := Real.rpow_nonneg hξ0.le _
  calc vn (((Real.sqrt (β (j - 1)))⁻¹ : ℂ) • (Ot.M j x X Ψ h - (Ot.μ j x : ℂ) • phiX j x X Ψ h))
      = (Real.sqrt (β (j - 1)))⁻¹ * vn (Ot.M j x X Ψ h - (Ot.μ j x : ℂ) • phiX j x X Ψ h) := by
        rw [vn_smul]; push_cast at hnorm ⊢; rw [hnorm]
    _ ≤ (Real.sqrt (Real.exp 1) / Real.sqrt (β 0) *
          (Real.sqrt ((L : ℝ) ^ ((j - 1) * (d - 2))))⁻¹) * (B * (1 + Cφ) * E) :=
        mul_le_mul hsj hvec (vn_nonneg _) (by positivity)
    _ = (Real.sqrt (Real.exp 1) * (L : ℝ) ^ (((d : ℝ) - 2) / 2) * (1 + Cφ) *
          (β 0) ^ (-(3 / 4 : ℝ) + Q.ρ₁)) * ((β 0) ^ (-(1 / 4 : ℝ)) *
          (ξ ^ (((d : ℝ) - 2) / 2) * ξ ^ Q.ρ₀) * E) := by
        rw [hLpow, hB, hρL, div_eq_mul_inv]
        calc _ = (Real.sqrt (Real.exp 1) * (L : ℝ) ^ (((d : ℝ) - 2) / 2) * (1 + Cφ)) *
              ((Real.sqrt (β 0))⁻¹ * (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁)) *
              (ξ ^ (((d : ℝ) - 2) / 2) * ξ ^ Q.ρ₀ * E) := by ring
          _ = _ := by rw [hsβ]; ring
    _ ≤ 1 * ((β 0) ^ (-(1 / 4 : ℝ)) * (ξ ^ (((d : ℝ) - 2) / 2) * ξ ^ (P.γ - P.α₁)) * E) := by
        refine mul_le_mul hsmall ?_ (by positivity) zero_le_one
        have := Real.rpow_nonneg hβ0.le (-(1 / 4 : ℝ))
        gcongr
    _ = _ := by rw [one_mul, hξadd]

end Balaban.Observables