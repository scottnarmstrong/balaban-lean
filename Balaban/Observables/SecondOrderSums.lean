/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.FirstOrderBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The second-order step of OBSERVABLES.md §3.6: the sums over scales

The rows `R₂^{i,k+1}`, `R₂^{k+1,k+1}`, `R₃^{k+1,k+1}` are sums over scales `j` (and `i`) of terms
with the bounds of the table of §3.6 (P9 (3.30), (3.39), (3.41)), `ξ_j = L^{-j}`, `η = L^{-k}`:

* `R2old_total`: `x_j ≤ K β^{-1+ρ₁+ρ₂} ξ_j^{ρ₀-D/2+γ} η^{D/2-Dρ₂}` for `i ≤ j ≤ k` sums to
  `≤ K L^θ/(L^θ-1) β^{-1+ρ₁+ρ₂} ξ_i^θ η^{ρ₀}`, `θ = γ-Dρ₂` (E2), (E4);
* `R2new_total`: `x_j ≤ K β^{-1+ρ₁+mρ₂} ξ_j^{ρ₀+γ-1} η^{1-mDρ₂}`, `m ≤ 2`, `1 ≤ j ≤ k`, sums to
  `≤ K L^{ρ₀}/(L^{θ}-1) β^{-1+ρ₁+mρ₂} ξ_{k+1}^{ρ₀}`, `θ = γ-mDρ₂` (E3), (E4) (`m = 2` is
  `R₂^{k+1,k+1}`, `m = 1` is T2);
* `R3_total`: the double sum of `x_{ij} ≤ K β^{-2+2ρ₁+2ρ₂} ξ_i^{ρ₀+γ-1} ξ_j^{ρ₀+γ-1} η^{2-2Dρ₂}`.
-/

@[expose] public section

namespace Balaban.Observables

open Real

/-- `ξ^a η^b ≤ ξ^{a+b-c} η^c` for `0 < η ≤ ξ` and `c ≤ b`: part of `η^b` is traded for `ξ`. -/
theorem xi_eta_split_gen {ξj η a b c : ℝ} (hξj : 0 < ξj) (hη : 0 < η) (hηξ : η ≤ ξj)
    (hcb : c ≤ b) : ξj ^ a * η ^ b ≤ ξj ^ (a + b - c) * η ^ c := by
  have e1 : η ^ b = η ^ (b - c) * η ^ c := by
    rw [← Real.rpow_add hη]; congr 1; ring
  have h2 : η ^ (b - c) ≤ ξj ^ (b - c) := Real.rpow_le_rpow hη.le hηξ (by linarith)
  have e3 : ξj ^ a * ξj ^ (b - c) = ξj ^ (a + b - c) := by
    rw [← Real.rpow_add hξj]; congr 1; ring
  rw [e1, ← e3]
  have h4 : 0 ≤ η ^ c := Real.rpow_nonneg hη.le _
  have h5 : 0 ≤ ξj ^ a := Real.rpow_nonneg hξj.le _
  calc ξj ^ a * (η ^ (b - c) * η ^ c) = ξj ^ a * η ^ (b - c) * η ^ c := by ring
    _ ≤ ξj ^ a * ξj ^ (b - c) * η ^ c := by gcongr

/-- The geometric tail `∑_{j=i}^k (L^{-j})^θ ≤ (L^{-i})^θ L^θ/(L^θ-1)` for `L ≥ 2`, `θ > 0`. -/
theorem sum_xi_pow_tail_le {L θ : ℝ} (hL : 2 ≤ L) (hθ : 0 < θ) (i k : ℕ) :
    ∑ j ∈ Finset.Icc i k, (((L ^ j)⁻¹ : ℝ)) ^ θ ≤
      (((L ^ i)⁻¹ : ℝ)) ^ θ * (L ^ θ / (L ^ θ - 1)) := by
  have hLp : 0 < L := by linarith
  have hLθ : 1 < L ^ θ := Real.one_lt_rpow (by linarith) hθ
  set q : ℝ := (L ^ θ)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hLθ
  have hterm : ∀ j : ℕ, (((L ^ j)⁻¹ : ℝ)) ^ θ = q ^ j := by
    intro j
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hLp.le,
      mul_comm, Real.rpow_mul hLp.le, Real.rpow_natCast, hq, inv_pow]
  simp_rw [hterm]
  have := geom_sum_Ico_le_of_lt_one hq0 hq1 (m := i) (n := k + 1)
  rw [show Finset.Icc i k = Finset.Ico i (k + 1) from by ext; simp]
  refine this.trans (le_of_eq ?_)
  have hd : L ^ θ - 1 ≠ 0 := by linarith
  have hd' : L ^ θ ≠ 0 := by linarith
  rw [hq]; field_simp

section Sums

variable {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ}

theorem xi_le_one_of_pow {L : ℝ} (hL : 2 ≤ L) (j : ℕ) : ((L ^ j)⁻¹ : ℝ) ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))

/-- **`R₂^{i,k+1}`, `i ≤ k`** (P9 (3.30)): the sum over `i ≤ j ≤ k` of terms
`K β^{-1+ρ₁+ρ₂} ξ_j^{ρ₀-D/2+γ} η^{D/2-Dρ₂}`.  Uses (E2), (E4). -/
theorem R2old_total (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k i : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ)) (xs : ℕ → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hj : ∀ j ∈ Finset.Icc i k, xs j ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ - ((d : ℝ) - 2) / 2 + γ) *
        S.η ^ (((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂)) :
    ∑ j ∈ Finset.Icc i k, xs j ≤
      (K * (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1))) *
        S.β ^ (-1 + ρ₁ + ρ₂) * (((S.L ^ i)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) *
          S.η ^ ρ₀ := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hη0 := S.hη0
  have hθ : 0 < γ - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E4; have := hE.ρ₂_pos; nlinarith
  have hcb : ρ₀ ≤ ((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E2; have := hE.ρ₂_pos; nlinarith
  set θ := γ - ((d : ℝ) - 2) * ρ₂ with hθdef
  have hterm : ∀ j ∈ Finset.Icc i k, xs j ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) *
      ((((S.L ^ j)⁻¹ : ℝ)) ^ θ * S.η ^ ρ₀) := by
    intro j hjm
    have hj' := Finset.mem_Icc.1 hjm
    have hξj : 0 < ((S.L ^ j)⁻¹ : ℝ) := by have := S.L_pos; positivity
    have hηξ : S.η ≤ ((S.L ^ j)⁻¹ : ℝ) := by
      rw [hηk]
      exact inv_anti₀ (by have := S.L_pos; positivity)
        (pow_le_pow_right₀ (by linarith [S.hL]) hj'.2)
    have h1 := xi_eta_split_gen (a := ρ₀ - ((d : ℝ) - 2) / 2 + γ)
      (b := ((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂) hξj hη0 hηξ hcb
    have e : ρ₀ - ((d : ℝ) - 2) / 2 + γ + (((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂) - ρ₀ = θ := by
      rw [hθdef]; ring
    rw [e] at h1
    refine (hj j hjm).trans ?_
    have hpre : 0 ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) := by positivity
    calc _ = K * S.β ^ (-1 + ρ₁ + ρ₂) * ((((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ - ((d : ℝ) - 2) / 2 + γ) *
          S.η ^ (((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hpre
  calc ∑ j ∈ Finset.Icc i k, xs j
      ≤ ∑ j ∈ Finset.Icc i k, K * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
          (((S.L ^ j)⁻¹ : ℝ)) ^ θ :=
        Finset.sum_le_sum (fun j hjm => (hterm j hjm).trans (le_of_eq (by ring)))
    _ = K * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
          ∑ j ∈ Finset.Icc i k, (((S.L ^ j)⁻¹ : ℝ)) ^ θ := (Finset.mul_sum _ _ _).symm
    _ ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
          ((((S.L ^ i)⁻¹ : ℝ)) ^ θ * (S.L ^ θ / (S.L ^ θ - 1))) := by
        have h0 : 0 ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ := by positivity
        exact mul_le_mul_of_nonneg_left (sum_xi_pow_tail_le S.hL hθ i k) h0
    _ = _ := by ring

/-- **`R₂^{i,k+1}`, closed** (E1)-(E4): `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` once
`2 K (L^θ/(L^θ-1)) L^{ρ₀} ≤ β^{1/2-ρ₂}`. -/
theorem R2old_final (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k i : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ)) (xs : ℕ → ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hj : ∀ j ∈ Finset.Icc i k, xs j ≤ K * S.β ^ (-1 + ρ₁ + ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ - ((d : ℝ) - 2) / 2 + γ) *
        S.η ^ (((d : ℝ) - 2) / 2 - ((d : ℝ) - 2) * ρ₂))
    (hβ0 : 2 * (K * (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) /
        (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1))) * S.L ^ ρ₀ ≤ S.β ^ (1 / 2 - ρ₂)) :
    ∑ j ∈ Finset.Icc i k, xs j ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hβp := S.β_pos
  have hθ : 0 < γ - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E4; have := hE.ρ₂_pos; have := S.hD; nlinarith
  have hLθ : 1 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) := Real.one_lt_rpow (by linarith [S.hL]) hθ
  have h := R2old_total hE S k i hηk xs hK hj
  refine h.trans ?_
  set A : ℝ := K * (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1))
    with hA
  have hA0 : 0 ≤ A := by
    have : 0 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1 := by linarith
    rw [hA]; positivity
  have hξi : (((S.L ^ i)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) ≤ 1 :=
    Real.rpow_le_one (by have := S.L_pos; positivity) (xi_le_one_of_pow S.hL i) hθ.le
  have hu : S.β ^ (-1 + ρ₁ + ρ₂) = S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.β ^ (-(1 / 2 : ℝ) + ρ₂) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have hone : S.β ^ (1 / 2 - ρ₂) * S.β ^ (-(1 / 2 : ℝ) + ρ₂) = 1 := by
    rw [← Real.rpow_add hβp]; simp
  have hb2 : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₂) := Real.rpow_nonneg hβp.le _
  have hle : A * S.L ^ ρ₀ * S.β ^ (-(1 / 2 : ℝ) + ρ₂) ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hβ0 hb2
    rw [mul_assoc 2, mul_assoc, hone] at h2
    nlinarith [h2]
  have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
    have := S.ξ_pos; positivity
  calc A * S.β ^ (-1 + ρ₁ + ρ₂) * (((S.L ^ i)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) * S.η ^ ρ₀
      ≤ A * S.β ^ (-1 + ρ₁ + ρ₂) * 1 * S.η ^ ρ₀ := by
        have : 0 ≤ A * S.β ^ (-1 + ρ₁ + ρ₂) := by positivity
        have := Real.rpow_nonneg S.hη0.le ρ₀
        gcongr
    _ = (A * S.L ^ ρ₀ * S.β ^ (-(1 / 2 : ℝ) + ρ₂)) * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        rw [hu, S.η_rpow_eq (e := ρ₀)]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) :=
        mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

/-- **`R₂^{k+1,k+1}` (`m = 2`, (3.39)) and T2 (`m = 1`)**: the sum over `1 ≤ j ≤ k` of terms
`K β^{-1+ρ₁+mρ₂} ξ_j^{ρ₀+γ-1} η^{1-mDρ₂}`, `m ≤ 2`, is
`≤ K L^{ρ₀}/(L^θ-1) β^{-1+ρ₁+mρ₂} ξ_{k+1}^{ρ₀}`, `θ = γ-mDρ₂`.  Uses (E3), (E4). -/
theorem R2new_total (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ)) (xs : ℕ → ℝ)
    {mm K : ℝ} (hm2 : mm ≤ 2) (hK : 0 ≤ K)
    (hj : ∀ j ∈ Finset.Icc 1 k, xs j ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) * S.η ^ (1 - mm * (((d : ℝ) - 2) * ρ₂))) :
    ∑ j ∈ Finset.Icc 1 k, xs j ≤
      (K * S.L ^ ρ₀ / (S.L ^ (γ - mm * (((d : ℝ) - 2) * ρ₂)) - 1)) *
        (S.β ^ (-1 + ρ₁ + mm * ρ₂) * S.ξ ^ ρ₀) := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hη0 := S.hη0
  have hρ2 := hE.ρ₂_pos
  have hDρ : 0 ≤ ((d : ℝ) - 2) * ρ₂ := by positivity
  have hθ : 0 < γ - mm * (((d : ℝ) - 2) * ρ₂) := by
    have := hE.E4; nlinarith
  have hcb : ρ₀ ≤ 1 - mm * (((d : ℝ) - 2) * ρ₂) := by
    have := hE.E3; nlinarith
  set θ := γ - mm * (((d : ℝ) - 2) * ρ₂) with hθdef
  have hLθ : 1 < S.L ^ θ := Real.one_lt_rpow (by linarith [S.hL]) hθ
  have hterm : ∀ j ∈ Finset.Icc 1 k, xs j ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) *
      (S.η ^ ρ₀ * (((S.L ^ j)⁻¹ : ℝ)) ^ θ) := by
    intro j hjm
    have hj' := Finset.mem_Icc.1 hjm
    have hξj : 0 < ((S.L ^ j)⁻¹ : ℝ) := by have := S.L_pos; positivity
    have hηξ : S.η ≤ ((S.L ^ j)⁻¹ : ℝ) := by
      rw [hηk]
      exact inv_anti₀ (by have := S.L_pos; positivity)
        (pow_le_pow_right₀ (by linarith [S.hL]) hj'.2)
    have h1 := xi_eta_split_gen (a := ρ₀ + γ - 1) (b := 1 - mm * (((d : ℝ) - 2) * ρ₂))
      hξj hη0 hηξ hcb
    have e : ρ₀ + γ - 1 + (1 - mm * (((d : ℝ) - 2) * ρ₂)) - ρ₀ = θ := by
      rw [hθdef]; ring
    rw [e] at h1
    refine (hj j hjm).trans ?_
    have hpre : 0 ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) := by positivity
    calc _ = K * S.β ^ (-1 + ρ₁ + mm * ρ₂) * ((((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) *
          S.η ^ (1 - mm * (((d : ℝ) - 2) * ρ₂))) := by ring
      _ ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) * ((((S.L ^ j)⁻¹ : ℝ)) ^ θ * S.η ^ ρ₀) :=
          mul_le_mul_of_nonneg_left h1 hpre
      _ = _ := by ring
  have hgeo := sum_xi_pow_le S.hL hθ k
  have h0 : 0 ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) * S.η ^ ρ₀ := by positivity
  calc ∑ j ∈ Finset.Icc 1 k, xs j
      ≤ ∑ j ∈ Finset.Icc 1 k, K * S.β ^ (-1 + ρ₁ + mm * ρ₂) * S.η ^ ρ₀ *
          (((S.L ^ j)⁻¹ : ℝ)) ^ θ :=
        Finset.sum_le_sum (fun j hjm => (hterm j hjm).trans (le_of_eq (by ring)))
    _ = K * S.β ^ (-1 + ρ₁ + mm * ρ₂) * S.η ^ ρ₀ *
          ∑ j ∈ Finset.Icc 1 k, (((S.L ^ j)⁻¹ : ℝ)) ^ θ := (Finset.mul_sum _ _ _).symm
    _ ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) * S.η ^ ρ₀ * (1 / (S.L ^ θ - 1)) :=
        mul_le_mul_of_nonneg_left hgeo h0
    _ = _ := by rw [S.η_rpow_eq (e := ρ₀)]; ring

/-- **`R₂^{k+1,k+1}` and T2, closed** (E3), (E4): for `m ≤ 2` the sum is
`≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` once `2 K L^{ρ₀}/(L^θ-1) ≤ β^{1/2-mρ₂}`. -/
theorem R2new_final (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ)) (xs : ℕ → ℝ)
    {mm K : ℝ} (hm2 : mm ≤ 2) (hK : 0 ≤ K)
    (hj : ∀ j ∈ Finset.Icc 1 k, xs j ≤ K * S.β ^ (-1 + ρ₁ + mm * ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) * S.η ^ (1 - mm * (((d : ℝ) - 2) * ρ₂)))
    (hβ0 : 2 * (K * S.L ^ ρ₀ / (S.L ^ (γ - mm * (((d : ℝ) - 2) * ρ₂)) - 1)) ≤
      S.β ^ (1 / 2 - mm * ρ₂)) :
    ∑ j ∈ Finset.Icc 1 k, xs j ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hβp := S.β_pos
  have h := R2new_total hE S k hηk xs hm2 hK hj
  refine h.trans ?_
  set A : ℝ := K * S.L ^ ρ₀ / (S.L ^ (γ - mm * (((d : ℝ) - 2) * ρ₂)) - 1) with hA
  have hu : S.β ^ (-1 + ρ₁ + mm * ρ₂) =
      S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.β ^ (-(1 / 2 : ℝ) + mm * ρ₂) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have hone : S.β ^ (1 / 2 - mm * ρ₂) * S.β ^ (-(1 / 2 : ℝ) + mm * ρ₂) = 1 := by
    rw [← Real.rpow_add hβp]; simp
  have hb2 : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + mm * ρ₂) := Real.rpow_nonneg hβp.le _
  have hle : A * S.β ^ (-(1 / 2 : ℝ) + mm * ρ₂) ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hβ0 hb2
    rw [mul_assoc, hone] at h2
    nlinarith [h2]
  have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
    have := S.ξ_pos; positivity
  calc A * (S.β ^ (-1 + ρ₁ + mm * ρ₂) * S.ξ ^ ρ₀)
      = (A * S.β ^ (-(1 / 2 : ℝ) + mm * ρ₂)) * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        rw [hu]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) :=
        mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

/-- **`R₃^{k+1,k+1}`** (P9 (3.41)): a finite family `T ⊆ [1,k]²` of terms
`K β^{-2+2ρ₁+2ρ₂} ξ_i^{ρ₀+γ-1} ξ_j^{ρ₀+γ-1} η^{2-2Dρ₂}` sums to
`≤ K L^{ρ₀}/(L^θ-1)² β^{-2+2ρ₁+2ρ₂} ξ_{k+1}^{ρ₀}`, `θ = γ-Dρ₂`.  Uses (E3), (E4). -/
theorem R3_total (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ))
    (T : Finset (ℕ × ℕ)) (hT : T ⊆ Finset.Icc 1 k ×ˢ Finset.Icc 1 k) (xs : ℕ → ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hj : ∀ p ∈ T, xs p.1 p.2 ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) *
      (((S.L ^ p.1)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) * (((S.L ^ p.2)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) *
        S.η ^ (2 - 2 * (((d : ℝ) - 2) * ρ₂))) :
    ∑ p ∈ T, xs p.1 p.2 ≤
      (K * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) ^ 2) *
        (S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.ξ ^ ρ₀) := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hη0 := S.hη0
  have hρ2 := hE.ρ₂_pos
  have hρ0 := hE.ρ₀_pos
  have hDρ : 0 ≤ ((d : ℝ) - 2) * ρ₂ := by positivity
  have hθ : 0 < γ - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E4; nlinarith
  have hcb : ρ₀ ≤ 1 - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E3; nlinarith
  set θ := γ - ((d : ℝ) - 2) * ρ₂ with hθdef
  have hLθ : 1 < S.L ^ θ := Real.one_lt_rpow (by linarith [S.hL]) hθ
  have hLp := S.L_pos
  have hηle : ∀ j ∈ Finset.Icc 1 k, S.η ≤ ((S.L ^ j)⁻¹ : ℝ) := by
    intro j hjm
    have hj' := Finset.mem_Icc.1 hjm
    rw [hηk]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith [S.hL]) hj'.2)
  have hterm : ∀ p ∈ T, xs p.1 p.2 ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.η ^ ρ₀ *
      ((((S.L ^ p.1)⁻¹ : ℝ)) ^ θ * (((S.L ^ p.2)⁻¹ : ℝ)) ^ θ) := by
    intro p hp
    have hp' := Finset.mem_product.1 (hT hp)
    have hξi : 0 < ((S.L ^ p.1)⁻¹ : ℝ) := by positivity
    have hξj : 0 < ((S.L ^ p.2)⁻¹ : ℝ) := by positivity
    have h1 := xi_eta_split_gen (a := ρ₀ + γ - 1) (b := 1 - ((d : ℝ) - 2) * ρ₂) (c := 0)
      hξi hη0 (hηle _ hp'.1) (by linarith)
    have h2 := xi_eta_split_gen (a := ρ₀ + γ - 1) (b := 1 - ((d : ℝ) - 2) * ρ₂) (c := ρ₀)
      hξj hη0 (hηle _ hp'.2) hcb
    have e1 : ρ₀ + γ - 1 + (1 - ((d : ℝ) - 2) * ρ₂) - 0 = ρ₀ + θ := by rw [hθdef]; ring
    have e2 : ρ₀ + γ - 1 + (1 - ((d : ℝ) - 2) * ρ₂) - ρ₀ = θ := by rw [hθdef]; ring
    rw [e1, Real.rpow_zero, mul_one] at h1
    rw [e2] at h2
    have h1' : ((S.L ^ p.1)⁻¹ : ℝ) ^ (ρ₀ + θ) ≤ ((S.L ^ p.1)⁻¹ : ℝ) ^ θ :=
      Real.rpow_le_rpow_of_exponent_ge hξi (xi_le_one_of_pow S.hL _) (by linarith)
    have h3 := mul_le_mul (h1.trans h1') h2 (by positivity) (by positivity)
    have e3 : S.η ^ (2 - 2 * (((d : ℝ) - 2) * ρ₂)) =
        S.η ^ (1 - ((d : ℝ) - 2) * ρ₂) * S.η ^ (1 - ((d : ℝ) - 2) * ρ₂) := by
      rw [← Real.rpow_add hη0]; congr 1; ring
    refine (hj p hp).trans ?_
    have hpre : 0 ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) := by positivity
    calc _ = K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) *
          ((((S.L ^ p.1)⁻¹ : ℝ) ^ (ρ₀ + γ - 1) * S.η ^ (1 - ((d : ℝ) - 2) * ρ₂)) *
            (((S.L ^ p.2)⁻¹ : ℝ) ^ (ρ₀ + γ - 1) * S.η ^ (1 - ((d : ℝ) - 2) * ρ₂))) := by
          rw [e3]; ring
      _ ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) *
          ((((S.L ^ p.1)⁻¹ : ℝ)) ^ θ * ((((S.L ^ p.2)⁻¹ : ℝ)) ^ θ * S.η ^ ρ₀)) :=
          mul_le_mul_of_nonneg_left h3 hpre
      _ = _ := by ring
  have h0 : 0 ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.η ^ ρ₀ := by positivity
  have hgeo := sum_xi_pow_le S.hL hθ k
  have hgeo0 : 0 ≤ ∑ j ∈ Finset.Icc 1 k, (((S.L ^ j)⁻¹ : ℝ)) ^ θ :=
    Finset.sum_nonneg (fun j _ => by positivity)
  calc ∑ p ∈ T, xs p.1 p.2
      ≤ ∑ p ∈ T, K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.η ^ ρ₀ *
          ((((S.L ^ p.1)⁻¹ : ℝ)) ^ θ * (((S.L ^ p.2)⁻¹ : ℝ)) ^ θ) := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ Finset.Icc 1 k ×ˢ Finset.Icc 1 k, K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.η ^ ρ₀ *
          ((((S.L ^ p.1)⁻¹ : ℝ)) ^ θ * (((S.L ^ p.2)⁻¹ : ℝ)) ^ θ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hT (fun p _ _ => by positivity)
    _ = K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.η ^ ρ₀ *
          ((∑ i ∈ Finset.Icc 1 k, (((S.L ^ i)⁻¹ : ℝ)) ^ θ) *
            ∑ j ∈ Finset.Icc 1 k, (((S.L ^ j)⁻¹ : ℝ)) ^ θ) := by
        rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.η ^ ρ₀ *
          ((1 / (S.L ^ θ - 1)) * (1 / (S.L ^ θ - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hgeo hgeo hgeo0 (by
          have : 0 < S.L ^ θ - 1 := by linarith
          positivity)) h0
    _ = _ := by
        rw [S.η_rpow_eq (e := ρ₀)]
        have : S.L ^ θ - 1 ≠ 0 := by linarith
        field_simp

/-- **`R₃^{k+1,k+1}`, closed**: `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` once
`2 K L^{ρ₀}/(L^θ-1)² ≤ β^{3/2-ρ₁-2ρ₂}`. -/
theorem R3_final (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (hηk : S.η = ((S.L ^ k)⁻¹ : ℝ))
    (T : Finset (ℕ × ℕ)) (hT : T ⊆ Finset.Icc 1 k ×ˢ Finset.Icc 1 k) (xs : ℕ → ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hj : ∀ p ∈ T, xs p.1 p.2 ≤ K * S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) *
      (((S.L ^ p.1)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) * (((S.L ^ p.2)⁻¹ : ℝ)) ^ (ρ₀ + γ - 1) *
        S.η ^ (2 - 2 * (((d : ℝ) - 2) * ρ₂)))
    (hβ0 : 2 * (K * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) ^ 2) ≤
      S.β ^ (3 / 2 - ρ₁ - 2 * ρ₂)) :
    ∑ p ∈ T, xs p.1 p.2 ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hβp := S.β_pos
  have h := R3_total hE S k hηk T hT xs hK hj
  refine h.trans ?_
  set A : ℝ := K * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) ^ 2 with hA
  have hu : S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) =
      S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.β ^ (-(3 / 2 : ℝ) + ρ₁ + 2 * ρ₂) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have hone : S.β ^ (3 / 2 - ρ₁ - 2 * ρ₂) * S.β ^ (-(3 / 2 : ℝ) + ρ₁ + 2 * ρ₂) = 1 := by
    rw [← Real.rpow_add hβp]; simp
  have hb2 : 0 ≤ S.β ^ (-(3 / 2 : ℝ) + ρ₁ + 2 * ρ₂) := Real.rpow_nonneg hβp.le _
  have hle : A * S.β ^ (-(3 / 2 : ℝ) + ρ₁ + 2 * ρ₂) ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hβ0 hb2
    rw [mul_assoc, hone] at h2
    nlinarith [h2]
  have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
    have := S.ξ_pos; positivity
  calc A * (S.β ^ (-2 + 2 * ρ₁ + 2 * ρ₂) * S.ξ ^ ρ₀)
      = (A * S.β ^ (-(3 / 2 : ℝ) + ρ₁ + 2 * ρ₂)) * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        rw [hu]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) :=
        mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

end Sums

end Balaban.Observables
