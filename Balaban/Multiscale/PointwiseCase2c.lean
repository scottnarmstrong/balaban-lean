/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseCase2b

/-!
# Lemma P, Case 2, step 3: the `L²` part

`ρ^{-d/2} ‖ũ‖_{ℓ²(B_{2ρ})} ≤ K e^{-(ε₀/2) t} ℓ_{j'}² ‖f‖_∞` for `ρ = c₀ L^{j-1}/d`, with `K`
depending only on `d`, `L`, `c₀` (`l2_part`).
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem rpow_neg_half_eq {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ρ ^ (-(d : ℝ) / 2) = (Real.sqrt (ρ ^ d))⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← Real.rpow_neg hρ.le]
  congr 1
  ring

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} {Λ : ℝ} (S : PtSetting G Λ)

theorem l2_part {c0 : ℝ} (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4) {j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (hρ : 8 ≤ c0 * (L : ℝ) ^ (j - 1) / d) {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist x S.y') :
    (c0 * (L : ℝ) ^ (j - 1) / d) ^ (-(d : ℝ) / 2) *
        Real.sqrt (∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * (c0 * (L : ℝ) ^ (j - 1) / d)),
          ‖S.ut (liftPt x w)‖ ^ 2) ≤
      2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
        Real.sqrt ((c0 / d) ^ d) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * S.j') * Mf) := by
  have hc := poincareConst_pos S.hd0
  have hε0 := agmonRate_pos S.hd0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast S.hd0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hb1 := one_le_bd (d := d) (L := L)
  have hb0 : 0 < bd d L := by linarith
  obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
  have hj01 : 1 ≤ j₀ := by omega
  simp only [Nat.add_sub_cancel] at hρ ⊢
  set ρ := c0 * (L : ℝ) ^ j₀ / d with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hLj0 : (0 : ℝ) < (L : ℝ) ^ j₀ := by positivity
  have hRd : (d : ℝ) * (2 * ρ) ≤ (L : ℝ) ^ (j₀ + 1 - 1) := by
    simp only [Nat.add_sub_cancel]
    rw [hρdef]
    field_simp
    nlinarith
  obtain ⟨t₂, htt, ht2, habs⟩ := scale_abs S (j := j₀ + 1) (by omega) hx ht0 ht
  have ht20 : 0 ≤ t₂ := ht0.trans htt
  have hball := ball_sq_bound S hj2 hjk hx (R := 2 * ρ) (by positivity) hRd ht20 ht2
  set Q2 := ∑ w ∈ latticeBall (0 : Fin d → ℤ) (2 * ρ), ‖S.ut (liftPt x w)‖ ^ 2 with hQ2
  set amp := S.amp with hamp
  have hampn := S.amp_nonneg
  have hΛ : Real.sqrt Q2 ≤ (L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
      (2 / poincareConst d) * amp := by
    have h1 : Q2 ≤ ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
        (2 / poincareConst d) * amp) ^ 2 := by
      refine hball.trans (le_of_eq ?_)
      rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
      have : Real.exp (-(2 * agmonRate d * (t₂ - 1))) =
          Real.exp (((2 : ℕ) : ℝ) * (-(agmonRate d * (t₂ - 1)))) := by
        congr 1; push_cast; ring
      rw [this]
      field_simp
      ring
    calc Real.sqrt Q2 ≤ Real.sqrt (((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * amp) ^ 2) := Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  have hP : 0 < Real.sqrt ((c0 / d) ^ d) := Real.sqrt_pos.2 (by positivity)
  have hrp := rpow_neg_half_eq hρ0 d
  have hsq : Real.sqrt (ρ ^ d) = Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀) := by
    have e : ρ ^ d = (c0 / d) ^ d * ((L : ℝ) ^ j₀) ^ d := by
      rw [← mul_pow, hρdef]; congr 1; ring
    rw [e, Real.sqrt_mul (by positivity), sqrt_L_pow_eq (by have := S.hd; omega)]
  rw [hrp, hsq]
  have hamp_le := amp_le S hMf0 hMf
  have hE1 : Real.exp (-(agmonRate d * (t₂ - 1))) =
      Real.exp (agmonRate d) * Real.exp (-(agmonRate d * t₂)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE2 : Real.exp (agmonRate d * (1 + 2 * d)) =
      Real.exp (agmonRate d) * Real.exp (2 * agmonRate d * d) := by
    rw [← Real.exp_add]; congr 1; ring
  have hMfn := hMf0
  calc (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ * Real.sqrt Q2
      ≤ (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
        ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * amp) := mul_le_mul_of_nonneg_left hΛ (by positivity)
    _ ≤ (Real.sqrt ((c0 / d) ^ d) * ((L : ℝ) ^ j₀ * bd d L ^ j₀))⁻¹ *
        ((L : ℝ) ^ (j₀ + 1 + 1) * Real.exp (-(agmonRate d * (t₂ - 1))) *
          (2 / poincareConst d) * (Real.exp (2 * agmonRate d * d) * ((L : ℝ) ^ S.j') ^ 2 *
            bd d L ^ S.j' * Mf)) := by
        gcongr
    _ = (2 / poincareConst d * Real.exp (agmonRate d) * Real.exp (2 * agmonRate d * d) *
          (L : ℝ) ^ 2 / (Real.sqrt ((c0 / d) ^ d) * bd d L ^ j₀)) *
        ((bd d L ^ S.j' * Real.exp (-(agmonRate d * t₂))) * (((L : ℝ) ^ S.j') ^ 2 * Mf)) := by
        rw [hE1]
        field_simp
        ring
    _ ≤ (2 / poincareConst d * Real.exp (agmonRate d) * Real.exp (2 * agmonRate d * d) *
          (L : ℝ) ^ 2 / (Real.sqrt ((c0 / d) ^ d) * bd d L ^ j₀)) *
        ((bd d L ^ (j₀ + 1) * bd d L * Real.exp (-(agmonRate d / 2 * t))) *
          (((L : ℝ) ^ S.j') ^ 2 * Mf)) := by
        gcongr
    _ = _ := by
        rw [hE2, pow_mul', pow_succ]
        field_simp
        ring

end PtSetting

end Balaban.Multiscale
