/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseGeom

/-!
# Lemma P: the scale mismatch for the pointwise bounds

`bd d L = sqrt (L^{d-2})`; the amplitude of the source satisfies
`A ≤ e^{2 ε₀ d} ℓ_{j'}² bd^{j'} ‖f‖_∞` (`amp_le`), and the factor `bd^{j'}` relative to the layer `j`
of the evaluation point is absorbed by the separation of the layers (`scale_abs`).
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem sqrt_pow_eq' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

/-- `bd = sqrt (L^{d-2})`. -/
def bd (d L : ℕ) : ℝ := Real.sqrt ((L : ℝ) ^ (d - 2))

theorem one_le_bd (d : ℕ) : 1 ≤ bd d L := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold bd
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (one_le_pow₀ hL)

theorem bd_le (d : ℕ) : bd d L ≤ (L : ℝ) ^ d := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold bd
  have h1 : Real.sqrt ((L : ℝ) ^ (d - 2)) ≤ (L : ℝ) ^ (d - 2) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have : (1 : ℝ) ≤ (L : ℝ) ^ (d - 2) := one_le_pow₀ hL
    nlinarith
  exact h1.trans (pow_le_pow_right₀ hL (by omega))

theorem pow_mul_exp_le' {B c : ℝ} (hB : 1 ≤ B) (hc : B ≤ Real.exp c) (m : ℕ) :
    B ^ m * Real.exp (-(c * ((m - 1 : ℕ) : ℝ))) ≤ B := by
  have hB0 : (0 : ℝ) < B := by linarith
  have key : ∀ n : ℕ, B ^ n * Real.exp (-(c * n)) ≤ 1 := by
    intro n
    have h1 : B ^ n ≤ Real.exp c ^ n := pow_le_pow_left₀ hB0.le hc n
    have h2 : Real.exp c ^ n = Real.exp (n * c) := by rw [Real.exp_nat_mul]
    have h3 : Real.exp (n * c) * Real.exp (-(c * n)) = 1 := by
      rw [← Real.exp_add]; simp [mul_comm]
    calc B ^ n * Real.exp (-(c * n)) ≤ Real.exp (n * c) * Real.exp (-(c * n)) :=
          mul_le_mul_of_nonneg_right (h1.trans h2.le) (Real.exp_pos _).le
      _ = 1 := h3
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [hB]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have : n + 1 - 1 = n := by omega
    rw [this, pow_succ]
    calc B ^ n * B * Real.exp (-(c * n)) = B * (B ^ n * Real.exp (-(c * n))) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left (key n) hB0.le
      _ = B := mul_one _

omit [NeZero L] in
theorem sqrt_L_pow_eq (hd : 2 ≤ d) (j : ℕ) :
    Real.sqrt (((L : ℝ) ^ j) ^ d) = (L : ℝ) ^ j * bd d L ^ j := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have e : ((L : ℝ) ^ j) ^ d = ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ (d - 2)) ^ j := by
    have h1 : ((L : ℝ) ^ j) ^ (d - 2) = ((L : ℝ) ^ (d - 2)) ^ j := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [← h1, ← pow_add]
    congr 1
    omega
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    sqrt_pow_eq' (by positivity)]
  rfl

theorem amp_le {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G) {Mf : ℝ} (hMf0 : 0 ≤ Mf)
    (hMf : ∀ i, ‖S.f i‖ ≤ Mf) :
    S.amp ≤ Real.exp (2 * agmonRate d * d) * ((L : ℝ) ^ S.j') ^ 2 * bd d L ^ S.j' * Mf := by
  have h := sqrt_sqNorm_le_of_supp G S.hj'k hMf0 hMf S.hsupp
  rw [sqrt_L_pow_eq (by have := S.hd; omega)] at h
  unfold PtSetting.amp
  have hE : 0 ≤ Real.exp (2 * agmonRate d * d) := (Real.exp_pos _).le
  have hL : 0 ≤ (L : ℝ) ^ S.j' := by positivity
  calc (L : ℝ) ^ S.j' * Real.exp (2 * agmonRate d * d) * Real.sqrt (Green.sqNorm S.f)
      ≤ (L : ℝ) ^ S.j' * Real.exp (2 * agmonRate d * d) *
        ((L : ℝ) ^ S.j' * bd d L ^ S.j' * Mf) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The scale mismatch: the factor `bd^{j'}` is absorbed by the layer separation. -/
theorem scale_abs {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G) {j : ℕ} (hj1 : 1 ≤ j)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x S.y') :
    ∃ t₂ : ℝ, t ≤ t₂ ∧ ENNReal.ofReal t₂ ≤ G.pathDist x S.y' ∧
      bd d L ^ S.j' * Real.exp (-(agmonRate d * t₂)) ≤
        bd d L ^ j * bd d L * Real.exp (-(agmonRate d / 2 * t)) := by
  have hε0 := agmonRate_pos S.hd0
  have hb1 := one_le_bd (d := d) (L := L)
  have hb0 : 0 < bd d L := by linarith
  rcases le_or_gt S.j' j with h | h
  · refine ⟨t, le_rfl, ht, ?_⟩
    have h1 : bd d L ^ S.j' ≤ bd d L ^ j := pow_le_pow_right₀ hb1 h
    have h2 : Real.exp (-(agmonRate d * t)) ≤ Real.exp (-(agmonRate d / 2 * t)) := by
      apply Real.exp_le_exp.2
      nlinarith
    calc bd d L ^ S.j' * Real.exp (-(agmonRate d * t)) ≤ bd d L ^ j *
          Real.exp (-(agmonRate d / 2 * t)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by
          rw [mul_assoc, mul_comm (bd d L) _, ← mul_assoc]
          have : 0 ≤ bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) := by positivity
          nlinarith
  · have hsep0 := G.pathDist_separation_le S.hϱ hj1 S.hj'k hx (G.mem_layer.1 S.hy').1
    set s0 : ℝ := (ϱ - 1) * ((S.j' - j - 1 : ℕ) : ℝ) with hs0
    have hs00 : 0 ≤ s0 := mul_nonneg (by linarith [S.hϱ]) (Nat.cast_nonneg _)
    refine ⟨max t s0, le_max_left _ _, ?_, ?_⟩
    · rcases le_total t s0 with h' | h'
      · rw [max_eq_right h']; exact hsep0
      · rw [max_eq_left h']; exact ht
    · set m := S.j' - j with hm
      have hjm : S.j' = j + m := by omega
      have hexp : Real.exp (-(agmonRate d * max t s0)) ≤
          Real.exp (-(agmonRate d / 2 * t)) * Real.exp (-(agmonRate d / 2 * s0)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : t ≤ max t s0 := le_max_left _ _
        have h2 : s0 ≤ max t s0 := le_max_right _ _
        nlinarith
      have hc : bd d L ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) :=
        (bd_le d).trans S.hsep
      have habs := pow_mul_exp_le' hb1 hc m
      have e : agmonRate d / 2 * s0 = agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ) := by
        rw [hs0]; ring
      rw [e] at hexp
      calc bd d L ^ S.j' * Real.exp (-(agmonRate d * max t s0))
          ≤ bd d L ^ (j + m) * (Real.exp (-(agmonRate d / 2 * t)) *
            Real.exp (-(agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
            rw [hjm]; exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) *
            (bd d L ^ m * Real.exp (-(agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
            rw [pow_add]; ring
        _ ≤ bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) * bd d L :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = _ := by ring

end Balaban.Multiscale
