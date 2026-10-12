/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ChainSeq
public import Balaban.LargeField.History.StepSpine
public import Balaban.SmallField.Def6InfPaving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Inhabitation witnesses for the numerical hypothesis structures

`RunningHyp`, `StepRadii`, `RadiusHyp`, `StepGeom`, `SpineNum`, `IsAdmDelta`, `GoodMap`.
None of these witnesses is degenerate: the running coefficients are the exact `β L^{k(d-2)}`,
`ν L^{2k}`; the radii sit at the minimal value `4L + 20`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField

/-- **`RunningHyp` is inhabited** (`γ_k = δ_k = 1`, `ε = 0`, `a = 5/4`). -/
theorem runningHyp_nonempty {d L : ℕ} (hd : 2 ≤ d) (hL : 2 ≤ L) {β ν : ℝ} (hβ : 0 < β)
    (hν : 0 < ν) :
    ∃ betaRun nuRun : ℕ → ℝ, RunningHyp d L β ν (5 / 4) 0 betaRun nuRun :=
  ⟨fun k => β * (L : ℝ) ^ (k * (d - 2)) * 1, fun k => ν * (L : ℝ) ^ (2 * k) * 1,
    { hd := hd, hL := hL, hβ := hβ, hν := hν, ha1 := by norm_num, ha2 := by norm_num
      hε0 := le_rfl, hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, rfl⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, rfl⟩ }⟩

/-- **`StepRadii` is inhabited**, with `R_prev = R_k = 4L + 20`. -/
theorem stepRadii_nonempty {L : ℕ} (hL : 2 ≤ L) :
    ∃ ω r : ℕ, StepRadii L ω r ((4 * L + 20 : ℝ)) ((4 * L + 20 : ℝ)) := by
  refine ⟨2 * ⌊(4 * L + 20 : ℝ)⌋₊ + L + 11, ⌈(4 * L + 20 : ℝ)⌉₊, ?_⟩
  exact StepRadii.of_real hL (by positivity) le_rfl le_rfl le_rfl rfl

/-- **`StepGeom` is inhabited** (`n₀ = L n₁`, `ω_k = L`). -/
theorem stepGeom_nonempty {L : ℕ} (hL : 2 ≤ L) (n1 : ℕ) :
    ∃ ωk ω r : ℕ, StepGeom L (L * n1) n1 ωk ω r ((4 * L + 20 : ℝ)) ((4 * L + 20 : ℝ)) := by
  obtain ⟨ω, r, h⟩ := stepRadii_nonempty hL
  refine ⟨L, ω, r, rfl, h, ?_, le_rfl, ?_⟩
  · have h1 := h.omega_rho
    have : (L + L - 2) / L < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  · have := h.omega_rho; omega

/-- **`RadiusHyp` is inhabited**: `λ_j = 1 + j`, `R_j = R_base λ_j²`, `R_base = 4L + 20`. -/
theorem radiusHyp_nonempty (L : ℕ) :
    RadiusHyp L (4 * L + 20) (fun j => 1 + (j : ℝ))
      (fun j => (4 * L + 20 : ℝ) * (1 + (j : ℝ)) ^ 2) where
  mono := fun i j h => by
    have : (i : ℝ) ≤ j := by exact_mod_cast h
    simp only; linarith
  one_le := fun j => by simp
  nonneg := fun j => by positivity
  le := fun j => le_rfl
  base := le_rfl

/-- **`SpineNum` is inhabited** for every `L ≥ 1`, `r`, `ρ_k`. -/
theorem spineNum_nonempty (d r ρk : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ∃ ω ρ : ℕ, ∃ D : ℝ, RegionStep.SpineNum d L r ω ρk ρ D := by
  refine ⟨1, ρk + 4 + 5 * r, Real.sqrt d * (2 * (((ρk + 4 + 5 * r : ℕ) : ℝ) + 4) +
    (((1 : ℕ) : ℝ) - 1) + 2), ?_, ?_, le_rfl, le_rfl⟩
  · have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have h0 : (0 : ℝ) ≤ ρk + 4 := by positivity
    have : ((ρk : ℝ) + 4) / L ≤ ρk + 4 := div_le_self h0 hL'
    push_cast
    nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  · push_cast
    nlinarith [(Nat.cast_nonneg ρk : (0 : ℝ) ≤ ρk)]

/-- **`IsAdmDelta` is inhabited** by `δ_i = 2^{-i}` when `d ≥ 3`, `L ≥ 4` (so `L^{(d-2)/2} ≥ 2`). -/
theorem isAdmDelta_nonempty {d L : ℕ} (hd : 3 ≤ d) (hL : 4 ≤ L) {ε : ℝ} (hε : 0 ≤ ε)
    (k1 k : ℕ) : IsAdmDelta d L ε k1 k (fun i => (1 / 2 : ℝ) ^ i) where
  pos := fun i _ _ => by positivity
  anti := fun i _ _ => by
    simp only [pow_succ]
    have : (0 : ℝ) < (1 / 2) ^ i := by positivity
    nlinarith
  growth := fun i j _ hij _ => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hL4 : (4 : ℝ) ≤ L := by exact_mod_cast hL
    have hd3 : (1 : ℝ) ≤ (d : ℝ) - 2 := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h2 : (2 : ℝ) ^ (m : ℝ) ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2 * (((i + m : ℕ) : ℝ) - i)) := by
      have hm : (((i + m : ℕ) : ℝ) - i) = m := by push_cast; ring
      rw [hm]
      have e : (2 : ℝ) ^ (m : ℝ) = (4 : ℝ) ^ ((1 / 2 : ℝ) * m) := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        congr 1; ring
      rw [e]
      calc (4 : ℝ) ^ ((1 / 2 : ℝ) * m) ≤ (L : ℝ) ^ ((1 / 2 : ℝ) * m) :=
            Real.rpow_le_rpow (by norm_num) hL4 (by positivity)
        _ ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2 * (m : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by
              have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
              nlinarith)
    have hexp : 1 ≤ Real.exp ε := Real.one_le_exp hε
    have h2' : (2 : ℝ) ^ m = (2 : ℝ) ^ (m : ℝ) := by simp
    have hp : (0 : ℝ) < (1 / 2) ^ (i + m) := by positivity
    have : (1 / 2 : ℝ) ^ i = 2 ^ m * (1 / 2) ^ (i + m) := by
      rw [pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ m), mul_assoc, ← mul_pow]; norm_num
    rw [this]
    have h3 : (2 : ℝ) ^ m * (1 / 2) ^ (i + m) ≤
        (L : ℝ) ^ (((d : ℝ) - 2) / 2 * (((i + m : ℕ) : ℝ) - i)) * (1 / 2) ^ (i + m) := by
      rw [h2'] ; exact mul_le_mul_of_nonneg_right h2 hp.le
    have hLp : 0 ≤ (L : ℝ) ^ (((d : ℝ) - 2) / 2 * (((i + m : ℕ) : ℝ) - i)) := by positivity
    nlinarith [mul_nonneg hLp hp.le]
  tail := fun i _ _ => by
    have h : ∑ n ∈ Finset.Icc i k, (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ i / (1 - 1 / 2) := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    have hp : (0 : ℝ) < (1 / 2) ^ i := by positivity
    linarith [show (1 / 2 : ℝ) ^ i / (1 - 1 / 2) = 2 * (1 / 2) ^ i by ring]

/-- **`GoodMap` is inhabited** (the identity). -/
theorem goodMap_nonempty (d n s a : ℕ) :
    Balaban.SmallField.Def6.GoodMap (d := d) (n := n) s a 1 :=
  Balaban.SmallField.Def6.GoodMap.one s a

end Balaban.Inhabited
