/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.Thm31bFromTower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable prefactor at its birth scale

For the observable term created at one step the prefactor `obsPrefactor p s b` is bounded by
`C b^{-1/2-δ'/(d-2)}`, hence at `b = β L^{k(d-2)}` by `C β^{-e/(d-2)} L^{-k e}` with
`e = (d-2)/2 + δ'`.  The last theorem converts a class-type bound with the factor `L^{-j e}` into
the per-term bound of the root.
-/

@[expose] public section

namespace Balaban.Inhabited

open Real Balaban.Fluctuation

/-- A power of the logarithm is dominated by any positive power: for `m ≥ 0`, `ε > 0` there is
`C ≥ 0` with `(log b)^m ≤ C b^ε` for `b ≥ 1`. -/
theorem log_rpow_le_const_mul_rpow {m ε : ℝ} (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 1 ≤ b → Real.log b ^ m ≤ C * b ^ ε := by
  set η : ℝ := ε / (m + 1) with hη
  have hm1 : 0 < m + 1 := by linarith
  have hηpos : 0 < η := div_pos hε hm1
  refine ⟨(η⁻¹) ^ m, by positivity, fun b hb => ?_⟩
  have hb0 : 0 < b := by linarith
  have hlog : Real.log b ≤ b ^ η / η := Real.log_le_rpow_div hb0.le hηpos
  have hl0 : 0 ≤ Real.log b := Real.log_nonneg hb
  calc Real.log b ^ m ≤ (b ^ η / η) ^ m := Real.rpow_le_rpow hl0 hlog hm
    _ = (η⁻¹) ^ m * b ^ (η * m) := by
        rw [div_eq_inv_mul, Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hb0.le]
    _ ≤ (η⁻¹) ^ m * b ^ ε := by
        have : η * m ≤ ε := by
          rw [hη, div_mul_eq_mul_div, div_le_iff₀ hm1]; nlinarith
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb this)
          (by positivity)

private lemma obsW_pow_eq (p : ℕ) (n : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    obsW (p : ℝ) b ^ n = Real.log b ^ ((p : ℝ) * n) := by
  unfold obsW
  rw [Real.rpow_mul_natCast (Real.log_nonneg hb)]

/-- **T1.** The prefactor decays like `b^{-1/2-δ'/(d-2)}` (`dm2 = d - 2`). -/
theorem obsPrefactor_le_scale (p : ℕ) {s δ' dm2 : ℝ} (hdm : 0 < dm2)
    (hδs : δ' < s * dm2) (hδd : δ' < dm2 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 1 ≤ b → obsPrefactor p s b ≤ C * b ^ (-(1 / 2) - δ' / dm2) := by
  have h1 : 0 < s - δ' / dm2 := by
    have : δ' / dm2 < s := by rw [div_lt_iff₀ hdm]; exact hδs
    linarith
  have h2 : 0 < 1 / 2 - δ' / dm2 := by
    have : δ' / dm2 < 1 / 2 := by rw [div_lt_iff₀ hdm]; linarith
    linarith
  obtain ⟨C1, hC1, H1⟩ := log_rpow_le_const_mul_rpow (m := (p : ℝ) * (4 : ℕ)) (by positivity) h1
  obtain ⟨C2, hC2, H2⟩ := log_rpow_le_const_mul_rpow (m := (p : ℝ) * (2 : ℕ)) (by positivity) h2
  refine ⟨C1 + C2, by positivity, fun b hb => ?_⟩
  have hb0 : 0 < b := by linarith
  unfold obsPrefactor
  rw [obsW_pow_eq p 4 hb, obsW_pow_eq p 2 hb]
  have e1 : b ^ (s - δ' / dm2) * b ^ (-(1 / 2) - s) = b ^ (-(1 / 2) - δ' / dm2) := by
    rw [← Real.rpow_add hb0]; congr 1; ring
  have e2 : b ^ (1 / 2 - δ' / dm2) / b = b ^ (-(1 / 2) - δ' / dm2) := by
    rw [← Real.rpow_sub_one hb0.ne']; congr 1; ring
  have hp : 0 ≤ b ^ (-(1 / 2 : ℝ) - s) := by positivity
  calc _ ≤ (C1 * b ^ (s - δ' / dm2)) * b ^ (-(1 / 2) - s)
        + (C2 * b ^ (1 / 2 - δ' / dm2)) / b := by
        gcongr
        · exact H1 b hb
        · exact H2 b hb
    _ = (C1 + C2) * b ^ (-(1 / 2) - δ' / dm2) := by
        rw [mul_assoc, e1, mul_div_assoc, e2]; ring

private lemma scale_rpow (β Lr : ℝ) (hβ : 0 < β) (hL : 0 < Lr) (n : ℕ) (x : ℝ) :
    (β * Lr ^ n) ^ (-x) = β ^ (-x) * Lr ^ (-((n : ℝ) * x)) := by
  rw [Real.mul_rpow hβ.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 2; ring

/-- **T2.** The scale corollary at `b = β L^{k(d-2)}`, `e = (d-2)/2 + δ'`; the constant `C` is that
of T1 with `dm2 = d - 2` (it depends only on `p, s, δ', d`). -/
theorem obsPrefactor_le_birth_scale (p : ℕ) {s δ' : ℝ} {d : ℕ} (hd : 3 ≤ d)
    (hδs : δ' < s * ((d : ℝ) - 2)) (hδd : δ' < ((d : ℝ) - 2) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L k : ℕ) (β : ℝ), 2 ≤ L → 1 ≤ β →
      obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) ≤
        C * β ^ (-(((d - 2 : ℝ) / 2 + δ') / ((d : ℝ) - 2))) *
          (L : ℝ) ^ (-((k : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) ∧
      obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) ≤
        (C * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ') *
            β ^ (-((((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2)))) *
          (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by
  have hdm : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C, hC, H⟩ := obsPrefactor_le_scale p hdm hδs hδd
  refine ⟨C, hC, fun L k β hL hβ => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hL0 : (0 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hcast : (((d - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hb : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) :=
      one_le_pow₀ (by have : (2 : ℝ) ≤ L := by exact_mod_cast hL
                      linarith)
    nlinarith
  have key : obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2))) ≤
      C * β ^ (-(((d - 2 : ℝ) / 2 + δ') / ((d : ℝ) - 2))) *
        (L : ℝ) ^ (-((k : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by
    refine (H _ hb).trans ?_
    have hx : -(1 / 2 : ℝ) - δ' / ((d : ℝ) - 2) = -(((d - 2 : ℝ) / 2 + δ') / ((d : ℝ) - 2)) := by
      field_simp
      ring
    rw [hx, scale_rpow β L hβ0 hL0, mul_assoc]
    have hexp : -(((k * (d - 2) : ℕ) : ℝ) *
        (((d - 2 : ℝ) / 2 + δ') / ((d : ℝ) - 2))) = -((k : ℝ) * (((d : ℝ) - 2) / 2 + δ')) := by
      push_cast
      rw [hcast]
      field_simp
    rw [hexp]
  refine ⟨key, key.trans (le_of_eq ?_)⟩
  have hsplit : (L : ℝ) ^ (-((k : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) =
      (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ') *
        (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by
    rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
  rw [hsplit]; ring

/-- **T2 at `d = L = 3`**, in the scale variable `β 3^k` of the landed bounds: with `e = 1/2 + δ'`,
`obsPrefactor p s (β 3^k) ≤ C 3^e β^{-e} 3^{-(k+1)e}`. -/
theorem obsPrefactor_le_birth_scale_three (p : ℕ) {s δ' : ℝ} (hδs : δ' < s) (hδd : δ' < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (β : ℝ), 1 ≤ β →
      obsPrefactor p s (β * (3 : ℝ) ^ k) ≤
        C * (3 : ℝ) ^ (1 / 2 + δ') * β ^ (-(1 / 2 + δ')) *
          (3 : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (1 / 2 + δ'))) := by
  obtain ⟨C, hC, H⟩ := obsPrefactor_le_scale p (s := s) (δ' := δ') (dm2 := 1) one_pos (by linarith) (by linarith)
  refine ⟨C, hC, fun k β hβ => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hb : 1 ≤ β * (3 : ℝ) ^ k := by
    have : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  refine (H _ hb).trans (le_of_eq ?_)
  have hx : -(1 / 2 : ℝ) - δ' / 1 = -(1 / 2 + δ') := by ring
  rw [hx, scale_rpow β 3 hβ0 (by norm_num)]
  have hsplit : (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ'))) =
      (3 : ℝ) ^ (1 / 2 + δ') * (3 : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (1 / 2 + δ'))) := by
    rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
  rw [hsplit]; ring

/-- **Absorption.** The new term meets any prescribed class constant `c > 0` once `β` is large. -/
theorem birth_const_le_of_large {C c e q : ℝ} (L : ℝ) (hL : 0 < L) (hc : 0 < c) (hq : 0 < q) :
    ∃ β₁ : ℝ, 1 ≤ β₁ ∧ ∀ β : ℝ, β₁ ≤ β → |C| * L ^ e * β ^ (-q) ≤ c := by
  set A : ℝ := |C| * L ^ e with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max 1 ((A / c) ^ (1 / q)), le_max_left _ _, fun β hβ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hβ)
  show A * β ^ (-q) ≤ c
  have h1 : (A / c) ^ (1 / q) ≤ β := le_trans (le_max_right _ _) hβ
  have h2 : A / c ≤ β ^ q := by
    have := Real.rpow_le_rpow (by positivity) h1 hq.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one] at this
  rw [Real.rpow_neg hβ0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hc] at h2
  linarith

/-- **T3.** Conversion of a class-type bound with the factor `L^{-j e}` into the root's per-term
bound with exponent `(d-2)/2 + δ`, given the rate inequality for `sizeJ`. -/
theorem rootBound_of_classBound {v lam κ Y c₉cl c₉root e δ Sz a L : ℝ} {j d : ℕ}
    (hL : 1 ≤ L) (he : ((d : ℝ) - 2) / 2 + δ ≤ e)
    (hv : v ≤ c₉cl * L ^ (-((j : ℝ) * e)) * Real.exp (-lam * Sz))
    (hc : 0 ≤ c₉cl) (hc9 : c₉cl * Real.exp lam ≤ c₉root)
    (hrate : Real.exp (-lam * Sz) ≤ Real.exp lam * Real.exp (-κ * Y / a ^ d)) :
    v ≤ c₉root * L ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * Real.exp (-κ * Y / a ^ d) := by
  have hL0 : 0 < L := by linarith
  have hmono : L ^ (-((j : ℝ) * e)) ≤ L ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  refine hv.trans ?_
  have hc90 : 0 ≤ c₉root := le_trans (by positivity) hc9
  have hE : 0 ≤ Real.exp (-κ * Y / a ^ d) := (Real.exp_pos _).le
  have hP : 0 ≤ L ^ (-((j : ℝ) * e)) := by positivity
  calc c₉cl * L ^ (-((j : ℝ) * e)) * Real.exp (-lam * Sz)
      ≤ c₉cl * L ^ (-((j : ℝ) * e)) * (Real.exp lam * Real.exp (-κ * Y / a ^ d)) := by
        gcongr
    _ = (c₉cl * Real.exp lam) * L ^ (-((j : ℝ) * e)) * Real.exp (-κ * Y / a ^ d) := by ring
    _ ≤ c₉root * L ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * Real.exp (-κ * Y / a ^ d) := by
        gcongr

end Balaban.Inhabited
