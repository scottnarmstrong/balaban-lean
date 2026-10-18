/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsScalarTilt
public import Balaban.Inhabited.DAPhysicalCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The margin of a polynomial threshold in the step radius, uniformly in the scale

The thresholds of the class chain are of the form `C (log b)^q ≤ t^a b^s` with `b = β 3^k`
(for example the Cauchy radius of the corrected marks needs `p₁³ ≤ c t³ √b`, i.e. `a = 3`,
`s = 1/2`, `q = 3p`; the amplitudes need `a = 1` or `2`).  For the radii `t_k ≥ c 3^{-α (k+1)}`
of `exists_stepTower_room` with `ε_j ∝ 3^{-α j}`:

* `exists_beta0_margin`: if `a α < s`, one `β₀` (depending on `a, s, α, c, C, q` only) gives
  `C (log (β 3^k))^q ≤ t^a (β 3^k)^s` for every `k`, every `β ≥ β₀` and every `t ≥ c 3^{-α(k+1)}`.
  The margin is `3^{(s - aα) k}`.
* `exists_beta0_margin_pLog`: the same for `C p₁^m ≤ t^a b^s` with `p₁ ≤ pLog A₁ p b`.
-/

@[expose] public section

namespace Balaban.Inhabited

private theorem margin_pow_le_exp {q : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    ∃ M : ℝ, 0 < M ∧ ∀ k : ℕ, (k : ℝ) ^ q ≤ M * (3 : ℝ) ^ (γ * (k : ℝ)) := by
  have hr : 1 < (3 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  obtain ⟨M, hM⟩ := (tendsto_pow_const_div_const_pow_of_one_lt q hr).bddAbove_range
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun k => ?_⟩
  have h1 : (k : ℝ) ^ q / ((3 : ℝ) ^ γ) ^ k ≤ M := hM ⟨k, rfl⟩
  have h2 : ((3 : ℝ) ^ γ) ^ k = (3 : ℝ) ^ (γ * (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [h2] at h1
  have hp : 0 < (3 : ℝ) ^ (γ * (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_le_iff₀ hp] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)

private theorem margin_add_pow_le (q : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ q ≤ 2 ^ q * (x ^ q + y ^ q) := by
  have hxq : 0 ≤ x ^ q := pow_nonneg hx q
  have hyq : 0 ≤ y ^ q := pow_nonneg hy q
  have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
  rcases le_total x y with h | h
  · calc (x + y) ^ q ≤ (2 * y) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * y ^ q := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h2
  · calc (x + y) ^ q ≤ (2 * x) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * x ^ q := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) h2

/-- **The margin of a polynomial threshold in the step radius.**  If `a α < s`, then for
`C ≥ 0`, `c > 0` and `q : ℕ` there is `β₀ ≥ 3`, depending on `a, s, α, c, C, q` only, with
`C (log (β 3^k))^q ≤ t^a (β 3^k)^s` for every `k`, every `β ≥ β₀` and every `t ≥ c 3^{-α (k+1)}`. -/
theorem exists_beta0_margin {a s α c C : ℝ} (q : ℕ) (hc : 0 < c) (ha : 0 ≤ a) (hs : 0 < s)
    (hγ : a * α < s) (hC : 0 ≤ C) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (k : ℕ) (β t : ℝ), β₀ ≤ β →
      c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t →
      C * Real.log (β * 3 ^ k) ^ q ≤ t ^ a * (β * 3 ^ k) ^ s := by
  set γ : ℝ := s - a * α with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  obtain ⟨M, hM0, hM⟩ := margin_pow_le_exp (q := q) hγ0
  set K : ℝ := c ^ a * (3 : ℝ) ^ (-(a * α)) with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  have hCq : 0 < C * 2 ^ q + 1 := by positivity
  obtain ⟨B₁, hB₁, hB₁'⟩ := Balaban.Fluctuation.exists_log_rpow_le (q : ℝ) (K / (2 * (C * 2 ^ q + 1))) s hs
    (by positivity)
  set D : ℝ := 2 * C * 2 ^ q * (Real.log 3) ^ q * M / K with hD
  have hD0 : 0 ≤ D := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    rw [hD]; positivity
  set B₂ : ℝ := (max D 1) ^ (1 / s) with hB₂
  have hB₂1 : 1 ≤ B₂ := Real.one_le_rpow (le_max_right _ _) (by positivity)
  refine ⟨max 3 (max B₁ B₂), le_max_left _ _, fun k β t hβ ht => ?_⟩
  have hβ3 : 3 ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : B₁ ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβ2 : B₂ ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ0 : 0 < β := by linarith
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hc3 : 0 < c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le hc3 ht
  -- lower bound of the right side
  have hta : (c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1)))) ^ a ≤ t ^ a :=
    Real.rpow_le_rpow hc3.le ht ha
  have e1 : (c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1)))) ^ a =
      c ^ a * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1)) * a) := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul (by norm_num)]
  have e2 : (β * 3 ^ k) ^ s = β ^ s * (3 : ℝ) ^ (s * (k : ℝ)) := by
    rw [Real.mul_rpow hβ0.le h3k.le, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      mul_comm (k : ℝ) s]
  have e3 : (3 : ℝ) ^ (-(α * ((k : ℝ) + 1)) * a) * (3 : ℝ) ^ (s * (k : ℝ)) =
      (3 : ℝ) ^ (-(a * α)) * (3 : ℝ) ^ (γ * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    rw [hγdef]; ring
  have hrhs : K * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) ≤ t ^ a * (β * 3 ^ k) ^ s := by
    have hbs : 0 ≤ (β * 3 ^ k) ^ s := Real.rpow_nonneg hb0.le _
    calc K * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) =
        (c ^ a * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1)) * a)) * (β * 3 ^ k) ^ s := by
          rw [e2, hK]
          calc c ^ a * (3 : ℝ) ^ (-(a * α)) * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) =
              c ^ a * (((3 : ℝ) ^ (-(a * α)) * (3 : ℝ) ^ (γ * (k : ℝ))) * β ^ s) := by ring
            _ = c ^ a * (((3 : ℝ) ^ (-(α * ((k : ℝ) + 1)) * a) * (3 : ℝ) ^ (s * (k : ℝ))) *
                β ^ s) := by rw [e3]
            _ = _ := by ring
      _ = (c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1)))) ^ a * (β * 3 ^ k) ^ s := by rw [e1]
      _ ≤ _ := mul_le_mul_of_nonneg_right hta hbs
  refine le_trans ?_ hrhs
  -- the logarithm
  have hlog : Real.log (β * 3 ^ k) = Real.log β + (k : ℝ) * Real.log 3 := by
    rw [Real.log_mul hβ0.ne' h3k.ne', Real.log_pow]
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlb : 0 ≤ Real.log β := Real.log_nonneg (by linarith)
  have hsplit := margin_add_pow_le q hlb (mul_nonneg (Nat.cast_nonneg k) hl3)
  rw [← hlog] at hsplit
  have hβs : 0 < β ^ s := Real.rpow_pos_of_pos hβ0 _
  have hg1 : (1 : ℝ) ≤ (3 : ℝ) ^ (γ * (k : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hg0 : 0 < (3 : ℝ) ^ (γ * (k : ℝ)) := by linarith
  -- first part
  have hp1 : Real.log β ^ q ≤ K / (2 * (C * 2 ^ q + 1)) * β ^ s := by
    have := hB₁' β hβ1
    rwa [Real.rpow_natCast] at this
  have hp1' : C * 2 ^ q * Real.log β ^ q ≤ K / 2 * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) := by
    have hCnn : 0 ≤ C * 2 ^ q := by positivity
    calc C * 2 ^ q * Real.log β ^ q ≤ C * 2 ^ q * (K / (2 * (C * 2 ^ q + 1)) * β ^ s) :=
          mul_le_mul_of_nonneg_left hp1 hCnn
      _ = (C * 2 ^ q / (C * 2 ^ q + 1)) * (K / 2 * β ^ s) := by
          field_simp
      _ ≤ 1 * (K / 2 * β ^ s) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = K / 2 * β ^ s := one_mul _
      _ ≤ K / 2 * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith
  -- second part
  have hBs : D ≤ β ^ s := by
    have h1 : B₂ ^ s ≤ β ^ s := Real.rpow_le_rpow (by linarith) hβ2 hs.le
    have h2 : B₂ ^ s = max D 1 := by
      rw [hB₂, ← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
    rw [h2] at h1
    exact (le_max_left _ _).trans h1
  have hp2 : C * 2 ^ q * ((k : ℝ) * Real.log 3) ^ q ≤
      K / 2 * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) := by
    have h1 : ((k : ℝ) * Real.log 3) ^ q ≤ (Real.log 3) ^ q * M * (3 : ℝ) ^ (γ * (k : ℝ)) := by
      rw [mul_pow]
      calc (k : ℝ) ^ q * Real.log 3 ^ q ≤ M * (3 : ℝ) ^ (γ * (k : ℝ)) * Real.log 3 ^ q :=
            mul_le_mul_of_nonneg_right (hM k) (by positivity)
        _ = _ := by ring
    have hCnn : 0 ≤ C * 2 ^ q := by positivity
    calc C * 2 ^ q * ((k : ℝ) * Real.log 3) ^ q ≤
          C * 2 ^ q * ((Real.log 3) ^ q * M * (3 : ℝ) ^ (γ * (k : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hCnn
      _ = K / 2 * (D * (3 : ℝ) ^ (γ * (k : ℝ))) := by
          rw [hD]; field_simp
      _ ≤ K / 2 * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hBs hg0.le
  calc C * Real.log (β * 3 ^ k) ^ q ≤ C * (2 ^ q * (Real.log β ^ q +
        ((k : ℝ) * Real.log 3) ^ q)) := mul_le_mul_of_nonneg_left hsplit hC
    _ = C * 2 ^ q * Real.log β ^ q + C * 2 ^ q * ((k : ℝ) * Real.log 3) ^ q := by ring
    _ ≤ K / 2 * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) +
        K / 2 * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) := add_le_add hp1' hp2
    _ = K * (β ^ s * (3 : ℝ) ^ (γ * (k : ℝ))) := by ring

/-- **The margin for a cutoff `p₁ ≤ pLog A₁ p b`.**  Under the hypotheses of `exists_beta0_margin`
(with `q = p m`), `C p₁^m ≤ t^a (β 3^k)^s` for `0 < p₁ ≤ pLog A₁ p (β 3^k)`. -/
theorem exists_beta0_margin_pLog {a s α c C A₁ : ℝ} (p m : ℕ) (hc : 0 < c) (ha : 0 ≤ a)
    (hs : 0 < s) (hγ : a * α < s) (hC : 0 ≤ C) (hA : 0 ≤ A₁) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (k : ℕ) (β t p₁ : ℝ), β₀ ≤ β →
      c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t → 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      C * p₁ ^ m ≤ t ^ a * (β * 3 ^ k) ^ s := by
  obtain ⟨β₀, h3, H⟩ := exists_beta0_margin (a := a) (s := s) (α := α) (c := c)
    (C := C * A₁ ^ m) (p * m) hc ha hs hγ (by positivity)
  refine ⟨β₀, h3, fun k β t p₁ hβ ht hp hp₁ => ?_⟩
  refine le_trans ?_ (H k β t hβ ht)
  have h0 : p₁ ^ m ≤ (A₁ * Real.log (β * 3 ^ k) ^ p) ^ m := pow_le_pow_left₀ hp.le hp₁ m
  have e : (A₁ * Real.log (β * 3 ^ k) ^ p) ^ m = A₁ ^ m * Real.log (β * 3 ^ k) ^ (p * m) := by
    rw [mul_pow, ← pow_mul]
  calc C * p₁ ^ m ≤ C * (A₁ ^ m * Real.log (β * 3 ^ k) ^ (p * m)) := by
        refine mul_le_mul_of_nonneg_left (h0.trans (le_of_eq e)) hC
    _ = _ := by ring

end Balaban.Inhabited
