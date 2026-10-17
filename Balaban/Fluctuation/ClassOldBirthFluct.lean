/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldBirthDelta
public import Balaban.Fluctuation.ScaleUniform
import Mathlib.Tactic.Positivity

/-!
# The fluctuation radius `δ₁` is a small multiple of `ε_k`

The fluctuation chart asks `√N ‖cc‖ C c_ψ < δ₁` (`C = covSupConstC`).  The amplitude is
`‖cc‖ ≤ β_k^{-1/2}` and the cutoff is `c_ψ = A₁ (log β_k)^p`.  Since `(log x)^p ≤ (p/u)^p x^u`,
the product is at most `A₁ (p/u)^p β_k^{-(1/2-u)}`.  With `β_k ≥ M L^{(d-2)k}` and
`α ≤ (d-2)(1/2-u)` this is at most `A₁ (p/u)^p M^{-(1/2-u)} L^{-αk} ≤ A₁ (p/u)^p M^{-(1/2-u)} ε_k/α₀`,
so the choice `δ₁ = 2 √N ‖cc‖ C c_ψ` satisfies `δ₁ ≤ c_δ ε_k` as soon as
`2 √N C A₁ (p/u)^p ≤ c_δ α₀ M^{1/2-u}`, a lower bound on `M ≍ β`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField

/-- `(log x)^p ≤ (p/u)^p x^u` for `x ≥ 1`, `u > 0`, `p ≥ 1`. -/
theorem log_pow_le_rpow {x u : ℝ} {p : ℕ} (hx : 1 ≤ x) (hu : 0 < u) (hp : 1 ≤ p) :
    Real.log x ^ p ≤ ((p : ℝ) / u) ^ p * x ^ u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have ht : 0 < u / p := by positivity
  have h1 := Real.log_le_rpow_div (by linarith : 0 ≤ x) ht
  have h0 := Real.log_nonneg hx
  calc Real.log x ^ p ≤ (x ^ (u / p) / (u / p)) ^ p := pow_le_pow_left₀ h0 h1 p
    _ = ((p : ℝ) / u) ^ p * x ^ u := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        have : u / p * p = u := by field_simp
        rw [this, div_eq_mul_inv, ← inv_pow, inv_div]
        ring

/-- **The amplitude product is at most `K L^{-αk}`.** -/
theorem amp_le_decay {d L k : ℕ} [NeZero L] {α u A₁ C βk M : ℝ} {p : ℕ} {cc : ℂ} {cψ : ℝ}
    (hL : 1 ≤ (L : ℝ)) (hp : 1 ≤ p) (hu : 0 < u) (hu2 : u < 1 / 2) (hA₁ : 0 ≤ A₁) (hC : 0 ≤ C)
    (hM : 1 < M) (hβk : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk)
    (hcc : ‖cc‖ ≤ βk ^ (-(1 / 2 : ℝ))) (hcψ : cψ = A₁ * Real.log βk ^ p)
    (hαu : α ≤ ((d : ℝ) - 2) * (1 / 2 - u)) (hd : 2 ≤ d) :
    ‖cc‖ * (C * cψ) ≤ C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k) := by
  have hR : 1 ≤ (L : ℝ) ^ (((d : ℝ) - 2) * k) := by
    apply Real.one_le_rpow hL
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hR0 : 0 < (L : ℝ) ^ (((d : ℝ) - 2) * k) := by linarith
  have hM0 : 0 < M := by linarith
  have hβ1 : 1 ≤ βk := by nlinarith
  have hβ0 : 0 < βk := by linarith
  have hq : 0 < 1 / 2 - u := by linarith
  have hlog := log_pow_le_rpow hβ1 hu hp
  -- ‖cc‖ * cψ ≤ A₁ (p/u)^p βk^{-(1/2-u)}
  have h1 : ‖cc‖ * cψ ≤ A₁ * ((p : ℝ) / u) ^ p * βk ^ (-(1 / 2 - u)) := by
    rw [hcψ]
    calc ‖cc‖ * (A₁ * Real.log βk ^ p) ≤ βk ^ (-(1 / 2 : ℝ)) * (A₁ * (((p : ℝ) / u) ^ p * βk ^ u)) :=
          mul_le_mul hcc (mul_le_mul_of_nonneg_left hlog hA₁) (mul_nonneg hA₁ (pow_nonneg (Real.log_nonneg hβ1) _)) (by positivity)
      _ = A₁ * ((p : ℝ) / u) ^ p * βk ^ (-(1 / 2 - u)) := by
          have : βk ^ (-(1 / 2 : ℝ)) * βk ^ u = βk ^ (-(1 / 2 - u)) := by
            rw [← Real.rpow_add hβ0]; ring_nf
          rw [← this]; ring
  have h2 : βk ^ (-(1 / 2 - u)) ≤ M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k) := by
    have e1 : βk ^ (-(1 / 2 - u)) ≤ (M * (L : ℝ) ^ (((d : ℝ) - 2) * k)) ^ (-(1 / 2 - u)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hβk (by linarith)
    rw [Real.mul_rpow hM0.le hR0.le, ← Real.rpow_mul (by linarith)] at e1
    refine e1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le hL
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  calc ‖cc‖ * (C * cψ) = C * (‖cc‖ * cψ) := by ring
    _ ≤ C * (A₁ * ((p : ℝ) / u) ^ p * βk ^ (-(1 / 2 - u))) := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * (A₁ * ((p : ℝ) / u) ^ p * (M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem one_le_epsTail (j : ℕ) : 1 ≤ epsTail j := by
  unfold epsTail
  have : 0 ≤ ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
    tsum_nonneg fun m => by split_ifs <;> positivity
  linarith

/-- **`δ₁ = 2 √N ‖cc‖ C c_ψ` is admissible and at most `c_δ ε_k`.**  Conditions: `L ≥ 1`, `p ≥ 1`,
`0 < u < 1/2`, `‖cc‖ ≤ β_k^{-1/2}`, `c_ψ = A₁ (log β_k)^p`, `β_k ≥ M L^{(d-2)k}`, `M > 1`,
`α ≤ (d-2)(1/2-u)`, and the single size condition `2 √N C A₁ (p/u)^p ≤ c_δ α₀ M^{1/2-u}`
(a lower bound on `M`, that is on `β`).  Here `W = √N ‖cc‖ C c_ψ > 0` is the hypothesis of the
fluctuation chart, and `δ₁` is any number with `δ₁ = 2 W`. -/
theorem delta1_le_of_amp {d L k N : ℕ} [NeZero L] {α α₀ u A₁ C βk M cδ δ₁ : ℝ} {p : ℕ} {cc : ℂ}
    {cψ : ℝ}
    (hL : 1 ≤ (L : ℝ)) (hp : 1 ≤ p) (hu : 0 < u) (hu2 : u < 1 / 2) (hA₁ : 0 ≤ A₁) (hC : 0 ≤ C)
    (hM : 1 < M) (hβk : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk)
    (hcc : ‖cc‖ ≤ βk ^ (-(1 / 2 : ℝ))) (hcψ : cψ = A₁ * Real.log βk ^ p)
    (hαu : α ≤ ((d : ℝ) - 2) * (1 / 2 - u)) (hd : 2 ≤ d) (hα₀ : 0 ≤ α₀) (hcδ : 0 ≤ cδ)
    (hsize : 2 * Real.sqrt N * C * A₁ * ((p : ℝ) / u) ^ p ≤ cδ * α₀ * M ^ (1 / 2 - u))
    (hW : 0 < Real.sqrt N * (‖cc‖ * (C * cψ)))
    (hδ₁ : δ₁ = 2 * (Real.sqrt N * (‖cc‖ * (C * cψ)))) :
    Real.sqrt N * (‖cc‖ * (C * cψ)) < δ₁ ∧ 0 ≤ δ₁ ∧ δ₁ ≤ cδ * epsSeq L α α₀ k := by
  refine ⟨by rw [hδ₁]; linarith, by rw [hδ₁]; linarith, ?_⟩
  have h := amp_le_decay (d := d) (L := L) (k := k) (u := u) (A₁ := A₁) (C := C) (M := M)
    hL hp hu hu2 hA₁ hC hM hβk hcc hcψ hαu hd
  have hM0 : 0 < M := by linarith
  have hMq : 0 < M ^ (1 / 2 - u) := Real.rpow_pos_of_pos hM0 _
  have hEq : (L : ℝ) ^ (-α * k) = ((L : ℝ) ^ (-α)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  have hE0 : 0 ≤ ((L : ℝ) ^ (-α)) ^ k := by positivity
  have hneg : M ^ (-(1 / 2 - u)) = (M ^ (1 / 2 - u))⁻¹ := Real.rpow_neg hM0.le _
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hK : 2 * Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u))) ≤ cδ * α₀ := by
    rw [hneg]
    have : 2 * Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * (M ^ (1 / 2 - u))⁻¹) =
        (2 * Real.sqrt N * C * A₁ * ((p : ℝ) / u) ^ p) / M ^ (1 / 2 - u) := by
      field_simp
    rw [this, div_le_iff₀ hMq]
    exact hsize
  have hep : α₀ * ((L : ℝ) ^ (-α)) ^ k ≤ epsSeq L α α₀ k := by
    unfold epsSeq
    have := one_le_epsTail k
    nlinarith [mul_nonneg hα₀ hE0]
  rw [hδ₁]
  calc 2 * (Real.sqrt N * (‖cc‖ * (C * cψ)))
      ≤ 2 * (Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k))) := by
        gcongr
    _ = (2 * Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u)))) * ((L : ℝ) ^ (-α * k)) := by
        ring
    _ ≤ (cδ * α₀) * ((L : ℝ) ^ (-α * k)) := by
        rw [hEq]; exact mul_le_mul_of_nonneg_right hK hE0
    _ = cδ * (α₀ * ((L : ℝ) ^ (-α)) ^ k) := by rw [hEq]; ring
    _ ≤ cδ * epsSeq L α α₀ k := mul_le_mul_of_nonneg_left hep hcδ

end Balaban.Fluctuation
