/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormLocal
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The rotated frame of the data (Step 2 of SMALLFIELD.md §2.3)

For `(ψ, b)` with `‖ψ(0)·ψ(0) - 1‖ ≤ σ²ε ≤ 1/4`:

* `exists_sqrt`: a square root `u` of `ψ(0)·ψ(0)` with `‖u - 1‖ ≤ σ²ε`;
* `exists_frame`: a complex orthogonal `R` with bounded entries and `R ψ(0) = u e_{i₀}`;
* `dot_mulVec_rot`: the bilinear form is invariant under `R`;
* `long_identity`: `2 u φ₀ + φ₀² + θ = g(x) - g(0)` for the rotated differences `φ`.
-/

@[expose] public section

open Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem exists_sqrt (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / 4) :
    ∃ u : ℂ, u * u = z ∧ ‖u - 1‖ ≤ ‖z - 1‖ ∧ ‖u - 1‖ ≤ 1 / 4 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 2)
  obtain ⟨u, hu, hre⟩ : ∃ u : ℂ, u * u = z ∧ 0 ≤ u.re := by
    by_cases h : 0 ≤ w.re
    · exact ⟨w, by rw [← hw]; ring, h⟩
    · exact ⟨-w, by rw [← hw]; ring, by simp; linarith [not_le.mp h]⟩
  have h1 : 1 ≤ ‖u + 1‖ := by
    calc (1 : ℝ) ≤ (u + 1).re := by simp; linarith
      _ ≤ ‖u + 1‖ := Complex.re_le_norm _
  have h2 : ‖u - 1‖ ≤ ‖z - 1‖ := by
    have : z - 1 = (u - 1) * (u + 1) := by rw [← hu]; ring
    rw [this, norm_mul]
    nlinarith [norm_nonneg (u - 1)]
  exact ⟨u, hu, h2, h2.trans hz⟩

theorem dot_mulVec_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (v w : Spin N) :
    dot (R.mulVec v) (R.mulVec w) = dot v w := by
  have : dot (R.mulVec v) (R.mulVec w) = (R.mulVec v) ⬝ᵥ (R.mulVec w) := rfl
  rw [this, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
  unfold IsOrth at hR
  rw [hR, Matrix.one_mulVec]
  rfl

theorem norm_mulVec_le {R : Matrix (Fin N) (Fin N) ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i k, ‖R i k‖ ≤ B) (v : Spin N) : ‖R.mulVec v‖ ≤ N * B * ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ k, R i k * v k‖ ≤ ∑ k, ‖R i k * v k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, B * ‖v‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact mul_le_mul (hB i k) (norm_le_pi_norm v k) (norm_nonneg _) hB0
    _ = N * B * ‖v‖ := by simp; ring

theorem pack_add (X : Finset (Site d)) (ψ ψ' : Site d → Spin N) (b b' : Spin N) :
    pack X (fun x => ψ x + ψ' x) (b + b') = pack X ψ b + pack X ψ' b' := by
  ext (p | i) <;> simp [pack]

theorem pack_sub (X : Finset (Site d)) (ψ ψ' : Site d → Spin N) (b b' : Spin N) :
    pack X (fun x => ψ x - ψ' x) (b - b') = pack X ψ b - pack X ψ' b' := by
  ext (p | i) <;> simp [pack]

/-- The frame: a square root `u` of `ψ(0)·ψ(0)` and a rotation taking `ψ(0)` to `u e_{i₀}`. -/
structure Frame (i₀ : Fin N) (σ ε : ℝ) (ψ : Site d → Spin N) (u : ℂ)
    (R : Matrix (Fin N) (Fin N) ℂ) : Prop where
  orth : IsOrth R
  bd : EntryBd N R
  u_sq : u * u = dot (ψ 0) (ψ 0)
  u_close : ‖u - 1‖ ≤ σ ^ 2 * ε
  rot0 : R.mulVec (ψ 0) = u • (Pi.single i₀ 1 : Spin N)

theorem exists_frame (i₀ : Fin N) {Dom : Set ((Site d → Spin N) × Spin N)} {ν σ ε K₂ : ℝ}
    {ψ : Site d → Spin N} {b : Spin N} (dat : DataHyp Dom ν σ ε K₂ ψ b)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) : ∃ (u : ℂ) (R : Matrix (Fin N) (Fin N) ℂ), Frame i₀ σ ε ψ u R := by
  obtain ⟨u, hu, hu1, hu2⟩ := exists_sqrt (dot (ψ 0) (ψ 0)) ((dat.sq 0).trans hτ)
  obtain ⟨R, hR, hRb, hRp⟩ := exists_normalizing_rot i₀ (p := ψ 0)
    (fun k => (norm_le_pi_norm (ψ 0) k).trans dat.bdd0) hu hu2
  exact ⟨u, R, ⟨hR, hRb, hu, hu1.trans (dat.sq 0), hRp⟩⟩

variable {i₀ : Fin N}

theorem Frame.long_identity {σ ε : ℝ} {ψ : Site d → Spin N} {u : ℂ}
    {R : Matrix (Fin N) (Fin N) ℂ} (hF : Frame i₀ σ ε ψ u R) (x : Site d) :
    2 * u * (R.mulVec (ψ x - ψ 0)) i₀ + ((R.mulVec (ψ x - ψ 0)) i₀) ^ 2 +
        dotT i₀ (R.mulVec (ψ x - ψ 0)) (R.mulVec (ψ x - ψ 0)) =
      dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0) := by
  set φ := R.mulVec (ψ x - ψ 0) with hφ
  have h1 : R.mulVec (ψ x) = u • (Pi.single i₀ 1 : Spin N) + φ := by
    rw [hφ, Matrix.mulVec_sub, ← hF.rot0]; abel
  have h2 := dot_mulVec_rot hF.orth (ψ x) (ψ x)
  rw [h1] at h2
  have h3 : dot (u • (Pi.single i₀ 1 : Spin N) + φ) (u • (Pi.single i₀ 1 : Spin N) + φ) =
      u * u + 2 * u * φ i₀ + (φ i₀ ^ 2 + dotT i₀ φ φ) := by
    simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, dot_single_left,
      dot_single_right]
    have : dot φ φ = φ i₀ ^ 2 + dotT i₀ φ φ := by
      unfold dot dotT
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]; ring
    rw [this]; simp; ring
  rw [h3, hF.u_sq] at h2
  linear_combination h2

/-- Solving the longitudinal identity `2 u φ₀ + φ₀² + θ = g`. -/
theorem long_bounds {u φ0 θ g : ℂ} {τ T : ℝ} (hu : ‖u - 1‖ ≤ τ) (hτ : τ ≤ 1 / 4)
    (hg : ‖g‖ ≤ 2 * τ) (hθ : ‖θ‖ ≤ T) (hφ : ‖φ0‖ ≤ 1 / 2)
    (hid : 2 * u * φ0 + φ0 ^ 2 + θ = g) :
    ‖φ0‖ ≤ 2 * τ + T ∧ ‖φ0 - g / 2 + θ / 2‖ ≤ (2 * τ + T) * τ + (2 * τ + T) ^ 2 := by
  have hun : 3 / 4 ≤ ‖u‖ := by
    have := norm_sub_norm_le (1 : ℂ) u
    rw [norm_sub_rev] at this
    simp at this; linarith
  have hu0 : u ≠ 0 := by intro h; rw [h] at hun; simp at hun; linarith
  have hT0 : 0 ≤ T := le_trans (norm_nonneg _) hθ
  have hτ0 : 0 ≤ τ := le_trans (norm_nonneg _) hu
  have h2 : 1 ≤ ‖2 * u + φ0‖ := by
    have := norm_sub_norm_le (2 * u) (-φ0)
    rw [norm_neg, sub_neg_eq_add] at this
    have h2u : ‖2 * u‖ = 2 * ‖u‖ := by simp
    linarith
  have hF : ‖φ0‖ ≤ 2 * τ + T := by
    have e : φ0 * (2 * u + φ0) = g - θ := by linear_combination hid
    have : ‖φ0‖ * 1 ≤ ‖φ0‖ * ‖2 * u + φ0‖ := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    rw [← norm_mul, e] at this
    calc ‖φ0‖ ≤ ‖g - θ‖ := by linarith
      _ ≤ ‖g‖ + ‖θ‖ := norm_sub_le _ _
      _ ≤ 2 * τ + T := by linarith
  refine ⟨hF, ?_⟩
  have e : φ0 - g / 2 + θ / 2 = (g - θ) * ((1 - u) / (2 * u)) - φ0 ^ 2 / (2 * u) := by
    field_simp
    linear_combination hid
  rw [e]
  have h2u : ‖2 * u‖ ≥ 3 / 2 := by
    have : ‖2 * u‖ = 2 * ‖u‖ := by simp
    linarith
  have hinv : ‖(1 : ℂ) / (2 * u)‖ ≤ 2 / 3 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have t1 : ‖(g - θ) * ((1 - u) / (2 * u))‖ ≤ (2 * τ + T) * τ := by
    rw [norm_mul, show (1 - u) / (2 * u) = (1 - u) * (1 / (2 * u)) by ring, norm_mul]
    have h1u : ‖1 - u‖ ≤ τ := by rw [norm_sub_rev]; exact hu
    have : ‖g - θ‖ ≤ 2 * τ + T := (norm_sub_le _ _).trans (by linarith)
    calc ‖g - θ‖ * (‖1 - u‖ * ‖(1 : ℂ) / (2 * u)‖) ≤ (2 * τ + T) * (τ * 1) :=
          mul_le_mul this (mul_le_mul h1u (hinv.trans (by norm_num)) (norm_nonneg _) hτ0)
            (by positivity) (by positivity)
      _ = _ := by ring
  have t2 : ‖φ0 ^ 2 / (2 * u)‖ ≤ (2 * τ + T) ^ 2 := by
    rw [div_eq_mul_one_div, norm_mul, norm_pow]
    calc ‖φ0‖ ^ 2 * ‖(1 : ℂ) / (2 * u)‖ ≤ (2 * τ + T) ^ 2 * 1 :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hF 2) (hinv.trans (by norm_num))
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact (norm_sub_le _ _).trans (add_le_add t1 t2)

end Balaban.SmallField
