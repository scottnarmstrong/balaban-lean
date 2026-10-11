module

public import Balaban.Green.LimitCauchy
public import Balaban.Green.MassLipschitz
public import Balaban.Green.CoarseOperator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Limits of the fine Green function

Crude (constants depending on `d, L, k`) properties of `H⁻¹`, `H = fineHamiltonian d (M L^k) (L^k) M ν a`
(`-N²Δ + ν + a P` on the torus of side `M L^k`, `N = L^k`), used for the infinite-volume limit
(G1) and the limit `μ ↓ 0` (G3) of the Gaussian kernels:

* `fineGreen_decay`: Combes--Thomas decay of `H⁻¹`, uniformly in `M` and `ν ∈ [0, 1]`;
* `fineGreen_lipschitz`: `|H(ν₁)⁻¹(x, y) - H(ν₂)⁻¹(x, y)| ≤ Λ |ν₁ - ν₂|`, uniformly in `M, x, y`;
* `fineGreen_cauchy_coarse`: the entries at sites of `ℤ^d` are Cauchy as the coarse side `M → ∞`
  (the landed `fineGreen_cauchy` is for the coarse side `L (j+1)` only).
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban

section Decay

variable {d L : ℕ} [NeZero L]

/-- Crude exponential decay of the inverse of the fine operator (Combes--Thomas), with constants
depending on `d, L, k` only. -/
theorem fineGreen_decay (hd : 0 < d) (k : ℕ) :
    ∃ c ρ : ℝ, 0 ≤ c ∧ 0 < ρ ∧ ∀ {N₀ : ℕ} [NeZero N₀] {ν a : ℝ}, 0 ≤ ν → ν ≤ 1 → 1 / 2 ≤ a →
      a ≤ 2 → ∀ x y : Torus d (N₀ * L ^ k),
      |(fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ x y| ≤
        c * Real.exp (-ρ * torusDist d (N₀ * L ^ k) x y) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  set c₀ : ℝ := (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 1 + 2) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1)
    with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set γ₀ : ℝ := min (2 / (d : ℝ)) (1 / 2) with hγ₀
  have hγ : 0 < γ₀ := lt_min (by positivity) (by norm_num)
  set κ : ℝ := ballConst d (1 / 4) with hκdef
  have hκ : 0 ≤ κ := ballConst_nonneg (by norm_num)
  refine ⟨2 * γ₀⁻¹, ctRate c₀ 1 γ₀ κ, by positivity, ctRate_pos hc₀0 one_pos hγ hκ, ?_⟩
  intro N₀ _ ν a hν hν1 ha1 ha2 x y
  set A := fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a with hAdef
  have hcoer : IsCoercive (A.map (algebraMap ℝ ℂ)) γ₀ :=
    isCoercive_map_of_real A fun φ =>
      fineHamiltonian_coercive hd (mul_comm _ _) hN hν ha1 φ
  set Ac : Matrix (L1Torus d (N₀ * L ^ k)) (L1Torus d (N₀ * L ^ k)) ℂ :=
    A.map (algebraMap ℝ ℂ) with hAc
  have hA : ∀ x y : L1Torus d (N₀ * L ^ k), ‖Ac x y‖ ≤ c₀ * Real.exp (-1 * dist x y) := by
    intro x y
    have h := fineHamiltonian_decay (L := L) (k := k) (N₀ := N₀) hν (by linarith) ha2 x y
    have e : ‖Ac x y‖ = |A x y| := by
      show ‖algebraMap ℝ ℂ (A x y)‖ = |A x y|
      simp
    rw [e, dist_L1Torus]
    refine h.trans ?_
    rw [hc₀]
    have : (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2) ≤ (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + 1 + 2) := by
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity)
      ) (by positivity)
  have hK : ∀ x : L1Torus d (N₀ * L ^ k), ∑ y, Real.exp (-(1 / 4) * dist x y) ≤ κ := fun x =>
    ballSum_L1Torus d (N₀ * L ^ k) (by norm_num) x
  obtain ⟨hU, hb⟩ := combesThomas hc₀0 one_pos hγ hκ hA hK hcoer (t := 0) le_rfl
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hU hb
  have hinv : Ac⁻¹ = A⁻¹.map (algebraMap ℝ ℂ) := map_inv_real A hU
  have e2 : ‖Ac⁻¹ x y‖ = |A⁻¹ x y| := by
    rw [hinv]
    show ‖algebraMap ℝ ℂ (A⁻¹ x y)‖ = |A⁻¹ x y|
    simp
  have := hb x y
  rw [e2] at this
  exact this

/-- Lipschitz dependence of the fine Green function on the mass, uniformly in the torus. -/
theorem fineGreen_lipschitz (hd : 0 < d) (k : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ {N₀ : ℕ} [NeZero N₀] {ν₁ ν₂ a : ℝ}, 0 ≤ ν₁ → ν₁ ≤ 1 → 0 ≤ ν₂ → ν₂ ≤ 1 →
      1 / 2 ≤ a → a ≤ 2 → ∀ x y : Torus d (N₀ * L ^ k),
      |(fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ x y -
          (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹ x y| ≤ Λ * |ν₁ - ν₂| := by
  obtain ⟨c, ρ, hc, hρ, hdec⟩ := fineGreen_decay (L := L) hd k
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  refine ⟨c ^ 2 * ballConst d (ρ / 2), by
    have := ballConst_nonneg (d := d) (r := ρ / 2) (by positivity)
    positivity, ?_⟩
  intro N₀ _ ν₁ ν₂ a hν₁ hν₁1 hν₂ hν₂1 ha1 ha2 x y
  have h := congrFun (congrFun (inv_sub_inv (d := d) (ℓ := N₀ * L ^ k) (N := L ^ k) (m := N₀)
    (mul_comm _ _) hN hd hν₁ hν₂ (by linarith : 0 < a)) x) y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h
  rw [h, abs_mul, ← abs_neg (ν₂ - ν₁), neg_sub]
  have hsum : |∑ z, (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ x z *
      (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹ z y| ≤ c ^ 2 * ballConst d (ρ / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ z, |(fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ x z *
          (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹ z y|
        ≤ ∑ z : Torus d (N₀ * L ^ k), c ^ 2 * (Real.exp (-ρ * torusDist d (N₀ * L ^ k) x z) *
            Real.exp (-ρ * torusDist d (N₀ * L ^ k) z y)) := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [abs_mul]
          have h1 := hdec hν₁ hν₁1 ha1 ha2 x z
          have h2 := hdec hν₂ hν₂1 ha1 ha2 z y
          calc _ ≤ (c * Real.exp (-ρ * torusDist d (N₀ * L ^ k) x z)) *
                (c * Real.exp (-ρ * torusDist d (N₀ * L ^ k) z y)) :=
                mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
            _ = _ := by ring
      _ = c ^ 2 * ∑ z : Torus d (N₀ * L ^ k), (Real.exp (-ρ * torusDist d (N₀ * L ^ k) x z) *
            Real.exp (-ρ * torusDist d (N₀ * L ^ k) z y)) := by rw [Finset.mul_sum]
      _ ≤ c ^ 2 * (ballConst d (ρ / 2) * Real.exp (-(ρ / 2) * torusDist d (N₀ * L ^ k) x y)) :=
          mul_le_mul_of_nonneg_left (sum_exp_conv_le hρ x y) (by positivity)
      _ ≤ c ^ 2 * ballConst d (ρ / 2) := by
          have hb := ballConst_nonneg (d := d) (r := ρ / 2) (by positivity)
          have he : Real.exp (-(ρ / 2) * torusDist d (N₀ * L ^ k) x y) ≤ 1 :=
            Real.exp_le_one_iff.2 (by
              have := torusDist_nonneg_gen (d := d) x y
              nlinarith)
          calc _ ≤ c ^ 2 * (ballConst d (ρ / 2) * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hb) (by positivity)
            _ = _ := by ring
  calc |ν₁ - ν₂| * |∑ z, _| ≤ |ν₁ - ν₂| * (c ^ 2 * ballConst d (ρ / 2)) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := by ring

end Decay

section Cauchy

variable {d L : ℕ} [NeZero L]

/-- **Cauchy property of the fine Green function in the coarse side.** The entries of
`H⁻¹`, `H = -N²Δ + ν + a P` on the torus of side `(j+1) L^k` (coarse side `j + 1`), at the images
of sites of `ℤ^d`, form Cauchy sequences in `j`, uniformly on cubes. -/
theorem fineGreen_cauchy_coarse (hd : 0 < d) {k : ℕ} {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ u ∈ sqBox d R₀, ∀ u' ∈ sqBox d R₀,
      |(fineHamiltonian d ((j₁ + 1) * L ^ k) (L ^ k) (j₁ + 1) ν a)⁻¹
          (castTorus ((j₁ + 1) * L ^ k) u) (castTorus ((j₁ + 1) * L ^ k) u') -
        (fineHamiltonian d ((j₂ + 1) * L ^ k) (L ^ k) (j₂ + 1) ν a)⁻¹
          (castTorus ((j₂ + 1) * L ^ k) u) (castTorus ((j₂ + 1) * L ^ k) u')| ≤ η := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ : 0 < min (2 / (d : ℝ)) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hc : 0 ≤ (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1) :=
    by positivity
  have : ∀ j : ℕ, NeZero ((j + 1) * L ^ k) := fun j => inferInstance
  have hle : ∀ j : ℕ, j ≤ (j + 1) * L ^ k := fun j =>
    (Nat.le_succ j).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hL))
  refine cauchy_inv_entries (d := d) hc one_pos hγ (fun j => (j + 1) * L ^ k) hle
    (fun j => fineHamiltonian d ((j + 1) * L ^ k) (L ^ k) (j + 1) ν a) ?_ ?_ ?_ R₀ η hη
  · intro j x y
    have := fineHamiltonian_decay (N₀ := j + 1) (L := L) (k := k) hν (by linarith) ha2 x y
    simpa using this
  · intro j φ
    exact fineHamiltonian_coercive hd (mul_comm _ _) hN hν ha1 φ
  · intro R ε hε
    refine ⟨2 * R + 1, fun j₁ hj₁ j₂ hj₂ u hu u' hu' => ?_⟩
    have hm₁ : 2 * R + 1 < j₁ + 1 := by omega
    have hm₂ : 2 * R + 1 < j₂ + 1 := by omega
    rw [fineHamiltonian_castTorus (mul_comm _ _) hN hm₁ ν a hu hu',
      fineHamiltonian_castTorus (mul_comm _ _) hN hm₂ ν a hu hu', sub_self, abs_zero]
    exact hε.le

end Cauchy

end Balaban.Green
