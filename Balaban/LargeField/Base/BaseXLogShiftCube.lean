/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXLogShiftOps
public import Balaban.Localization.Decoupled2XBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The large-`x` expansion of the cube chain of the first step

At the first step (level one) and mass `ν + x`, the cube resolvent satisfies
`(T_q + x) G^{(q)}_x = c_q` with the cut Dirichlet operator `T_q` of the cube at mass `ν`, of
norm at most `ν + 4 d + 3` (`opNorm_cutOperator_le`).  Hence `x G^{(q)}_x c_q = c_q + O(1/x)` and
the first approximation `G*_{x,s} = Σ_q s_q χ_q G^{(q)}_x c_q` of the decoupled Green function
satisfies `x G*_{x,s} = σ_s + O(1/x)`, `σ_s = Σ_q s_q χ_q` (a diagonal multiplier), while
`𝒦_{x,s} = Σ_q s_q K^x_q G^{(q)}_x c_q = O(1/x)` (the commutators `K^x_q` are bounded by the
off-diagonal sums of the Dirichlet operator, and carry no mass).  This is the first-order content
needed for the shifted logarithm (`BaseXLogShift`, `notes/phase1/BASEX.md`).

* `cubeSigma`: the multiplier `σ_s = Σ_q s_q χ_q`;
* `cube_resid_sqNorm_le`: `‖x G^{(q)}_x g - c_q g‖ ≤ (ν + 4 d + 3) Γ⁻¹ ‖c_q g‖`, `Γ = L^{-2}/8 + x`;
* `sqNorm_cubeSum_le`: the overlap estimate for sums of vectors supported in the cubes;
* `opNorm_x_Gstarx_sub_sigma_le`, `opNorm_Kcalx_le`: `‖x G* - σ‖` and `‖𝒦‖` are `O(Γ⁻¹)`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Green Balaban.Multiscale Balaban.Localization
open scoped Matrix.Norms.L2Operator

section Defs

variable {d L N₁ m₁ : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The multiplier `σ_s = Σ_q s_q χ_q`** of the decoupling parameters of the cover of `G`: the
leading coefficient of the first approximation `G*_{x,s}` of the decoupled Green function at large
mass, `x G*_{x,s} → σ_s`.  At the physical point `s ≡ 1` it is the identity (`Σ_q χ_q = 1`). -/
noncomputable def cubeSigma (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ) : G.Ω 1 → ℂ := fun y =>
  ∑ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd s q * (((coverOf G).chi q y : ℝ) : ℂ)

/-- The spectral gap constant `L^{-2}/8` of the cube operators at level one. -/
noncomputable def cubeGap (L : ℕ) : ℝ := (1 / 8) * (((L : ℝ) ^ (0 + 1)) ^ 2)⁻¹

theorem cubeGap_pos (L : ℕ) [NeZero L] : 0 < cubeGap L := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold cubeGap; positivity

end Defs

section Cube

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}

/-- The cube operator at mass `ν + x` is the cut Dirichlet operator of the cube at mass `ν`
plus `x`. -/
theorem cubeHx_eq_cutOperator_add (hL : 2 ≤ L) (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    (q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1) :
    cubeHx G a aT 0 (ν + x) α q =
      cutOperator G a ν (cubeCut G (intBox q)) α + (x : ℂ) • (1 : Matrix (G.Ω 1) (G.Ω 1) ℂ) := by
  unfold cubeHx
  rw [cutXOperator_add_mass, cutXOperator_zero_eq_cutOperator G hL ha0 ha1 ha1' haT]

/-- **The residual of the cube resolvent**: `‖x G^{(q)}_x g - c_q g‖² ≤ b² Γ⁻² ‖c_q g‖²`, with
`b = ν + 4 d + 3` and `Γ = L^{-2}/8 + x`. -/
theorem cube_resid_sqNorm_le (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx) (hν : 0 ≤ ν)
    (hx : 0 ≤ x) (hα : AdmPot G α) (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1} (hq : q ∈ (coverOf G).cubeIdx)
    (g : G.Ω 1 → ℂ) :
    (cubeGap L + x) ^ 2 * sqNorm ((x : ℂ) • (cubeGx G a aT 0 (ν + x) α q *ᵥ g) - cD G q *ᵥ g) ≤
      (ν + 4 * d + 3) ^ 2 * sqNorm (cD G q *ᵥ g) := by
  have hL : 2 ≤ L := by have := S.hL; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set u := cubeGx G a aT 0 (ν + x) α q *ᵥ g with hu
  have hH := Dec2.cubeHx_cubeGx S hα (le_refl (0 : ℝ)) hq g
  rw [← hu, cubeHx_eq_cutOperator_add hL ha0 ha1 ha1' haT q, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec] at hH
  have hres : (x : ℂ) • u - cD G q *ᵥ g = -(cutOperator G a ν (cubeCut G (intBox q)) α *ᵥ u) := by
    rw [← hH]; abel
  have hα1 : ∀ z, ‖α z‖ ≤ 1 := by
    intro z
    refine (Dec2.AdmPot.le_eighth' S.hd hα z).trans ?_
    have hp : (1 : ℝ) ≤ G.spacing (z : Balaban.Localization.CTorus d L N₁ m₁ 1) := by
      obtain ⟨h1, h2, _⟩ := G.layerIndex_spec z.2
      have : G.layerIndex (z : Balaban.Localization.CTorus d L N₁ m₁ 1) = 1 := le_antisymm h2 h1
      rw [GeneratingSet.spacing, this, pow_one]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    rw [div_le_one (by positivity)]
    nlinarith
  have hT := opNorm_cutOperator_le G (cubeCut G (intBox q)) S.weights hν hα1
  have h1 := sqNorm_mulVec_le_opNorm (cutOperator G a ν (cubeCut G (intBox q)) α) u
  have h2 := cubeGx_sqNorm_le S (hν) hx hα hq g
  have h3 : sqNorm ((x : ℂ) • u - cD G q *ᵥ g) ≤ (ν + 4 * d + 3) ^ 2 * sqNorm u := by
    have hneg : ∀ v : G.Ω 1 → ℂ, sqNorm (-v) = sqNorm v := fun v => by simp [sqNorm]
    rw [hres, hneg]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (sqNorm_nonneg _))
    exact pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hΓ : (cubeGap L + x) ^ 2 * sqNorm u ≤ sqNorm (cD G q *ᵥ g) := by
    simpa [cubeGap] using h2
  calc (cubeGap L + x) ^ 2 * sqNorm ((x : ℂ) • u - cD G q *ᵥ g)
      ≤ (cubeGap L + x) ^ 2 * ((ν + 4 * d + 3) ^ 2 * sqNorm u) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = (ν + 4 * d + 3) ^ 2 * ((cubeGap L + x) ^ 2 * sqNorm u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hΓ (sq_nonneg _)

end Cube

section Sums

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}

/-- A site where `χ_q` does not vanish lies in the interaction cube of `q`. -/
theorem mem_intBox_of_chi_ne_zero (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1} (hq : q ∈ (coverOf G).cubeIdx)
    {y : G.Ω 1} (h : (coverOf G).chi q (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ≠ 0) :
    (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ intBox q :=
  (S.inner_near q hq y.2 h (Or.inr (SameCell.refl _ _))).self

/-- **The overlap estimate.**  If `F q` vanishes outside the interaction cube of `q` and
`‖F q‖² ≤ β² ‖c_q g‖²`, then `‖Σ_q F q‖² ≤ (3·5^d)² β² ‖g‖²`. -/
theorem sqNorm_cubeSum_le (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    {F : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → G.Ω 1 → ℂ}
    (hF : ∀ q ∈ (coverOf G).cubeIdx, ∀ y : G.Ω 1,
      (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ intBox q → F q y = 0)
    {β : ℝ} (g : G.Ω 1 → ℂ)
    (hFq : ∀ q ∈ (coverOf G).cubeIdx, sqNorm (F q) ≤ β ^ 2 * sqNorm (cD G q *ᵥ g)) :
    sqNorm (fun y => ∑ q ∈ (coverOf G).cubeIdx, F q y) ≤
      (3 * 5 ^ d : ℝ) ^ 2 * β ^ 2 * sqNorm g := by
  have hn0 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
  unfold sqNorm at *
  calc ∑ y, ‖∑ q ∈ (coverOf G).cubeIdx, F q y‖ ^ 2
      ≤ ∑ y : G.Ω 1, (3 * 5 ^ d : ℝ) * ∑ q ∈ (coverOf G).cubeIdx, ‖F q y‖ ^ 2 :=
        Finset.sum_le_sum fun y _ => Dec2.sq_norm_sum_overlap S hF y
    _ = (3 * 5 ^ d : ℝ) * ∑ q ∈ (coverOf G).cubeIdx, ∑ y, ‖F q y‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ (coverOf G).cubeIdx, β ^ 2 * ∑ y, ‖(cD G q *ᵥ g) y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq => hFq q hq) hn0
    _ = (3 * 5 ^ d : ℝ) * β ^ 2 * ∑ q ∈ (coverOf G).cubeIdx, ∑ y, ‖(cD G q *ᵥ g) y‖ ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ (3 * 5 ^ d : ℝ) * β ^ 2 * ((3 * 5 ^ d : ℝ) * ∑ y, ‖g y‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simpa [sqNorm] using sum_sqNorm_cD_le S g
    _ = _ := by ring

/-- The norm of the cube products. -/
theorem norm_sProd_le_exp (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hκ : 0 ≤ κ)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1}
    (hq : q ∈ (coverOf G).cubeIdx) : ‖(coverOf G).sProd s q‖ ≤ Real.exp (N0 d L * κ) :=
  (coverOf G).norm_sProd_le (S.card_qset q hq) hκ hs

/-- **The multiplier `σ_s` is bounded**: `|σ_s(y)| ≤ 3·5^d e^{N₀ κ}`. -/
theorem norm_cubeSigma_le (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hκ : 0 ≤ κ)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (y : G.Ω 1) :
    ‖cubeSigma G s y‖ ≤ (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) := by
  classical
  have hn0 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
  set e := Real.exp (N0 d L * κ) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set F : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → G.Ω 1 → ℂ := fun q y' =>
    (coverOf G).sProd s q * (((coverOf G).chi q y' : ℝ) : ℂ) with hF
  have hFs : ∀ q ∈ (coverOf G).cubeIdx, ∀ y' : G.Ω 1,
      (y' : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ intBox q → F q y' = 0 := by
    intro q hq y' hy'
    have : (coverOf G).chi q y' = 0 := by
      by_contra h; exact hy' (mem_intBox_of_chi_ne_zero S hq h)
    simp [hF, this]
  have h1 := Dec2.sq_norm_sum_overlap S hFs y
  have h2 : ∑ q ∈ (coverOf G).cubeIdx, ‖F q y‖ ^ 2 ≤ e ^ 2 * (3 * 5 ^ d : ℝ) := by
    calc ∑ q ∈ (coverOf G).cubeIdx, ‖F q y‖ ^ 2
        ≤ ∑ q ∈ (coverOf G).cubeIdx, (if (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ intBox q
          then e ^ 2 else 0) := by
          refine Finset.sum_le_sum fun q hq => ?_
          by_cases hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ intBox q
          · simp only [hy, ↓reduceIte]
            have hc := Dec2.chi_mem_Icc S hq y
            have hsp := norm_sProd_le_exp S hκ hs hq
            have : ‖F q y‖ ≤ e := by
              simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1]
              calc ‖(coverOf G).sProd s q‖ * (coverOf G).chi q y ≤ e * 1 :=
                    mul_le_mul hsp hc.2 hc.1 he0
                _ = e := mul_one e
            exact pow_le_pow_left₀ (norm_nonneg _) this 2
          · simp only [hy, ↓reduceIte]
            rw [hFs q hq y hy]; simp
      _ = e ^ 2 * (((coverOf G).cubeIdx.filter fun q =>
            (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ intBox q).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ e ^ 2 * (3 * 5 ^ d : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact_mod_cast Dec2.card_overlap_le S y
  have h3 : ‖cubeSigma G s y‖ ^ 2 ≤ ((3 * 5 ^ d : ℝ) * e) ^ 2 := by
    calc ‖cubeSigma G s y‖ ^ 2 = ‖∑ q ∈ (coverOf G).cubeIdx, F q y‖ ^ 2 := rfl
      _ ≤ (3 * 5 ^ d : ℝ) * ∑ q ∈ (coverOf G).cubeIdx, ‖F q y‖ ^ 2 := h1
      _ ≤ (3 * 5 ^ d : ℝ) * (e ^ 2 * (3 * 5 ^ d : ℝ)) := mul_le_mul_of_nonneg_left h2 hn0
      _ = _ := by ring
  exact le_of_sq_le_sq h3 (by positivity)

end Sums

section FirstOrder

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν x Cx κ : ℝ} {α : G.Ω 1 → ℂ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}

/-- **First order of the first approximation**: `‖x G*_{x,s} - σ_s‖ ≤ 3·5^d e^{N₀κ} (ν+4d+3) / Γ`,
`Γ = L^{-2}/8 + x`. -/
theorem opNorm_x_Gstarx_sub_sigma_le (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx)
    (hν : 0 ≤ ν) (hx : 0 ≤ x) (hκ : 0 ≤ κ) (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hα : AdmPot G α)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    ‖(x : ℂ) • Dec2.Gstarx (coverOf G) G a aT 0 (ν + x) α s - Matrix.diagonal (cubeSigma G s)‖ ≤
      (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * (ν + 4 * d + 3) / (cubeGap L + x) := by
  have hΓ : 0 < cubeGap L + x := by have := cubeGap_pos L; positivity
  set e := Real.exp (N0 d L * κ) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set b : ℝ := ν + 4 * d + 3 with hb
  have hb0 : 0 ≤ b := by positivity
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
  set v : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → G.Ω 1 → ℂ := fun q =>
    (x : ℂ) • (cubeGx G a aT 0 (ν + x) α q *ᵥ g) - cD G q *ᵥ g with hv
  set F : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → G.Ω 1 → ℂ := fun q y =>
    (coverOf G).sProd s q * (((coverOf G).chi q y : ℝ) * v q y) with hF
  have hFs : ∀ q ∈ (coverOf G).cubeIdx, ∀ y : G.Ω 1,
      (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ intBox q → F q y = 0 := by
    intro q hq y hy
    have : (coverOf G).chi q y = 0 := by
      by_contra h; exact hy (mem_intBox_of_chi_ne_zero S hq h)
    simp [hF, this]
  have hMg : ((x : ℂ) • Dec2.Gstarx (coverOf G) G a aT 0 (ν + x) α s -
      Matrix.diagonal (cubeSigma G s)) *ᵥ g = fun y => ∑ q ∈ (coverOf G).cubeIdx, F q y := by
    funext y
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply, Dec2.Gstarx_mulVec,
      Matrix.mulVec_diagonal, smul_eq_mul]
    unfold cubeSigma
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Dec2.chiD_mulVec]
    simp only [hF, hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : (coverOf G).chi q y = 0
    · simp [hc]
    · have hy := mem_intBox_of_chi_ne_zero S hq hc
      simp only [cD_mulVec, hy, ↓reduceIte]
      ring
  have hβ : ∀ q ∈ (coverOf G).cubeIdx, sqNorm (F q) ≤
      (e * b / (cubeGap L + x)) ^ 2 * sqNorm (cD G q *ᵥ g) := by
    intro q hq
    have h1 := cube_resid_sqNorm_le S hν hx hα ha0 ha1 ha1' haT hq g
    have hsp := norm_sProd_le_exp S hκ hs hq
    have hv1 : sqNorm (v q) ≤ b ^ 2 / (cubeGap L + x) ^ 2 * sqNorm (cD G q *ᵥ g) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith [h1]
    have hF1 : sqNorm (F q) ≤ e ^ 2 * sqNorm (v q) := by
      unfold sqNorm
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      have hc := Dec2.chi_mem_Icc S hq y
      have : ‖F q y‖ ≤ e * ‖v q y‖ := by
        simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1]
        calc ‖(coverOf G).sProd s q‖ * ((coverOf G).chi q y * ‖v q y‖)
            ≤ e * (1 * ‖v q y‖) :=
              mul_le_mul hsp (mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _))
                (by have := hc.1; positivity) he0
          _ = _ := by ring
      calc ‖F q y‖ ^ 2 ≤ (e * ‖v q y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = _ := by ring
    calc sqNorm (F q) ≤ e ^ 2 * sqNorm (v q) := hF1
      _ ≤ e ^ 2 * (b ^ 2 / (cubeGap L + x) ^ 2 * sqNorm (cD G q *ᵥ g)) :=
          mul_le_mul_of_nonneg_left hv1 (sq_nonneg _)
      _ = _ := by field_simp
  have := sqNorm_cubeSum_le S hFs g hβ
  rw [hMg]
  calc _ ≤ _ := this
    _ = _ := by field_simp

/-- **The commutator term decays**: `‖𝒦_{x,s}‖ ≤ 3·5^d e^{N₀κ} (2(4d+2)) / Γ`. -/
theorem opNorm_Kcalx_le (S : Dec2.XCover (coverOf G) G a aT (ν + x) Cx)
    (hν : 0 ≤ ν) (hx : 0 ≤ x) (hκ : 0 ≤ κ) (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hα : AdmPot G α)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    ‖Dec2.Kcalx (coverOf G) G a aT 0 (ν + x) α s‖ ≤
      (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) * (2 * (4 * d + 2)) / (cubeGap L + x) := by
  have hΓ : 0 < cubeGap L + x := by have := cubeGap_pos L; positivity
  have hL : 2 ≤ L := by have := S.hL; omega
  set e := Real.exp (N0 d L * κ) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set P : ℝ := 4 * d + 2 with hP
  have hP0 : 0 ≤ P := by positivity
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun g => ?_
  -- the commutator of the cube chain
  have hK : ∀ q ∈ (coverOf G).cubeIdx, ‖Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q‖ ≤ 2 * P := by
    intro q hq
    have hH : xDirichletOperator (k := 0) G a aT 0 (ν + x) 0 = dirichletOperator G a (ν + x) 0 :=
      xDirichletOperator_zero_eq_dirichletOperator G hL ha0 ha1 ha1' haT (ν + x) 0
    have hKe : Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q =
        Matrix.diagonal (fun y : G.Ω 1 => (((coverOf G).chi q y : ℝ) : ℂ)) *
            dirichletOperator G a (ν + x) 0 -
          dirichletOperator G a (ν + x) 0 * Matrix.diagonal
            (fun y : G.Ω 1 => (((coverOf G).chi q y : ℝ) : ℂ)) := by
      unfold Dec2.Kzx Dec2.chiD
      rw [hH]
    rw [hKe]
    refine opNorm_comm_le _ _ (fun y => ?_) hP0
      (fun z => dirichlet_offdiag_row_le G S.weights (ν + x) 0 z)
      (fun y => dirichlet_offdiag_col_le G S.weights (ν + x) 0 y)
    have hc := Dec2.chi_mem_Icc S hq y
    simp only [Complex.norm_real, Real.norm_of_nonneg hc.1]
    exact hc.2
  set u : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → G.Ω 1 → ℂ := fun q =>
    cubeGx G a aT 0 (ν + x) α q *ᵥ g with hu
  set F : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → G.Ω 1 → ℂ := fun q y =>
    (coverOf G).sProd s q * (Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q *ᵥ u q) y with hF
  have hFs : ∀ q ∈ (coverOf G).cubeIdx, ∀ y : G.Ω 1,
      (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ intBox q → F q y = 0 := by
    intro q hq y hy
    have := Dec2.rowSupp_Kzx_cubeGx (x := 0) (α := α) S hq g y hy
    simp only [hF, hu]
    rw [← Matrix.mulVec_mulVec] at this
    rw [this, mul_zero]
  have hMg : Dec2.Kcalx (coverOf G) G a aT 0 (ν + x) α s *ᵥ g =
      fun y => ∑ q ∈ (coverOf G).cubeIdx, F q y := by
    rw [Dec2.Kcalx_mulVec]
  have hβ : ∀ q ∈ (coverOf G).cubeIdx, sqNorm (F q) ≤
      (e * (2 * P) / (cubeGap L + x)) ^ 2 * sqNorm (cD G q *ᵥ g) := by
    intro q hq
    have hsp := norm_sProd_le_exp S hκ hs hq
    have h1 := cubeGx_sqNorm_le S hν hx hα hq g
    have h1' : (cubeGap L + x) ^ 2 * sqNorm (u q) ≤ sqNorm (cD G q *ᵥ g) := by
      simpa [cubeGap, hu] using h1
    have h2 := sqNorm_mulVec_le_opNorm (Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q) (u q)
    have h3 : sqNorm (Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q *ᵥ u q) ≤
        (2 * P) ^ 2 * sqNorm (u q) :=
      h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hK q hq) 2)
        (sqNorm_nonneg _))
    have h4 : sqNorm (F q) ≤ e ^ 2 * sqNorm (Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q *ᵥ u q) := by
      unfold sqNorm
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      have : ‖F q y‖ ≤ e * ‖(Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q *ᵥ u q) y‖ := by
        simp only [hF, norm_mul]
        exact mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
      calc ‖F q y‖ ^ 2 ≤ (e * ‖(Dec2.Kzx (coverOf G) G a aT 0 (ν + x) q *ᵥ u q) y‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) this 2
        _ = _ := by ring
    have h5 : sqNorm (u q) ≤ sqNorm (cD G q *ᵥ g) / (cubeGap L + x) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith [h1']
    calc sqNorm (F q) ≤ e ^ 2 * ((2 * P) ^ 2 * sqNorm (u q)) :=
          h4.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
      _ ≤ e ^ 2 * ((2 * P) ^ 2 * (sqNorm (cD G q *ᵥ g) / (cubeGap L + x) ^ 2)) := by
          gcongr
      _ = _ := by field_simp
  have := sqNorm_cubeSum_le S hFs g hβ
  rw [hMg]
  calc _ ≤ _ := this
    _ = _ := by field_simp

end FirstOrder

end Balaban.LargeField.Base
