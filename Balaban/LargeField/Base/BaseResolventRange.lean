/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventMain
public import Balaban.Multiscale.AgmonCore
public import Balaban.Green.LimitCauchy
public import Balaban.LargeField.Base.BaseResolventDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Volume-independent row sums and range of `A_e(s)` (BASE-KERNEL-3 Theorem 1.1)

There are `J, R < ∞`, depending only on `d, L, ν` and not on the number `N₀` of blocks, the
domain `D`, the potential `α`, the parameters `s` or the background `e`, such that the block row
and column sums of `A_e(s)` are at most `J` and its blocks vanish beyond distance `R`
(`baseOp_rowSum_range`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset
open scoped Matrix.Norms.L2Operator

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Torus

theorem matrix_eq_of_forms {n : Type*} [Fintype n] [DecidableEq n] (M M' : Matrix n n ℝ)
    (h : ∀ g φ : n → ℝ, g ⬝ᵥ M *ᵥ φ = g ⬝ᵥ M' *ᵥ φ) : M = M' := by
  ext x y
  have := h (Pi.single x 1) (Pi.single y 1)
  simpa [Matrix.mulVec_single_one, dotProduct_single_one] using this

/-- `-Δ + ν = ν + ∑_b T_b` on the torus (sum over all bonds). -/
theorem latticeLaplacian_eq_bonds (ν : ℝ) :
    latticeLaplacian d (N₀ * L ^ 1) ν = ν • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) +
      ∑ b : FineBond d L N₀, bondMatrix b := by
  refine matrix_eq_of_forms _ _ fun g φ => ?_
  rw [latticeLaplacian_bilinear, Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec,
    dotProduct_sum]
  simp only [bondMatrix_bilinear, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul, Fintype.sum_prod_type]
  simp only [dotProduct]
  ring

theorem sum_abs_bondMatrix_row (b : FineBond d L N₀) (z : Torus d (N₀ * L ^ 1)) :
    ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y| ≤
      if (b.1 = z ∨ bondTip b = z) then 2 else 0 := by
  have hnorm : ∀ y, |bondMatrix b z y| = |bondVec b z| * |bondVec b y| := by
    intro y
    rw [bondMatrix, Matrix.vecMulVec_apply, abs_mul]
  simp only [hnorm]
  rw [← Finset.mul_sum]
  split_ifs with h
  · calc |bondVec b z| * ∑ y, |bondVec b y| ≤ 1 * 2 :=
          mul_le_mul (abs_bondVec_le_one b z) (sum_abs_bondVec_le b)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_one
      _ = 2 := one_mul _
  · have : bondVec b z = 0 := by
      by_contra hne; exact h (bondVec_ne_zero_mem b z hne)
    simp [this]

theorem sum_bonds_abs_row_le (S : Finset (FineBond d L N₀)) (z : Torus d (N₀ * L ^ 1)) :
    ∑ b ∈ S, ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y| ≤ 4 * d := by
  classical
  calc ∑ b ∈ S, ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y|
      ≤ ∑ b ∈ S, (if (b.1 = z ∨ bondTip b = z) then (2 : ℝ) else 0) :=
        Finset.sum_le_sum fun b _ => sum_abs_bondMatrix_row b z
    _ ≤ ∑ b : FineBond d L N₀, (if (b.1 = z ∨ bondTip b = z) then (2 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b _ _ => by split_ifs <;> norm_num)
    _ = 2 * ((Finset.univ.filter fun b : FineBond d L N₀ =>
          b.1 = z ∨ bondTip b = z).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * (2 * d : ℕ) := by
        gcongr
        exact_mod_cast card_bonds_at z
    _ = 4 * d := by push_cast; ring

theorem cutFullMatrix_eq (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (FineBond d L N₀)) :
    cutFullMatrix G a ν cut = ν • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) +
      ∑ b ∈ Finset.univ \ cut, bondMatrix b + avgMatrix G a := by
  unfold cutFullMatrix cutLaplacian
  rw [latticeLaplacian_eq_bonds, ← Finset.sum_sdiff (Finset.subset_univ cut)]
  abel

theorem avgMatrix_eq (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) :
    avgMatrix G a = (a 1 / ((L : ℝ) ^ 1) ^ 2) • layerProjMatrix G 1 := by
  unfold avgMatrix
  simp

theorem sum_abs_avgMatrix_row (G : GeneratingSet d L N₀ 1 ϱ) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights 1 a) (z : Torus d (N₀ * L ^ 1)) :
    ∑ y, |avgMatrix G a z y| ≤ 2 := by
  have ha1 := ha 1 le_rfl le_rfl
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hcoef : |a 1 / ((L : ℝ) ^ 1) ^ 2| ≤ 2 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ 1) ^ 2)]
    rw [abs_of_nonneg (by linarith [ha1.1])]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [ha1.2]
  have hrow := blockProjMatrix_row (d := d) (L := L) (N₀ := N₀) (k := 1) (j := 1) le_rfl z
  calc ∑ y, |avgMatrix G a z y|
      ≤ ∑ y, (2 * blockProjMatrix d (N₀ * L ^ 1) (L ^ 1) (N₀ * L ^ (1 - 1)) z y) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [avgMatrix_eq, Matrix.smul_apply, smul_eq_mul, abs_mul]
        have hb := blockProjMatrix_nonneg (d := d) (L := L) (N₀ := N₀) (k := 1) 1 z y
        have hl : |layerProjMatrix G 1 z y| ≤
            blockProjMatrix d (N₀ * L ^ 1) (L ^ 1) (N₀ * L ^ (1 - 1)) z y := by
          unfold layerProjMatrix
          split_ifs
          · exact (abs_of_nonneg hb).le
          · simpa using hb
        exact mul_le_mul hcoef hl (abs_nonneg _) (by norm_num)
    _ = 2 := by rw [← Finset.mul_sum, hrow]; ring

end Torus

section Rows

variable (G : GeneratingSet d L N₀ 1 ϱ)

theorem baseHamiltonian_apply (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : FineBond d L N₀ → ℂ) (z y : G.Ω 1) :
    baseHamiltonian G a ν α s z y =
      ((cutFullMatrix G a ν (baseCutBonds G) z y : ℝ) : ℂ) + (if z = y then α z else 0) +
        ∑ b ∈ baseCutBonds G, s b * baseBond G b z y := by
  unfold baseHamiltonian cutOperator
  simp [restrictOp, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.add_apply]

theorem sum_norm_cutFull_row_le {a : ℕ → ℝ} (ha : IsAdmissibleWeights 1 a) {ν : ℝ}
    (hν : 0 ≤ ν) (z : G.Ω 1) :
    ∑ y : G.Ω 1, |cutFullMatrix G a ν (baseCutBonds G) z y| ≤ ν + 4 * d + 2 := by
  classical
  have hsub : ∑ y : G.Ω 1, |cutFullMatrix G a ν (baseCutBonds G) z y| ≤
      ∑ y : Torus d (N₀ * L ^ 1), |cutFullMatrix G a ν (baseCutBonds G) z y| := by
    calc _ = ∑ y ∈ G.Ω 1, |cutFullMatrix G a ν (baseCutBonds G) z y| :=
          Finset.sum_coe_sort (G.Ω 1) (fun y => |cutFullMatrix G a ν (baseCutBonds G) z y|)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
  refine hsub.trans ?_
  have hentry : ∀ y : Torus d (N₀ * L ^ 1), |cutFullMatrix G a ν (baseCutBonds G) z y| ≤
      (if (z : Torus d (N₀ * L ^ 1)) = y then ν else 0) +
        ∑ b ∈ Finset.univ \ baseCutBonds G, |bondMatrix b z y| + |avgMatrix G a z y| := by
    intro y
    rw [cutFullMatrix_eq]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
      smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_
      (Finset.abs_sum_le_sum_abs _ _))) le_rfl)
    split_ifs with h
    · simp [abs_of_nonneg hν]
    · simp
  calc ∑ y : Torus d (N₀ * L ^ 1), |cutFullMatrix G a ν (baseCutBonds G) z y|
      ≤ ∑ y : Torus d (N₀ * L ^ 1), ((if (z : Torus d (N₀ * L ^ 1)) = y then ν else 0) +
        ∑ b ∈ Finset.univ \ baseCutBonds G, |bondMatrix b z y| + |avgMatrix G a z y|) :=
        Finset.sum_le_sum fun y _ => hentry y
    _ = ν + ∑ b ∈ Finset.univ \ baseCutBonds G, ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y| +
          ∑ y, |avgMatrix G a z y| := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
        simp
    _ ≤ ν + 4 * d + 2 := by
        have h1 := sum_bonds_abs_row_le (Finset.univ \ baseCutBonds G) z
        have h2 := sum_abs_avgMatrix_row G ha z
        linarith

omit [NeZero N₀] in
theorem eta_le_one {η : ℝ} (hη : η ≤ baseCoercivity L / (8 * d)) : η ≤ 1 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc0 := baseCoercivity_pos hL
  have hc1 := baseCoercivity_le_one hL
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp at hη; linarith
  · have hd : (1 : ℝ) ≤ d := by exact_mod_cast h
    refine hη.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith

theorem norm_param_le_two {η : ℝ} (hη1 : η ≤ 1) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) {b : FineBond d L N₀} (hb : b ∈ baseCutBonds G) :
    ‖s b‖ ≤ 2 := by
  obtain ⟨r, hr0, hr1, hrs⟩ := hs b hb
  calc ‖s b‖ = ‖(s b - (r : ℂ)) + (r : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖s b - (r : ℂ)‖ + ‖(r : ℂ)‖ := norm_add_le _ _
    _ ≤ η + 1 := by
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
    _ ≤ 2 := by linarith

/-- Row sums of the scalar operator `H(s)`: at most `ν + 12 d + 3`, independent of the volume. -/
theorem baseHamiltonian_row_le {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    {α : G.Ω 1 → ℂ} (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ}
    (hη : η ≤ baseCoercivity L / (8 * d)) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) (z : G.Ω 1) :
    ∑ y : G.Ω 1, ‖baseHamiltonian G a ν α s z y‖ ≤ ν + 12 * d + 3 := by
  classical
  have hη1 := eta_le_one hη
  have hLpos : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hαz : ‖α z‖ ≤ 1 := by
    refine (hα z).trans ?_
    rw [div_le_one (by positivity)]; nlinarith
  have h1 := sum_norm_cutFull_row_le G ha hν z
  have h2 : ∑ y : G.Ω 1, ‖(if z = y then α z else 0)‖ ≤ 1 := by
    rw [Finset.sum_eq_single z]
    · simpa using hαz
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  have h3 : ∑ y : G.Ω 1, ‖∑ b ∈ baseCutBonds G, s b * baseBond G b z y‖ ≤ 8 * d := by
    calc _ ≤ ∑ y : G.Ω 1, ∑ b ∈ baseCutBonds G, 2 * ‖baseBond G b z y‖ := by
          refine Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun b hb => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_param_le_two G hη1 hs hb) (norm_nonneg _)
      _ = 2 * ∑ b ∈ baseCutBonds G, ∑ y : G.Ω 1, ‖baseBond G b z y‖ := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ ≤ 2 * (4 * d) := mul_le_mul_of_nonneg_left (sum_bonds_norm_row_le G z) (by norm_num)
      _ = 8 * d := by ring
  calc ∑ y : G.Ω 1, ‖baseHamiltonian G a ν α s z y‖
      ≤ ∑ y : G.Ω 1, (|cutFullMatrix G a ν (baseCutBonds G) z y| +
          ‖(if z = y then α z else 0)‖ +
          ‖∑ b ∈ baseCutBonds G, s b * baseBond G b z y‖) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [baseHamiltonian_apply]
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ∑ y : G.Ω 1, |cutFullMatrix G a ν (baseCutBonds G) z y| +
          ∑ y : G.Ω 1, ‖(if z = y then α z else 0)‖ +
          ∑ y : G.Ω 1, ‖∑ b ∈ baseCutBonds G, s b * baseBond G b z y‖ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ ν + 12 * d + 3 := by linarith

end Rows

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem blockOf_mul (X Y : Matrix (ι × Fin N) (ι × Fin N) ℂ) (z y : ι) :
    blockOf (X * Y) z y = ∑ w, blockOf X z w * blockOf Y w y := by
  ext i j
  simp only [blockOf, Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

theorem blockOf_one (z w : ι) :
    blockOf (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) z w = if z = w then 1 else 0 := by
  ext i j
  by_cases h : z = w
  · subst h; simp [blockOf, Matrix.one_apply]
  · simp [blockOf, Matrix.one_apply, h]

theorem blockOf_liftOp (H : Matrix ι ι ℂ) (z y : ι) :
    blockOf (liftOp N H) z y = H z y • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [blockOf, liftOp]
  · simp [blockOf, liftOp, Matrix.one_apply, h]

theorem blockOf_add (X Y : Matrix (ι × Fin N) (ι × Fin N) ℂ) (z y : ι) :
    blockOf (X + Y) z y = blockOf X z y + blockOf Y z y := by
  ext i j; simp [blockOf]

theorem blockOf_sub (X Y : Matrix (ι × Fin N) (ι × Fin N) ℂ) (z y : ι) :
    blockOf (X - Y) z y = blockOf X z y - blockOf Y z y := by
  ext i j; simp [blockOf]

/-- The rank-one block `P_z = e_z e_zᵀ`. -/
def siteProj (e : ι → Fin N → ℝ) (z : ι) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => (e z i : ℂ) * (e z j : ℂ)

theorem blockOf_unitProj (e : ι → Fin N → ℝ) (z w : ι) :
    blockOf (unitProj e) z w = if z = w then siteProj e z else 0 := by
  ext i j
  by_cases h : z = w
  · subst h; simp [blockOf, unitProj_apply, siteProj]
  · simp [blockOf, unitProj_apply, h]

theorem siteProj_conjTranspose (e : ι → Fin N → ℝ) (z : ι) :
    (siteProj e z)ᴴ = siteProj e z := by
  ext i j
  simp [siteProj, Matrix.conjTranspose_apply, mul_comm]

theorem siteProj_mul_self (e : ι → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1) (z : ι) :
    siteProj e z * siteProj e z = siteProj e z := by
  ext i k
  have hc : (∑ j : Fin N, (e z j : ℂ) ^ 2) = 1 := by exact_mod_cast he z
  simp only [siteProj, Matrix.mul_apply, Matrix.of_apply]
  calc ∑ j, (e z i : ℂ) * (e z j : ℂ) * ((e z j : ℂ) * (e z k : ℂ))
      = (e z i : ℂ) * (e z k : ℂ) * ∑ j, (e z j : ℂ) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    _ = _ := by rw [hc, mul_one]

/-- The block `Q_z = 1 - P_z` and the block `P_z` have operator norm at most one. -/
theorem norm_siteProj_le (e : ι → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1) (z : ι) :
    ‖siteProj e z‖ ≤ 1 ∧ ‖(1 : Matrix (Fin N) (Fin N) ℂ) - siteProj e z‖ ≤ 1 := by
  have hsplit := fun f => sqNorm_proj_split (siteProj_conjTranspose e z) (siteProj_mul_self e he z) f
  constructor
  · refine l2_opNorm_le_of_sqNorm _ zero_le_one fun f => ?_
    have := hsplit f
    have h2 := sqNorm_nonneg ((1 - siteProj e z) *ᵥ f)
    rw [one_pow, one_mul]; linarith
  · refine l2_opNorm_le_of_sqNorm _ zero_le_one fun f => ?_
    have := hsplit f
    have h2 := sqNorm_nonneg (siteProj e z *ᵥ f)
    rw [one_pow, one_mul]; linarith

theorem blockOf_baseOp (e : ι → Fin N → ℝ) (H : Matrix ι ι ℂ) (z y : ι) :
    blockOf (baseOp N (fun z i => (e z i : ℂ)) H) z y =
      H z y • ((1 - siteProj e z) * (1 - siteProj e y)) + (if z = y then siteProj e z else 0) := by
  have hP : basePart (fun z i => (e z i : ℂ)) = unitProj e := rfl
  have hQ : ∀ a b, blockOf (1 - unitProj e) a b = if a = b then 1 - siteProj e a else 0 := by
    intro a b
    rw [blockOf_sub, blockOf_one, blockOf_unitProj]
    split_ifs <;> simp
  unfold baseOp
  rw [hP, blockOf_add, blockOf_unitProj, blockOf_mul]
  congr 1
  simp only [blockOf_mul, hQ, blockOf_liftOp]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single z]
    · simp [Matrix.smul_mul, Matrix.mul_smul]
    · intro w _ hw
      simp [Ne.symm hw]
    · simp
  · intro w _ hw
    simp [hw]
  · simp

theorem norm_blockOf_baseOp_le (e : ι → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)
    (H : Matrix ι ι ℂ) (z y : ι) :
    ‖blockOf (baseOp N (fun z i => (e z i : ℂ)) H) z y‖ ≤
      ‖H z y‖ + (if z = y then 1 else 0) := by
  rw [blockOf_baseOp]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h1 := (norm_siteProj_le e he z).2
    have h2 := (norm_siteProj_le e he y).2
    have hX : ‖((1 - siteProj e z) * (1 - siteProj e y) : Matrix (Fin N) (Fin N) ℂ)‖ ≤ 1 := by
      calc _ ≤ ‖(1 - siteProj e z : Matrix (Fin N) (Fin N) ℂ)‖ *
            ‖(1 - siteProj e y : Matrix (Fin N) (Fin N) ℂ)‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) hX
  · split_ifs
    · exact (norm_siteProj_le e he z).1
    · simp

end Blocks

end Balaban.LargeField.Base
