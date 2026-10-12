/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventAbs
public import Balaban.Multiscale.CutCoercivity
public import Balaban.Localization.DecoupledCovAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The direct base decoupled resolvent (BASE-KERNEL-3 §1)

`D = G.Ω 1` is the fine-site chart domain of a one-layer generating set (a union of complete first
blocks, exterior spins held fixed).  `baseCutBonds G` is the set `𝓔` of nearest-neighbour bonds with
both endpoints in `D` but in different first blocks, `baseBond G b = T_b`, and
`baseHamiltonian G a ν α s = H(s) = H_cut + ∑_{b ∈ 𝓔} s_b T_b` (1.2).  The family
`baseOp N e H = Q_e (H ⊗ I_N) Q_e + P_e` is (1.3), and `baseResolvent` is `(A_e(s) + x)⁻¹`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset
open Balaban.LargeField.Base

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The fine bonds `(x, μ)` of the one-layer chart torus. -/
abbrev FineBond (d L N₀ : ℕ) : Type := Torus d (N₀ * L ^ 1) × Fin d

section Defs

variable (G : GeneratingSet d L N₀ 1 ϱ)

/-- **The set `𝓔`** of BASE-KERNEL-3 §1: bonds with both endpoints in `D = Ω₁` but in different
first blocks.  A Dirichlet boundary bond (other endpoint outside `D`) is not in `𝓔`. -/
def baseCutBonds : Finset (FineBond d L N₀) :=
  Finset.univ.filter fun b => b.1 ∈ G.Ω 1 ∧ b.1 + Pi.single b.2 1 ∈ G.Ω 1 ∧
    jBlock d L N₀ 1 1 b.1 ≠ jBlock d L N₀ 1 1 (b.1 + Pi.single b.2 1)

/-- `T_b = D_b^* D_b` on `D`: the restriction to `D` of the bond matrix of `b`. -/
noncomputable def baseBond (b : FineBond d L N₀) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  restrictOp ((bondMatrix b).map (algebraMap ℝ ℂ)) (G.Ω 1)

/-- **`H(s) = H_cut + ∑_{b ∈ 𝓔} s_b T_b`** (1.2), with `H_cut` the cut Dirichlet operator
`cutOperator G a ν 𝓔 α` (`ν = μ_bg`). -/
noncomputable def baseHamiltonian (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : FineBond d L N₀ → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  cutOperator G a ν (baseCutBonds G) α + ∑ b ∈ baseCutBonds G, s b • baseBond G b

end Defs

/-- `P_e = E Eᵀ`, `(E f)_z = e_z f_z`. -/
noncomputable def basePart {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (e : ι → Fin N → ℂ) :
    Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  fieldMul e * (fieldMul e)ᵀ

/-- **`A_e = Q_e (H ⊗ I_N) Q_e + P_e`** (1.3), `Q_e = 1 - P_e`. -/
noncomputable def baseOp {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (e : ι → Fin N → ℂ)
    (H : Matrix ι ι ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  (1 - basePart e) * liftOp N H * (1 - basePart e) + basePart e

/-- **`𝒞_{e,x} = (A_e + x I)⁻¹`**. -/
noncomputable def baseResolvent {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (e : ι → Fin N → ℂ) (H : Matrix ι ι ℂ) (x : ℝ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  (baseOp N e H + (x : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ))⁻¹

section Endpoints

variable (G : GeneratingSet d L N₀ 1 ϱ)

theorem baseBond_apply (b : FineBond d L N₀) (x y : G.Ω 1) :
    baseBond G b x y = ((bondVec b x : ℝ) : ℂ) * ((bondVec b y : ℝ) : ℂ) := by
  simp [baseBond, restrictOp, bondMatrix, Matrix.vecMulVec_apply]

/-- `H(0) = H_cut`. -/
theorem baseHamiltonian_zero (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    baseHamiltonian G a ν α (fun _ => 0) = cutOperator G a ν (baseCutBonds G) α := by
  simp [baseHamiltonian]

/-- `H(1) = H`, the one-layer Dirichlet operator. -/
theorem baseHamiltonian_one (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    baseHamiltonian G a ν α (fun _ => 1) = dirichletOperator G a ν α := by
  rw [← cutOperator_empty]
  have key : cutFullMatrix G a ν ∅ =
      cutFullMatrix G a ν (baseCutBonds G) + ∑ b ∈ baseCutBonds G, bondMatrix b := by
    simp only [cutFullMatrix, cutLaplacian, Finset.sum_empty, sub_zero]
    abel
  have key2 : restrictOp ((cutFullMatrix G a ν ∅).map (algebraMap ℝ ℂ)) (G.Ω 1) =
      restrictOp ((cutFullMatrix G a ν (baseCutBonds G)).map (algebraMap ℝ ℂ)) (G.Ω 1) +
        ∑ b ∈ baseCutBonds G, baseBond G b := by
    rw [key]
    ext x y
    simp [restrictOp, baseBond, Matrix.sum_apply]
  unfold baseHamiltonian cutOperator
  simp only [one_smul]
  rw [key2]
  abel

/-- `T_b` as a rank-one matrix. -/
theorem baseBond_eq_vecMulVec (b : FineBond d L N₀) :
    baseBond G b = Matrix.vecMulVec (fun x : G.Ω 1 => ((bondVec b x : ℝ) : ℂ))
      (fun x : G.Ω 1 => ((bondVec b x : ℝ) : ℂ)) := by
  ext x y
  rw [baseBond_apply, Matrix.vecMulVec_apply]

/-- Each `T_b` is positive semidefinite. -/
theorem reQuad_baseBond_nonneg (b : FineBond d L N₀) (u : G.Ω 1 → ℂ) :
    0 ≤ reQuad (baseBond G b) u := by
  set vC : G.Ω 1 → ℂ := fun x => ((bondVec b x : ℝ) : ℂ) with hvC
  set w : ℂ := vC ⬝ᵥ u with hw
  have hs : star u ⬝ᵥ vC = star w := by
    rw [hw]
    simp only [dotProduct, star_sum, star_mul']
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hvC]
    ring
  have h1 : star u ⬝ᵥ (baseBond G b *ᵥ u) = star w * w := by
    rw [baseBond_eq_vecMulVec, Matrix.vecMulVec_mulVec]
    simp only [dotProduct_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [hs]
  rw [reQuad_eq_dot, h1, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_nonneg]

/-- Cutting `𝓔` removes no bond inside a first block. -/
theorem baseCutBonds_aligned : CutAligned G (baseCutBonds G) := by
  intro j hj x μ hb _ hin
  have hj1 : j = 1 := by
    have := Finset.mem_Icc.1 hj; omega
  subst hj1
  have hmem := (Finset.mem_filter.1 hb).2
  exact hmem.2.2 (blockMap_add_single_of_inner (side_eq (le_refl 1)) hin).symm

/-- The coercivity constant `c = 1/(4L²)` of BASE-KERNEL-3 Theorem 1.1. -/
noncomputable def baseCoercivity (L : ℕ) : ℝ := 1 / (4 * (L : ℝ) ^ 2)

omit [NeZero N₀] [NeZero L] in
theorem baseCoercivity_pos (hL : 0 < L) : 0 < baseCoercivity L := by
  unfold baseCoercivity
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

omit [NeZero N₀] [NeZero L] in
theorem baseCoercivity_le_one (hL : 0 < L) : baseCoercivity L ≤ 1 := by
  unfold baseCoercivity
  have : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [div_le_one (by positivity)]
  nlinarith

/-- **(1.5)** for real parameters: `Re ⟨u, H(r) u⟩ ≥ c ‖u‖²` (the scalar form). -/
theorem baseHamiltonian_isCoercive_real {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (r : FineBond d L N₀ → ℝ)
    (hr : ∀ b ∈ baseCutBonds G, 0 ≤ r b) :
    IsCoercive (baseHamiltonian G a ν α (fun b => (r b : ℂ))) (baseCoercivity L) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hα' : ∀ x : G.Ω 1, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2) := by
    intro x
    have hx : (x : Torus d (N₀ * L ^ 1)) ∈ G.layer 1 := by
      rw [GeneratingSet.mem_layer]
      exact ⟨x.2, by rw [show 1 + 1 = 1 + 1 from rfl, G.top]; simp⟩
    rw [G.spacing_eq le_rfl le_rfl hx]
    refine (hα x).trans (le_of_eq ?_)
    unfold coerciveConstSharp
    field_simp
    ring
  have hc := cutOperator_isCoercive_min_sharp G (baseCutBonds_aligned G) hν ha α hα'
  intro u
  have h1 := hc u
  have h2 := reQuad_sum_nonneg (S := baseCutBonds G) (baseBond G) r u hr
    (fun b _ => reQuad_baseBond_nonneg G b u)
  unfold baseHamiltonian
  rw [reQuad_add]
  have hconst : coerciveConstSharp * (((L : ℝ) ^ 1) ^ 2)⁻¹ = baseCoercivity L := by
    unfold coerciveConstSharp baseCoercivity; field_simp
  rw [hconst] at h1
  linarith

/-- The positive end `x + e_μ` of the bond `(x, μ)`. -/
abbrev bondTip (b : FineBond d L N₀) : Torus d (N₀ * L ^ 1) := b.1 + Pi.single b.2 1

/-- The bonds having `x` as an endpoint: at most `2d`. -/
theorem card_bonds_at (x : Torus d (N₀ * L ^ 1)) :
    (Finset.univ.filter fun b : FineBond d L N₀ => b.1 = x ∨ bondTip b = x).card ≤
      2 * d := by
  classical
  have hsub : (Finset.univ.filter fun b : FineBond d L N₀ => b.1 = x ∨ bondTip b = x)
      ⊆ (Finset.univ.image fun μ : Fin d => (x, μ)) ∪
        (Finset.univ.image fun μ : Fin d => (x - Pi.single μ 1, μ)) := by
    rintro ⟨y, μ⟩ hb
    rcases (Finset.mem_filter.1 hb).2 with h | h
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨μ, by simp only [Prod.mk.injEq, and_true]; exact h.symm⟩
    · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      refine Or.inr ⟨μ, ?_⟩
      simp only [Prod.mk.injEq, and_true]
      rw [← h]; simp [bondTip]
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin d)))
    (f := fun μ : Fin d => (x, μ))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin d)))
    (f := fun μ : Fin d => (x - Pi.single μ 1, μ))
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  omega

omit [NeZero N₀] [NeZero L] in
theorem abs_bondVec_le_one (b : FineBond d L N₀) (x : Torus d (N₀ * L ^ 1)) :
    |bondVec b x| ≤ 1 := by
  unfold bondVec
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

omit [NeZero N₀] [NeZero L] in
theorem bondVec_ne_zero_mem (b : FineBond d L N₀) (x : Torus d (N₀ * L ^ 1))
    (h : bondVec b x ≠ 0) : b.1 = x ∨ bondTip b = x := by
  by_contra hc
  push Not at hc
  apply h
  unfold bondVec
  simp only [Pi.sub_apply, Pi.single_apply, Ne.symm hc.1, Ne.symm hc.2, ite_false]
  simp

theorem sum_abs_bondVec_le (b : FineBond d L N₀) :
    ∑ y : Torus d (N₀ * L ^ 1), |bondVec b y| ≤ 2 := by
  classical
  have h : ∀ y : Torus d (N₀ * L ^ 1), |bondVec b y| ≤
      (if y = bondTip b then (1 : ℝ) else 0) + (if y = b.1 then (1 : ℝ) else 0) := by
    intro y
    unfold bondVec
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num
  calc ∑ y : Torus d (N₀ * L ^ 1), |bondVec b y|
      ≤ ∑ y : Torus d (N₀ * L ^ 1), ((if y = bondTip b then (1 : ℝ) else 0) +
        (if y = b.1 then (1 : ℝ) else 0)) := Finset.sum_le_sum fun y _ => h y
    _ = 2 := by
        rw [Finset.sum_add_distrib]
        simp
        norm_num

theorem sum_norm_baseBond_row (b : FineBond d L N₀) (x : G.Ω 1) :
    ∑ y : G.Ω 1, ‖baseBond G b x y‖ ≤ if (b.1 = x ∨ bondTip b = x) then 2 else 0 := by
  have hnorm : ∀ y : G.Ω 1, ‖baseBond G b x y‖ = |bondVec b x| * |bondVec b y| := by
    intro y
    rw [baseBond_apply, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  simp only [hnorm]
  rw [← Finset.mul_sum]
  have hD : ∑ y : G.Ω 1, |bondVec b y| ≤ 2 := by
    refine le_trans ?_ (sum_abs_bondVec_le b)
    calc ∑ y : G.Ω 1, |bondVec b y| = ∑ y ∈ G.Ω 1, |bondVec b y| := by
          rw [Finset.sum_coe_sort (G.Ω 1) (fun y => |bondVec b y|)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
  split_ifs with h
  · calc |bondVec b x| * ∑ y : G.Ω 1, |bondVec b y| ≤ 1 * 2 :=
          mul_le_mul (abs_bondVec_le_one b x) hD (Finset.sum_nonneg fun _ _ => abs_nonneg _)
            zero_le_one
      _ = 2 := one_mul _
  · have : bondVec b x = 0 := by
      by_contra hne; exact h (bondVec_ne_zero_mem b x hne)
    simp [this]

/-- Row sums of `∑_{b ∈ 𝓔} ‖T_b‖` are at most `4d`. -/
theorem sum_bonds_norm_row_le (x : G.Ω 1) :
    ∑ b ∈ baseCutBonds G, ∑ y : G.Ω 1, ‖baseBond G b x y‖ ≤ 4 * d := by
  classical
  calc ∑ b ∈ baseCutBonds G, ∑ y : G.Ω 1, ‖baseBond G b x y‖
      ≤ ∑ b ∈ baseCutBonds G, (if (b.1 = x ∨ bondTip b = x) then (2 : ℝ) else 0) :=
        Finset.sum_le_sum fun b _ => sum_norm_baseBond_row G b x
    _ ≤ ∑ b : FineBond d L N₀, (if (b.1 = x ∨ bondTip b = x) then (2 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b _ _ => by split_ifs <;> norm_num)
    _ = 2 * ((Finset.univ.filter fun b : FineBond d L N₀ =>
          b.1 = x ∨ bondTip b = x).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * (2 * d : ℕ) := by
        gcongr
        exact_mod_cast card_bonds_at (x : Torus d (N₀ * L ^ 1))
    _ = 4 * d := by push_cast; ring

theorem baseBond_symm (b : FineBond d L N₀) (x y : G.Ω 1) :
    baseBond G b x y = baseBond G b y x := by
  rw [baseBond_apply, baseBond_apply, mul_comm]

/-- Column sums likewise. -/
theorem sum_bonds_norm_col_le (y : G.Ω 1) :
    ∑ b ∈ baseCutBonds G, ∑ x : G.Ω 1, ‖baseBond G b x y‖ ≤ 4 * d := by
  simpa only [baseBond_symm G _ _ y] using sum_bonds_norm_row_le G y

/-- Parameters within `η` of a real vector in `[0,1]^𝓔`. -/
def baseParamNbhd (η : ℝ) : Set (FineBond d L N₀ → ℂ) :=
  {s | ∀ b ∈ baseCutBonds G, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ‖s b - (r : ℂ)‖ ≤ η}

/-- The open version: parameters strictly within `η` of a real vector in `[0,1]^𝓔`. -/
def baseParamNbhdOpen (η : ℝ) : Set (FineBond d L N₀ → ℂ) :=
  {s | ∀ b ∈ baseCutBonds G, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ‖s b - (r : ℂ)‖ < η}

/-- **(1.6), scalar form.**  If each complex `s_b` is within `η ≤ c/(8d)` of a real `r_b ∈ [0,1]`,
then `Re ⟨u, H(s) u⟩ ≥ (c/2) ‖u‖²`. -/
theorem baseHamiltonian_isCoercive_of_close {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) :
    IsCoercive (baseHamiltonian G a ν α s) (baseCoercivity L / 2) := by
  classical
  have hc0 := baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L))
  choose! r hr0 hr1 hrs using hs
  have h4 : 4 * (d : ℝ) * η ≤ baseCoercivity L / 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp; positivity
    · have hd : (0 : ℝ) < d := by exact_mod_cast h
      calc 4 * (d : ℝ) * η ≤ 4 * d * (baseCoercivity L / (8 * d)) := by gcongr
        _ = baseCoercivity L / 2 := by field_simp; ring
  have hreal := baseHamiltonian_isCoercive_real G hν ha hα r hr0
  set Δ : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
    ∑ b ∈ baseCutBonds G, (s b - (r b : ℂ)) • baseBond G b with hΔ
  have hsplit : baseHamiltonian G a ν α s =
      baseHamiltonian G a ν α (fun b => (r b : ℂ)) + Δ := by
    unfold baseHamiltonian
    rw [hΔ, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [sub_smul]; abel
  set E : G.Ω 1 → G.Ω 1 → ℝ := fun x y => ∑ b ∈ baseCutBonds G, η * ‖baseBond G b x y‖ with hE
  have hDE : ∀ x y, ‖Δ x y‖ ≤ E x y := by
    intro x y
    rw [hΔ, Matrix.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hrs b hb) (norm_nonneg _)
  have hrow : ∀ x, ∑ y, E x y ≤ 4 * d * η := by
    intro x
    calc ∑ y, E x y = ∑ b ∈ baseCutBonds G, ∑ y, η * ‖baseBond G b x y‖ := Finset.sum_comm
      _ = η * ∑ b ∈ baseCutBonds G, ∑ y, ‖baseBond G b x y‖ := by
          simp only [← Finset.mul_sum]
      _ ≤ η * (4 * d) := mul_le_mul_of_nonneg_left (sum_bonds_norm_row_le G x) hη0
      _ = 4 * d * η := by ring
  have hcol : ∀ y, ∑ x, E x y ≤ 4 * d * η := by
    intro y
    calc ∑ x, E x y = ∑ b ∈ baseCutBonds G, ∑ x, η * ‖baseBond G b x y‖ := Finset.sum_comm
      _ = η * ∑ b ∈ baseCutBonds G, ∑ x, ‖baseBond G b x y‖ := by
          simp only [← Finset.mul_sum]
      _ ≤ η * (4 * d) := mul_le_mul_of_nonneg_left (sum_bonds_norm_col_le G y) hη0
      _ = 4 * d * η := by ring
  intro u
  have h1 := hreal u
  have h2 := reQuad_ge_of_entry_bound Δ E hDE hrow hcol u
  rw [hsplit, reQuad_add]
  have hN := sqNorm_nonneg u
  nlinarith

section Main

open scoped Matrix.Norms.L2Operator

variable {N : ℕ}

/-- `P_e` of a real unit field is an orthogonal projection (`unitProj`). -/
theorem basePart_real {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Fin N → ℝ) :
    basePart (fun z i => (e z i : ℂ)) = unitProj e := rfl

/-- **(1.5), the operator `A_e(r)`**: for real parameters `r_b ∈ [0,1]` and a real unit background
`e`, `Re ⟨u, A_e(r) u⟩ ≥ c ‖u‖²`. -/
theorem baseOp_isCoercive_real {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (r : FineBond d L N₀ → ℝ)
    (hr : ∀ b ∈ baseCutBonds G, 0 ≤ r b ∧ r b ≤ 1) (e : G.Ω 1 → Fin N → ℝ)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) :
    IsCoercive (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α (fun b => (r b : ℂ)))) (baseCoercivity L) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hH := baseHamiltonian_isCoercive_real G hν ha hα r (fun b hb => (hr b hb).1)
  have hP := unitProj_conjTranspose e
  have hPP := unitProj_mul_self e he
  unfold baseOp
  rw [basePart_real]
  exact isCoercive_proj_split hP hPP (baseCoercivity_le_one hL) (isCoercive_liftOp hH)

/-- **(1.6), the operator `A_e(s)`**: `Re ⟨u, A_e(s) u⟩ ≥ (c/2) ‖u‖²` for complex parameters
within `η ≤ c/(8d)` of `[0,1]^𝓔`. -/
theorem baseOp_isCoercive_of_close {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1) :
    IsCoercive (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s))
      (baseCoercivity L / 2) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hH := baseHamiltonian_isCoercive_of_close G hν ha hα hη0 hη hs
  have hP := unitProj_conjTranspose e
  have hPP := unitProj_mul_self e he
  have hc := baseCoercivity_le_one hL
  unfold baseOp
  rw [basePart_real]
  exact isCoercive_proj_split hP hPP (by linarith) (isCoercive_liftOp hH)

/-- **(1.6), the resolvent**: `A_e(s) + x` is invertible and `‖𝒞_{e,x}(s)‖ ≤ (c/2 + x)⁻¹`
(`ℓ²` operator norm), for all `x ≥ 0`. -/
theorem baseResolvent_norm_le {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)
    {x : ℝ} (hx : 0 ≤ x) :
    IsUnit (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s) +
        (x : ℂ) • (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)) ∧
      ‖baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s) x‖ ≤
        (baseCoercivity L / 2 + x)⁻¹ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc := baseCoercivity_pos hL
  have h := (baseOp_isCoercive_of_close G hν ha hα hη0 hη hs e he).add_smul_one x
  exact opNorm_inv_le_of_isCoercive (by linarith) h

end Main

end Endpoints

end Balaban.LargeField.Base
