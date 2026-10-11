/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.Symmetry
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Block structure of the one- and two-point functions (Lemma 0.2 (c))

For `N ≥ 2` there are a real `blockM` and functions `blockGtr`, `blockGlg` on the torus,
independent of the direction `h` of the field, such that for every unit vector `h`
`⟨φ_x⟩ = blockM • h` and
`G(x, y) = blockGtr (x - y) (I - h ⊗ h) + blockGlg (x - y) h ⊗ h`
(`exists_block_structure`, `onePoint_eq_blockM_mul`, `twoPointTruncated_eq_block`).
The proof uses the stabilizer of `e₀`: sign changes of the coordinates `k ≠ 0` and transpositions
of coordinates `≠ 0`, together with a reflection carrying `e₀` to `h`.
-/

@[expose] public section

namespace Balaban

open Submodule

variable {d N ℓ : ℕ} [NeZero ℓ]

/-! ### Isometries used -/

omit [NeZero ℓ] in
theorem rotEntry_orth (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (i k : Fin N) :
    ∑ j, rotEntry R i j * rotEntry R k j = if i = k then 1 else 0 := by
  have := ((EuclideanSpace.basisFun (Fin N) ℝ).map R).sum_inner_mul_inner
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ))
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] at this
  exact this.trans (if_congr eq_comm rfl rfl)

/-- The sign change of the `k`-th coordinate. -/
noncomputable def flipIso (k : Fin N) :
    EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
  reflection (ℝ ∙ (EuclideanSpace.single k (1 : ℝ)))ᗮ

theorem flipIso_apply (k : Fin N) (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    flipIso k v i = if i = k then - v i else v i := by
  unfold flipIso
  rw [reflection_orthogonal_apply, reflection_singleton_apply]
  by_cases h : i = k
  · subst h; simp [EuclideanSpace.inner_single_left]; ring
  · simp [h, EuclideanSpace.inner_single_left]

theorem rotEntry_flip (k i j : Fin N) :
    rotEntry (flipIso k) i j = if i = j then (if i = k then -1 else 1) else 0 := by
  unfold rotEntry
  rw [flipIso_apply]
  by_cases h : i = j <;> by_cases h2 : i = k
  all_goals simp [h, h2, PiLp.single_apply]
  all_goals (split_ifs <;> simp_all)

/-- The transposition of two coordinates. -/
noncomputable def swapIso (a b : Fin N) :
    EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap a b)

theorem rotEntry_swap (a b i j : Fin N) :
    rotEntry (swapIso a b) i j = if Equiv.swap a b i = j then 1 else 0 := by
  unfold rotEntry swapIso
  simp only [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Pi.single_apply]

/-! ### The stabilizer of `e₀` -/

section Stabilizer

variable (β ν : ℝ) (i₀ : Fin N)

local notation "e₀" => (EuclideanSpace.single i₀ (1 : ℝ) : EuclideanSpace ℝ (Fin N))

theorem flipIso_fixes (k : Fin N) (hk : k ≠ i₀) : flipIso k e₀ = e₀ := by
  ext i
  rw [flipIso_apply]
  by_cases h : i = k
  · subst h; simp [hk]
  · simp [h]

theorem swapIso_fixes (a b : Fin N) (ha : a ≠ i₀) (hb : b ≠ i₀) : swapIso a b e₀ = e₀ := by
  ext i
  simp [swapIso, PiLp.single_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem onePoint_stab_zero (x : Torus d ℓ) (k : Fin N) (hk : k ≠ i₀) :
    onePoint d N ℓ β ν e₀ x k = 0 := by
  have := onePoint_rot (flipIso k) β ν e₀ x k
  rw [flipIso_fixes i₀ k hk] at this
  simp only [rotEntry_flip] at this
  simp at this
  linarith

theorem twoPointTruncated_stab_offDiag (x y : Torus d ℓ) (a b : Fin N) (hab : a ≠ b) :
    twoPointTruncated d N ℓ β ν e₀ x y a b = 0 := by
  obtain ⟨k, hk, hka⟩ : ∃ k, k ≠ i₀ ∧ ((a = k ∧ b ≠ k) ∨ (b = k ∧ a ≠ k)) := by
    by_cases ha : a = i₀
    · exact ⟨b, fun h => hab (ha.trans h.symm), Or.inr ⟨rfl, hab⟩⟩
    · exact ⟨a, ha, Or.inl ⟨rfl, fun h => hab h.symm⟩⟩
  have := twoPointTruncated_rot (flipIso k) β ν e₀ x y a b
  rw [flipIso_fixes i₀ k hk] at this
  simp only [rotEntry_flip] at this
  rcases hka with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2] at this
    rw [h1]; linarith
  · simp [h1, h2] at this
    rw [h1]; linarith

theorem twoPointTruncated_stab_diag (x y : Torus d ℓ) (a b : Fin N) (ha : a ≠ i₀)
    (hb : b ≠ i₀) :
    twoPointTruncated d N ℓ β ν e₀ x y a a = twoPointTruncated d N ℓ β ν e₀ x y b b := by
  have := twoPointTruncated_rot (swapIso a b) β ν e₀ x y a a
  rw [swapIso_fixes i₀ a b ha hb] at this
  simp only [rotEntry_swap] at this
  simp at this
  exact this

end Stabilizer

/-! ### The block structure -/

theorem twoPointTruncated_sub (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (x y : Torus d ℓ)
    (i k : Fin N) :
    twoPointTruncated d N ℓ β ν h x y i k = twoPointTruncated d N ℓ β ν h (x - y) 0 i k := by
  have := twoPointTruncated_add β ν h y (x - y) 0 i k
  rwa [sub_add_cancel, zero_add] at this

theorem twoPointTruncated_comm (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (x y : Torus d ℓ)
    (i k : Fin N) :
    twoPointTruncated d N ℓ β ν h x y i k = twoPointTruncated d N ℓ β ν h y x k i := by
  unfold twoPointTruncated
  rw [mul_comm (onePoint d N ℓ β ν h x i)]
  congr 1
  simp only [mul_comm]

/-- The first coordinate index (`N ≥ 2`). -/
def idx₀ (hN : 2 ≤ N) : Fin N := ⟨0, by omega⟩

/-- The second coordinate index (`N ≥ 2`). -/
def idx₁ (hN : 2 ≤ N) : Fin N := ⟨1, by omega⟩

theorem idx₁_ne_idx₀ (hN : 2 ≤ N) : idx₁ hN ≠ idx₀ hN := by
  simp [idx₀, idx₁, Fin.ext_iff]

/-- The magnetization `m = ⟨φ_1⟩` for the field in direction `e₁` (independent of the point). -/
noncomputable def blockM (d N ℓ : ℕ) [NeZero ℓ] (hN : 2 ≤ N) (β ν : ℝ) : ℝ :=
  onePoint d N ℓ β ν (EuclideanSpace.single (idx₀ hN) 1) 0 (idx₀ hN)

/-- The transversal covariance `G_tr(z) = G(z, 0)_{22}` for the field in direction `e₁`. -/
noncomputable def blockGtr (d N ℓ : ℕ) [NeZero ℓ] (hN : 2 ≤ N) (β ν : ℝ) (z : Torus d ℓ) : ℝ :=
  twoPointTruncated d N ℓ β ν (EuclideanSpace.single (idx₀ hN) 1) z 0 (idx₁ hN) (idx₁ hN)

/-- The longitudinal covariance `G_lg(z) = G(z, 0)_{11}` for the field in direction `e₁`. -/
noncomputable def blockGlg (d N ℓ : ℕ) [NeZero ℓ] (hN : 2 ≤ N) (β ν : ℝ) (z : Torus d ℓ) : ℝ :=
  twoPointTruncated d N ℓ β ν (EuclideanSpace.single (idx₀ hN) 1) z 0 (idx₀ hN) (idx₀ hN)

/-- A reflection carrying `e₀` to the unit vector `h`. -/
theorem exists_rot_single (hN : 2 ≤ N) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) :
    ∃ R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N),
      R (EuclideanSpace.single (idx₀ hN) 1) = h :=
  ⟨_, reflection_sub (by simp [hh])⟩

theorem onePoint_eq_blockM_mul (hN : 2 ≤ N) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (hh : ‖h‖ = 1) (x : Torus d ℓ) (i : Fin N) :
    onePoint d N ℓ β ν h x i = blockM d N ℓ hN β ν * h i := by
  obtain ⟨R, hR⟩ := exists_rot_single hN h hh
  have := onePoint_rot R β ν (EuclideanSpace.single (idx₀ hN) 1) x i
  rw [hR] at this
  rw [this, Finset.sum_eq_single (idx₀ hN)]
  · have h0 := onePoint_add (d := d) (N := N) (ℓ := ℓ) β ν
      (EuclideanSpace.single (idx₀ hN) 1) x 0 (idx₀ hN)
    rw [zero_add] at h0
    rw [h0, mul_comm]
    unfold blockM
    congr 1
    rw [← hR]
    rfl
  · intro j _ hj
    rw [onePoint_stab_zero β ν (idx₀ hN) x j hj, mul_zero]
  · simp

theorem twoPointTruncated_eq_block (hN : 2 ≤ N) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (hh : ‖h‖ = 1) (x y : Torus d ℓ) (i k : Fin N) :
    twoPointTruncated d N ℓ β ν h x y i k =
      blockGtr d N ℓ hN β ν (x - y) * ((if i = k then 1 else 0) - h i * h k)
        + blockGlg d N ℓ hN β ν (x - y) * (h i * h k) := by
  obtain ⟨R, hR⟩ := exists_rot_single hN h hh
  have key := twoPointTruncated_rot R β ν (EuclideanSpace.single (idx₀ hN) 1) x y i k
  rw [hR] at key
  rw [key]
  have hdiag : ∀ j : Fin N, ∑ l, rotEntry R i j * rotEntry R k l *
      twoPointTruncated d N ℓ β ν (EuclideanSpace.single (idx₀ hN) 1) x y j l =
      rotEntry R i j * rotEntry R k j *
      (if j = idx₀ hN then blockGlg d N ℓ hN β ν (x - y) else blockGtr d N ℓ hN β ν (x - y)) := by
    intro j
    rw [Finset.sum_eq_single j]
    · congr 1
      rw [twoPointTruncated_sub]
      by_cases hj : j = idx₀ hN
      · subst hj; simp [blockGlg]
      · simp only [hj, ite_false, blockGtr]
        exact twoPointTruncated_stab_diag β ν (idx₀ hN) (x - y) 0 j (idx₁ hN) hj
          (idx₁_ne_idx₀ hN)
    · intro l _ hl
      rw [twoPointTruncated_stab_offDiag β ν (idx₀ hN) x y j l (Ne.symm hl), mul_zero]
    · simp
  simp only [hdiag]
  have hent : ∀ i : Fin N, rotEntry R i (idx₀ hN) = h i := by
    intro i
    rw [← hR]; rfl
  have horth := rotEntry_orth R i k
  have hsplit : ∀ j : Fin N, rotEntry R i j * rotEntry R k j *
      (if j = idx₀ hN then blockGlg d N ℓ hN β ν (x - y) else blockGtr d N ℓ hN β ν (x - y)) =
      rotEntry R i j * rotEntry R k j * blockGtr d N ℓ hN β ν (x - y) +
      (if j = idx₀ hN then rotEntry R i j * rotEntry R k j *
        (blockGlg d N ℓ hN β ν (x - y) - blockGtr d N ℓ hN β ν (x - y)) else 0) := by
    intro j
    by_cases hj : j = idx₀ hN
    · simp [hj]; ring
    · simp [hj]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, horth]
  simp [hent]
  split_ifs <;> ring

theorem blockGtr_neg (hN : 2 ≤ N) (β ν : ℝ) (z : Torus d ℓ) :
    blockGtr d N ℓ hN β ν (-z) = blockGtr d N ℓ hN β ν z := by
  unfold blockGtr
  rw [twoPointTruncated_comm, twoPointTruncated_sub]
  simp

theorem blockGlg_neg (hN : 2 ≤ N) (β ν : ℝ) (z : Torus d ℓ) :
    blockGlg d N ℓ hN β ν (-z) = blockGlg d N ℓ hN β ν z := by
  unfold blockGlg
  rw [twoPointTruncated_comm, twoPointTruncated_sub]
  simp

/-- Lemma 0.2 (c): the one- and two-point functions have the block structure, with scalars
independent of the direction `h` of the field. -/
theorem exists_block_structure (hN : 2 ≤ N) (β ν : ℝ) :
    ∃ (m : ℝ) (Gtr Glg : Torus d ℓ → ℝ), ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
      ∀ (x y : Torus d ℓ) (i k : Fin N),
        onePoint d N ℓ β ν h x i = m * h i ∧
        twoPointTruncated d N ℓ β ν h x y i k =
          Gtr (x - y) * ((if i = k then 1 else 0) - h i * h k) + Glg (x - y) * (h i * h k) :=
  ⟨blockM d N ℓ hN β ν, blockGtr d N ℓ hN β ν, blockGlg d N ℓ hN β ν,
    fun h hh x y i k => ⟨onePoint_eq_blockM_mul hN β ν h hh x i,
      twoPointTruncated_eq_block hN β ν h hh x y i k⟩⟩

end Balaban
