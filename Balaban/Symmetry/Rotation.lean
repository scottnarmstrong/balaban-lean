/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Rotating a pair of real vectors to normal form

For real vectors `ψ ≠ 0` and `h` in `ℝ^ι` and distinct indices `i ≠ j` there is a real matrix
`M` with `Mᵀ M = 1` such that `M ψ = |ψ| e_i` and `M h = c e_i + s e_j`, where `c = ψ·h / |ψ|`
and `s = √(|h|² - c²)` (`exists_rotation`).  This is the rotation `R₁, R₂` of P1 (3.24), (3.25).
-/

@[expose] public section

open Matrix

namespace Balaban.Symmetry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "𝔼" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
theorem inner_toLp (x y : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 x : 𝔼) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

/-- The matrix of an orthonormal basis (rows are the basis vectors). -/
noncomputable def basisMatrix (b : OrthonormalBasis ι ℝ 𝔼) : Matrix ι ι ℝ := Matrix.of fun k l => b k l

omit [DecidableEq ι] in
theorem basisMatrix_mulVec (b : OrthonormalBasis ι ℝ 𝔼) (x : ι → ℝ) (k : ι) :
    (basisMatrix b *ᵥ x) k = inner ℝ (b k) (WithLp.toLp 2 x : 𝔼) := by
  have : inner ℝ (b k) (WithLp.toLp 2 x : 𝔼) = (b k).ofLp ⬝ᵥ x := by
    have h := inner_toLp (b k).ofLp x
    simpa using h
  rw [this]
  simp [basisMatrix, Matrix.mulVec, dotProduct]

theorem basisMatrix_transpose_mul (b : OrthonormalBasis ι ℝ 𝔼) :
    (basisMatrix b)ᵀ * basisMatrix b = 1 := by
  have h : basisMatrix b * (basisMatrix b)ᵀ = 1 := by
    ext k k'
    have := orthonormal_iff_ite.mp b.orthonormal k k'
    have h2 : inner ℝ (b k) (b k') = (b k).ofLp ⬝ᵥ (b k').ofLp := by
      have h := inner_toLp (b k).ofLp (b k').ofLp
      simpa using h
    rw [h2] at this
    simpa [basisMatrix, Matrix.mul_apply, Matrix.one_apply, dotProduct] using this
  exact mul_eq_one_comm.mp h

omit [DecidableEq ι] in
theorem exists_basis_single {i : ι} {u : 𝔼} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis ι ℝ 𝔼, b i = u := by
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := 𝔼) (by simp) (v := fun _ : ι => u) (s := {i})
    (by rw [orthonormal_subsingleton_iff]; intro a; exact hu)
  exact ⟨b, hb i rfl⟩

theorem exists_basis_pair {i j : ι} (hij : i ≠ j) {u₁ u₂ : 𝔼} (h1 : ‖u₁‖ = 1) (h2 : ‖u₂‖ = 1)
    (h12 : inner ℝ u₁ u₂ = 0) :
    ∃ b : OrthonormalBasis ι ℝ 𝔼, b i = u₁ ∧ b j = u₂ := by
  classical
  set v : ι → 𝔼 := fun k => if k = i then u₁ else if k = j then u₂ else 0 with hv
  have hvi : v i = u₁ := by simp [hv]
  have hvj : v j = u₂ := by simp [hv, hij.symm]
  have h21 : inner ℝ u₂ u₁ = 0 := by rw [real_inner_comm]; exact h12
  have hs : Orthonormal ℝ (({i, j} : Set ι).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : a = i ∨ a = j := by simpa using ha
    have hb' : b = i ∨ b = j := by simpa using hb
    simp only [Set.domRestrict_apply, Subtype.mk.injEq]
    rcases ha' with ha1 | ha1 <;> rcases hb' with hb1 | hb1 <;> simp only [ha1, hb1]
    · simp [hvi, h1]
    · simp [hvi, hvj, hij, h12]
    · simp [hvi, hvj, hij.symm, h21]
    · simp [hvj, h2]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := 𝔼) (by simp) hs
  exact ⟨b, by rw [hb i (by simp), hvi], by rw [hb j (by simp), hvj]⟩

/-- **Rotation to normal form** (P1 (3.24), (3.25)). -/
theorem exists_rotation {i j : ι} (hij : i ≠ j) (ψ h : ι → ℝ) (hψ : ψ ≠ 0) :
    ∃ M : Matrix ι ι ℝ, Mᵀ * M = 1 ∧
      M *ᵥ ψ = Real.sqrt (ψ ⬝ᵥ ψ) • (Pi.single i 1 : ι → ℝ) ∧
      M *ᵥ h = (ψ ⬝ᵥ h / Real.sqrt (ψ ⬝ᵥ ψ)) • (Pi.single i 1 : ι → ℝ) +
        Real.sqrt (h ⬝ᵥ h - (ψ ⬝ᵥ h / Real.sqrt (ψ ⬝ᵥ ψ)) ^ 2) • (Pi.single j 1 : ι → ℝ) := by
  have hψψ : 0 < ψ ⬝ᵥ ψ := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (Ne.symm ?_)
    intro h0; exact hψ (dotProduct_self_eq_zero.mp h0)
  set r : ℝ := Real.sqrt (ψ ⬝ᵥ ψ) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hψψ
  have hr2 : r ^ 2 = ψ ⬝ᵥ ψ := Real.sq_sqrt hψψ.le
  set X : 𝔼 := WithLp.toLp 2 ψ with hX
  set Y : 𝔼 := WithLp.toLp 2 h with hY
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : 𝔼, u₁ = r⁻¹ • X := ⟨_, rfl⟩
  set c : ℝ := ψ ⬝ᵥ h / r with hc
  set t : 𝔼 := Y - c • u₁ with ht
  have hXX : inner ℝ X X = r ^ 2 := by rw [hX, inner_toLp, hr2]
  have hXY : inner ℝ X Y = ψ ⬝ᵥ h := by rw [hX, hY, inner_toLp]
  have hYY : inner ℝ Y Y = h ⬝ᵥ h := by rw [hY, inner_toLp]
  have h11 : inner ℝ u₁ u₁ = 1 := by
    rw [hu₁, real_inner_smul_left, real_inner_smul_right, hXX]; field_simp
  have h1Y : inner ℝ u₁ Y = c := by
    rw [hu₁, real_inner_smul_left, hXY, hc]; field_simp
  have h1t : inner ℝ u₁ t = 0 := by
    rw [ht, inner_sub_right, real_inner_smul_right, h11, h1Y]; ring
  have htt : inner ℝ t t = h ⬝ᵥ h - c ^ 2 := by
    have h1Y' : inner ℝ Y u₁ = c := by rw [real_inner_comm]; exact h1Y
    simp only [ht, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      h11, h1Y, h1Y', hYY]
    ring
  set s : ℝ := ‖t‖ with hs
  have hs2 : s ^ 2 = h ⬝ᵥ h - c ^ 2 := by rw [hs, ← real_inner_self_eq_norm_sq, htt]
  have hsqrt : Real.sqrt (h ⬝ᵥ h - c ^ 2) = s := by
    rw [← hs2]; exact Real.sqrt_sq (norm_nonneg _)
  have hu1n : ‖u₁‖ = 1 := by
    have : ‖u₁‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, h11]
    nlinarith [norm_nonneg u₁]
  -- a basis adapted to `u₁` and `t`
  obtain ⟨b, hb1, hb2⟩ : ∃ b : OrthonormalBasis ι ℝ 𝔼,
      (∀ k, inner ℝ (b k) u₁ = if k = i then (1 : ℝ) else 0) ∧
      (∀ k, inner ℝ (b k) t = s * if k = j then (1 : ℝ) else 0) := by
    by_cases hs0 : s = 0
    · have ht0 : t = 0 := norm_eq_zero.mp hs0
      obtain ⟨b, hb⟩ := exists_basis_single (i := i) hu1n
      refine ⟨b, fun k => ?_, fun k => ?_⟩
      · rw [← hb]; exact orthonormal_iff_ite.mp b.orthonormal k i
      · simp [ht0, hs0]
    · have hspos : 0 < s := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0)
      set u₂ : 𝔼 := s⁻¹ • t with hu₂
      have hu2n : ‖u₂‖ = 1 := by
        rw [hu₂, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hspos]
        exact inv_mul_cancel₀ hspos.ne'
      have h12 : inner ℝ u₁ u₂ = 0 := by rw [hu₂, real_inner_smul_right, h1t]; ring
      obtain ⟨b, hbi, hbj⟩ := exists_basis_pair hij hu1n hu2n h12
      have htu : t = s • u₂ := by rw [hu₂, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      refine ⟨b, fun k => ?_, fun k => ?_⟩
      · rw [← hbi]; exact orthonormal_iff_ite.mp b.orthonormal k i
      · rw [htu, real_inner_smul_right, ← hbj]
        rw [orthonormal_iff_ite.mp b.orthonormal k j]
  refine ⟨basisMatrix b, basisMatrix_transpose_mul b, ?_, ?_⟩
  · funext k
    rw [basisMatrix_mulVec]
    have hXr : X = r • u₁ := by rw [hu₁, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [← hX, hXr, real_inner_smul_right, hb1]
    simp [Pi.single_apply]
  · funext k
    rw [basisMatrix_mulVec]
    have hYc : Y = c • u₁ + t := by rw [ht]; abel
    rw [← hY, hYc, inner_add_right, real_inner_smul_right, hb1, hb2]
    simp [Pi.single_apply, hsqrt]

end Balaban.Symmetry
