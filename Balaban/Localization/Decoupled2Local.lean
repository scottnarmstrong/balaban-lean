/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Analytic
public import Balaban.Localization.DecoupledLocal

/-!
# (DG5), (DG5'): locality of the decoupled Green's operator for a cover `C` and an operator `H`

The algebraic mechanism of `DecoupledLocal.lean` (`Gs_local`) with the cover read from `C`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

theorem rowSupp_chi_cubeG (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) : RowSupp (chiD C H q * cubeG H a ν α q) (intBox q) := by
  intro f x hx
  rw [← Matrix.mulVec_mulVec, chiD_mulVec, cubeG_supp S hα hq f x hx, mul_zero]

theorem rowSupp_Kz_cubeG (S : CoverBase C H a ν Kc Cx) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) : RowSupp (Kz C H a ν q * cubeG H a ν α q) (intBox q) := by
  intro f x hx
  by_contra hne
  rw [← Matrix.mulVec_mulVec] at hne
  exact hx (inner_of_Kz_ne_zero S hq _ x hne).self

/-- The cube Green's function only depends on the potential inside the cube. -/
theorem cubeG_congr (S : CoverBase C H a ν Kc Cx) {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α)
    (hα' : AdmPot H α') {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx)
    (hαα : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ intBox q → α x = α' x) :
    cubeG H a ν α q = cubeG H a ν α' q := by
  refine matrix_ext_mulVec fun f => ?_
  set u : H.Ω 1 → ℂ := cubeG H a ν α q *ᵥ f with hu
  have hsupp : ∀ z : H.Ω 1, (z : CTorus d L N₁ m₁ K) ∉ intBox q → u z = 0 :=
    fun z hz => cubeG_supp S hα hq f z hz
  have hH : cubeH H a ν α q *ᵥ u = cD H q *ᵥ f := cubeH_cubeG S hα hq f
  have hH' : cubeH H a ν α' q *ᵥ u = cD H q *ᵥ f := by
    funext x
    by_cases hxb : (x : CTorus d L N₁ m₁ K) ∈ intBox q
    · have e := cutOperator_eq_add (G := H) a ν (cubeCut H (intBox q)) α'
      have e0 := cutOperator_eq_add (G := H) a ν (cubeCut H (intBox q)) α
      have h1 : (cubeH H a ν α' q *ᵥ u) x = (cutOperator H a ν (cubeCut H (intBox q)) 0 *ᵥ u) x +
          α' x * u x := by
        unfold cubeH; rw [e, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      have h2 : (cubeH H a ν α q *ᵥ u) x = (cutOperator H a ν (cubeCut H (intBox q)) 0 *ᵥ u) x +
          α x * u x := by
        unfold cubeH; rw [e0, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      rw [h1, ← hαα x hxb, ← h2, hH]
    · rw [cD_mulVec]
      simp only [hxb, ↓reduceIte]
      exact cutOperator_mulVec_apply_of_not_mem H
        (S.blockAligned q hq) α'
        (fun z hz => hsupp z hz) x hxb
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 (cubeH_isUnit S hα' hq)
  rw [cubeG_mulVec]
  have : cubeH H a ν α' q *ᵥ u = cD H q *ᵥ f := hH'
  rw [hu] at this
  calc cubeG H a ν α q *ᵥ f = u := rfl
    _ = (cubeH H a ν α' q)⁻¹ *ᵥ (cubeH H a ν α' q *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet', Matrix.one_mulVec]
    _ = (cubeH H a ν α' q)⁻¹ *ᵥ (cD H q *ᵥ f) := by rw [hH']

open Classical in
/-- The centres whose interaction cube lies inside `Y`. -/
noncomputable def innerCentres (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Y : Finset (CTorus d L N₁ m₁ K)) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (C.cubeIdx).filter fun q => SubI H (intBox q) Y

/-- If every summand either lives inside `Y` (commutes with `P`) or is annihilated by `P` on both
sides, then the sum commutes with `P` and `P (∑ B) = ∑_{inner} B`. -/
theorem sum_block_facts {Y : Finset (CTorus d L N₁ m₁ K)} (B : ℕ × CTorus d L N₁ m₁ K →
    Matrix (H.Ω 1) (H.Ω 1) ℂ)
    (hin : ∀ q ∈ innerCentres C H Y, indY H Y * B q = B q ∧ B q * indY H Y = B q)
    (hout : ∀ q ∈ C.cubeIdx, q ∉ innerCentres C H Y → indY H Y * B q = 0 ∧ B q * indY H Y = 0) :
    indY H Y * (∑ q ∈ C.cubeIdx, B q) = ∑ q ∈ innerCentres C H Y, B q ∧
    (∑ q ∈ C.cubeIdx, B q) * indY H Y = ∑ q ∈ innerCentres C H Y, B q := by
  classical
  have hsub : innerCentres C H Y ⊆ C.cubeIdx := Finset.filter_subset _ _
  constructor
  · rw [Matrix.mul_sum]
    rw [← Finset.sum_subset hsub (f := fun q => indY H Y * B q)]
    · exact Finset.sum_congr rfl fun q hq => (hin q hq).1
    · intro q hq hnq; exact (hout q hq hnq).1
  · rw [Matrix.sum_mul]
    rw [← Finset.sum_subset hsub (f := fun q => B q * indY H Y)]
    · exact Finset.sum_congr rfl fun q hq => (hin q hq).2
    · intro q hq hnq; exact (hout q hq hnq).2

theorem blk_conditions {Y : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (M : ℕ × CTorus d L N₁ m₁ K → Matrix (H.Ω 1) (H.Ω 1) ℂ)
    (hM : ∀ q ∈ C.cubeIdx, RowSupp (M q) (intBox q) ∧ M q * cD H q = M q)
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) Y ∨ DisjI H (intBox q) Y) :
    (∀ q ∈ innerCentres C H Y, indY H Y * (C.sProd s q • M q) = C.sProd s q • M q ∧
      (C.sProd s q • M q) * indY H Y = C.sProd s q • M q) ∧
    (∀ q ∈ C.cubeIdx, q ∉ innerCentres C H Y →
      indY H Y * (C.sProd s q • M q) = 0 ∧ (C.sProd s q • M q) * indY H Y = 0) := by
  classical
  constructor
  · intro q hq
    have hq' := Finset.mem_filter.1 hq
    obtain ⟨h1, h2⟩ := hM q hq'.1
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_smul, indY_mul_of_rowSupp h1 hq'.2]
    · rw [Matrix.smul_mul]
      congr 1
      calc M q * indY H Y = (M q * cD H q) * indY H Y := by rw [h2]
        _ = M q * (cD H q * indY H Y) := by rw [Matrix.mul_assoc]
        _ = M q := by rw [cD_mul_indY_of_subset hq'.2, h2]
  · intro q hq hnq
    obtain ⟨h1, h2⟩ := hM q hq
    by_cases hc : C.sProd s q = 0
    · simp [hc]
    · have hdis : DisjI H (intBox q) Y := by
        rcases hdich q hq hc with h | h
        · exact absurd (Finset.mem_filter.2 ⟨hq, h⟩) hnq
        · exact h
      refine ⟨?_, ?_⟩
      · rw [Matrix.mul_smul, indY_mul_of_rowSupp_disjoint h1 hdis, smul_zero]
      · rw [Matrix.smul_mul]
        have : M q * indY H Y = 0 := by
          calc M q * indY H Y = (M q * cD H q) * indY H Y := by rw [h2]
            _ = M q * (cD H q * indY H Y) := by rw [Matrix.mul_assoc]
            _ = 0 := by rw [cD_mul_indY_of_disjoint hdis, Matrix.mul_zero]
        rw [this, smul_zero]

/-- **Locality of `G_s(A) f`** (the algebraic core of (DG5), (DG5')): if every interaction cube
with a non-zero factor lies inside `Y` or outside `Y`, the factors agree on the cubes inside `Y`,
and `A`, `f` agree on `Y`, then `G_s(A) f = G_{s'}(A') f'` on `Y`. -/
theorem Gs_local (S : CoverBase C H a ν Kc Cx) {Y : Finset (CTorus d L N₁ m₁ K)}
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, (C.sProd s q ≠ 0 ∨ C.sProd s' q ≠ 0) →
      SubI H (intBox q) Y ∨ DisjI H (intBox q) Y)
    (hagree : ∀ q ∈ C.cubeIdx, SubI H (intBox q) Y → C.sProd s q = C.sProd s' q)
    (hA : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → α x = α' x)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → f x = f' x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (Gs C H a ν α s *ᵥ f) x = (Gs C H a ν α' s' *ᵥ f') x := by
  classical
  intro x hxY
  have hd0 : (3 : ℕ) ≤ d := S.hd
  -- the hypotheses of `block_locality`
  have hMX : ∀ q ∈ C.cubeIdx, RowSupp (chiD C H q * cubeG H a ν α q) (intBox q) ∧
      chiD C H q * cubeG H a ν α q * cD H q = chiD C H q * cubeG H a ν α q := by
    intro q hq
    exact ⟨rowSupp_chi_cubeG S hα hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hMX' : ∀ q ∈ C.cubeIdx, RowSupp (chiD C H q * cubeG H a ν α' q) (intBox q) ∧
      chiD C H q * cubeG H a ν α' q * cD H q = chiD C H q * cubeG H a ν α' q := by
    intro q hq
    exact ⟨rowSupp_chi_cubeG S hα' hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hMK : ∀ q ∈ C.cubeIdx, RowSupp (Kz C H a ν q * cubeG H a ν α q) (intBox q) ∧
      Kz C H a ν q * cubeG H a ν α q * cD H q = Kz C H a ν q * cubeG H a ν α q := by
    intro q hq
    exact ⟨rowSupp_Kz_cubeG S hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hMK' : ∀ q ∈ C.cubeIdx, RowSupp (Kz C H a ν q * cubeG H a ν α' q) (intBox q) ∧
      Kz C H a ν q * cubeG H a ν α' q * cD H q = Kz C H a ν q * cubeG H a ν α' q := by
    intro q hq
    exact ⟨rowSupp_Kz_cubeG S hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hd1 : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) Y ∨ DisjI H (intBox q) Y :=
    fun q hq hc => hdich q hq (Or.inl hc)
  have hd2 : ∀ q ∈ C.cubeIdx, C.sProd s' q ≠ 0 → SubI H (intBox q) Y ∨ DisjI H (intBox q) Y :=
    fun q hq hc => hdich q hq (Or.inr hc)
  obtain ⟨hKin, hKout⟩ := blk_conditions (s := s) _ hMK hd1
  obtain ⟨hKin', hKout'⟩ := blk_conditions (s := s') _ hMK' hd2
  obtain ⟨hXin, hXout⟩ := blk_conditions (s := s) _ hMX hd1
  obtain ⟨hXin', hXout'⟩ := blk_conditions (s := s') _ hMX' hd2
  obtain ⟨hK1, hK2⟩ := sum_block_facts _ hKin hKout
  obtain ⟨hK1', hK2'⟩ := sum_block_facts _ hKin' hKout'
  obtain ⟨hX1, hX2⟩ := sum_block_facts _ hXin hXout
  obtain ⟨hX1', hX2'⟩ := sum_block_facts _ hXin' hXout'
  -- the inner sums coincide
  have hinnerK : ∑ q ∈ innerCentres C H Y, C.sProd s q • (Kz C H a ν q * cubeG H a ν α q) =
      ∑ q ∈ innerCentres C H Y, C.sProd s' q • (Kz C H a ν q * cubeG H a ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    rw [hagree q hq'.1 hq'.2, cubeG_congr S hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
  have hinnerX : ∑ q ∈ innerCentres C H Y, C.sProd s q • (chiD C H q * cubeG H a ν α q) =
      ∑ q ∈ innerCentres C H Y, C.sProd s' q • (chiD C H q * cubeG H a ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    rw [hagree q hq'.1 hq'.2, cubeG_congr S hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
  set P := indY H Y with hPdef
  have hKdef : Kcal C H a ν α s = ∑ q ∈ C.cubeIdx, C.sProd s q • (Kz C H a ν q * cubeG H a ν α q) := rfl
  have hKdef' : Kcal C H a ν α' s' =
      ∑ q ∈ C.cubeIdx, C.sProd s' q • (Kz C H a ν q * cubeG H a ν α' q) := rfl
  have hXdef : Gstar C H a ν α s = ∑ q ∈ C.cubeIdx, C.sProd s q • (chiD C H q * cubeG H a ν α q) := rfl
  have hXdef' : Gstar C H a ν α' s' =
      ∑ q ∈ C.cubeIdx, C.sProd s' q • (chiD C H q * cubeG H a ν α' q) := rfl
  have hP : P * P = P := indY_mul_self Y
  have hKP : P * Kcal C H a ν α s = Kcal C H a ν α s * P := by rw [hKdef, hK1, hK2]
  have hKP' : P * Kcal C H a ν α' s' = Kcal C H a ν α' s' * P := by rw [hKdef', hK1', hK2']
  have hcol : ∀ M : Matrix (H.Ω 1) (H.Ω 1) ℂ, P * M = M * P → P * M * P = P * M := by
    intro M hM
    calc P * M * P = P * (M * P) := Matrix.mul_assoc _ _ _
      _ = P * (P * M) := by rw [hM]
      _ = (P * P) * M := (Matrix.mul_assoc _ _ _).symm
      _ = P * M := by rw [hP]
  have hXc : P * Gstar C H a ν α s = Gstar C H a ν α s * P := by rw [hXdef, hX1, hX2]
  have hXc' : P * Gstar C H a ν α' s' = Gstar C H a ν α' s' * P := by rw [hXdef', hX1', hX2']
  have hXP : P * Gstar C H a ν α s = P * Gstar C H a ν α s * P := (hcol _ hXc).symm
  have hXP' : P * Gstar C H a ν α' s' = P * Gstar C H a ν α' s' * P := (hcol _ hXc').symm
  have hPK : P * Kcal C H a ν α s * P = P * Kcal C H a ν α' s' * P := by
    rw [hcol _ hKP, hcol _ hKP', hKdef, hKdef', hK1, hK1', hinnerK]
  have hPX : P * Gstar C H a ν α s * P = P * Gstar C H a ν α' s' * P := by
    rw [hcol _ hXc, hcol _ hXc', hXdef, hXdef', hX1, hX1', hinnerX]
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdetK' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  have hg : (1 - Kcal C H a ν α s) *ᵥ ((1 - Kcal C H a ν α s)⁻¹ *ᵥ f) = f := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have hg' : (1 - Kcal C H a ν α' s') *ᵥ ((1 - Kcal C H a ν α' s')⁻¹ *ᵥ f') = f' := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK', Matrix.one_mulVec]
  have hPf : P *ᵥ f = P *ᵥ f' := by
    funext y
    rw [hPdef, indY_mulVec, indY_mulVec]
    by_cases hy : (y : CTorus d L N₁ m₁ K) ∈ Y
    · simp [hy, hf y hy]
    · simp [hy]
  have hKP1 : P * (1 - Kcal C H a ν α s) = (1 - Kcal C H a ν α s) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hKP]
  have key := block_locality (P := P) (K := Kcal C H a ν α s) (K' := Kcal C H a ν α' s')
    (X := Gstar C H a ν α s) (X' := Gstar C H a ν α' s') hP hKP hKP' hXP hXP' hPK hPX hU hPf hg hg'
  have e1 := congrFun key x
  rw [hPdef, indY_mulVec, indY_mulVec] at e1
  simp only [hxY, ↓reduceIte] at e1
  unfold Gs
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact e1

end Balaban.Localization.Dec2
