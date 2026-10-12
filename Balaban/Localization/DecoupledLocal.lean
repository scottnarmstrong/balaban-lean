/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledAnalytic

/-!
# (DG5), (DG5'): locality of the decoupled Green's operator

The algebraic mechanism.  Let `P` be the multiplication by the indicator of a set `Y` and suppose
every interaction cube with a non-zero factor `s_z` lies either inside `Y` or outside `Y`.  Then
`G*_s`, `𝒦_s` commute with `P`, and `P G_s f` depends on `(s, A, f)` only through the cubes inside
`Y` (`Gs_local`): this is the block argument `block_locality`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Block locality.** `P` idempotent, `K`, `K'` commute with `P`, `1 - K` invertible,
`P K P = P K' P`, `P X = P X P`, `P X P = P X' P` imply that `P X g` only depends on `P f`, where
`(1 - K) g = f`, `(1 - K') g' = f'`. -/
theorem block_locality {P K K' X X' : Matrix ι ι ℂ} {f f' g g' : ι → ℂ}
    (hP : P * P = P) (hKP : P * K = K * P) (hKP' : P * K' = K' * P)
    (hXP : P * X = P * X * P) (hXP' : P * X' = P * X' * P)
    (hPK : P * K * P = P * K' * P) (hPX : P * X * P = P * X' * P)
    (hU : IsUnit (1 - K)) (hf : P *ᵥ f = P *ᵥ f')
    (hg : (1 - K) *ᵥ g = f) (hg' : (1 - K') *ᵥ g' = f') :
    P *ᵥ (X *ᵥ g) = P *ᵥ (X' *ᵥ g') := by
  have hcomm : ∀ v, P *ᵥ (K *ᵥ v) = K *ᵥ (P *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hKP]
  have hcomm' : ∀ v, P *ᵥ (K' *ᵥ v) = K' *ᵥ (P *ᵥ v) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hKP']
  have F1 : K * P = P * K * P := by rw [hKP, Matrix.mul_assoc, hP]
  have F1' : K' * P = P * K' * P := by rw [hKP', Matrix.mul_assoc, hP]
  have hPg : (1 - K) *ᵥ (P *ᵥ g) = P *ᵥ f := by
    calc (1 - K) *ᵥ (P *ᵥ g) = P *ᵥ g - K *ᵥ (P *ᵥ g) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = P *ᵥ g - P *ᵥ (K *ᵥ g) := by rw [hcomm]
      _ = P *ᵥ (g - K *ᵥ g) := by rw [Matrix.mulVec_sub]
      _ = P *ᵥ ((1 - K) *ᵥ g) := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = P *ᵥ f := by rw [hg]
  have hPg' : P *ᵥ g' - K' *ᵥ (P *ᵥ g') = P *ᵥ f' := by
    calc P *ᵥ g' - K' *ᵥ (P *ᵥ g') = P *ᵥ g' - P *ᵥ (K' *ᵥ g') := by rw [hcomm']
      _ = P *ᵥ (g' - K' *ᵥ g') := by rw [Matrix.mulVec_sub]
      _ = P *ᵥ ((1 - K') *ᵥ g') := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = P *ᵥ f' := by rw [hg']
  have hKK : K *ᵥ (P *ᵥ g') = K' *ᵥ (P *ᵥ g') := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, F1, F1', hPK]
  have hPgg : P *ᵥ g = P *ᵥ g' := by
    have h1 : (1 - K) *ᵥ (P *ᵥ g - P *ᵥ g') = 0 := by
      rw [Matrix.mulVec_sub, hPg, Matrix.sub_mulVec, Matrix.one_mulVec, hKK, hPg', hf, sub_self]
    have h0 : P *ᵥ g - P *ᵥ g' = 0 := by
      apply Matrix.mulVec_injective_iff_isUnit.2 hU
      rw [h1, Matrix.mulVec_zero]
    exact sub_eq_zero.1 h0
  calc P *ᵥ (X *ᵥ g) = (P * X) *ᵥ g := by rw [Matrix.mulVec_mulVec]
    _ = (P * X * P) *ᵥ g := by rw [← hXP]
    _ = (P * X) *ᵥ (P *ᵥ g) := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (P * X) *ᵥ (P *ᵥ g') := by rw [hPgg]
    _ = (P * X * P) *ᵥ g' := by rw [Matrix.mulVec_mulVec]
    _ = (P * X' * P) *ᵥ g' := by rw [hPX]
    _ = (P * X') *ᵥ g' := by rw [← hXP']
    _ = P *ᵥ (X' *ᵥ g') := by rw [Matrix.mulVec_mulVec]

end Abstract

section Cubes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- The multiplication by the indicator of a set `Y` of sites. -/
noncomputable def indY (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Matrix.diagonal fun x => if (x : CTorus d L N₁ m₁ K) ∈ Y then 1 else 0

theorem indY_mulVec (Y : Finset (CTorus d L N₁ m₁ K)) (v : G.Ω 1 → ℂ) (x : G.Ω 1) :
    (indY G Y *ᵥ v) x = if (x : CTorus d L N₁ m₁ K) ∈ Y then v x else 0 := by
  classical
  unfold indY
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem indY_mul_self (Y : Finset (CTorus d L N₁ m₁ K)) : indY G Y * indY G Y = indY G Y := by
  classical
  unfold indY
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

theorem cD_mul_self (q : ℕ × CTorus d L N₁ m₁ K) : cD G q * cD G q = cD G q := by
  classical
  unfold cD
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

theorem cD_mul_indY_of_subset {q : ℕ × CTorus d L N₁ m₁ K} {Y : Finset (CTorus d L N₁ m₁ K)}
    (h : box q ⊆ Y) : cD G q * indY G Y = cD G q := by
  classical
  unfold cD indY
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ box q
  · simp [hx, h hx]
  · simp [hx]

theorem cD_mul_indY_of_disjoint {q : ℕ × CTorus d L N₁ m₁ K} {Y : Finset (CTorus d L N₁ m₁ K)}
    (h : Disjoint (box q) Y) : cD G q * indY G Y = 0 := by
  classical
  unfold cD indY
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1; funext x
  by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ box q
  · have : (x : CTorus d L N₁ m₁ K) ∉ Y := fun hy => Finset.disjoint_left.1 h hx hy
    simp [hx, this]
  · simp [hx]

/-- A matrix whose output is supported in a set `B`. -/
def RowSupp (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) (B : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ (f : G.Ω 1 → ℂ) (x : G.Ω 1), (x : CTorus d L N₁ m₁ K) ∉ B → (M *ᵥ f) x = 0

theorem indY_mul_of_rowSupp {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {B Y : Finset (CTorus d L N₁ m₁ K)}
    (hM : RowSupp M B) (h : B ⊆ Y) : indY G Y * M = M := by
  refine matrix_ext_mulVec fun f => ?_
  funext x
  rw [← Matrix.mulVec_mulVec, indY_mulVec]
  by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ B
  · simp [h hx]
  · rw [hM f x hx]; simp

theorem indY_mul_of_rowSupp_disjoint {M : Matrix (G.Ω 1) (G.Ω 1) ℂ}
    {B Y : Finset (CTorus d L N₁ m₁ K)} (hM : RowSupp M B) (h : Disjoint B Y) :
    indY G Y * M = 0 := by
  refine matrix_ext_mulVec fun f => ?_
  funext x
  rw [← Matrix.mulVec_mulVec, indY_mulVec]
  by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ Y
  · have : (x : CTorus d L N₁ m₁ K) ∉ B := fun hb => Finset.disjoint_left.1 h hb hx
    simp [hx, hM f x this]
  · simp [hx]

variable {α : G.Ω 1 → ℂ}

theorem cubeG_mul_cD (q : ℕ × CTorus d L N₁ m₁ K) :
    cubeG G a ν α q * cD G q = cubeG G a ν α q := by
  unfold cubeG
  rw [Matrix.mul_assoc, cD_mul_self]

theorem rowSupp_chi_cubeG (S : DGSetting G a ν) (hα : AdmPot G α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : RowSupp (chiD G q * cubeG G a ν α q) (box q) := by
  intro f x hx
  rw [← Matrix.mulVec_mulVec, chiD_mulVec, cubeG_supp S hα hq f x hx, mul_zero]

theorem rowSupp_Kz_cubeG (S : DGSetting G a ν) (hα : AdmPot G α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : RowSupp (Kz G a ν q * cubeG G a ν α q) (box q) := by
  intro f x hx
  by_contra hne
  rw [← Matrix.mulVec_mulVec] at hne
  exact hx (inner_of_Kz_ne_zero S hq _ x hne).self

/-- The cube Green's function only depends on the potential inside the cube. -/
theorem cubeG_congr (S : DGSetting G a ν) {α α' : G.Ω 1 → ℂ} (hα : AdmPot G α)
    (hα' : AdmPot G α') {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    (hαα : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ box q → α x = α' x) :
    cubeG G a ν α q = cubeG G a ν α' q := by
  refine matrix_ext_mulVec fun f => ?_
  set u : G.Ω 1 → ℂ := cubeG G a ν α q *ᵥ f with hu
  have hsupp : ∀ z : G.Ω 1, (z : CTorus d L N₁ m₁ K) ∉ box q → u z = 0 :=
    fun z hz => cubeG_supp S hα hq f z hz
  have hH : cubeH G a ν α q *ᵥ u = cD G q *ᵥ f := cubeH_cubeG S hα hq f
  have hH' : cubeH G a ν α' q *ᵥ u = cD G q *ᵥ f := by
    funext x
    by_cases hxb : (x : CTorus d L N₁ m₁ K) ∈ box q
    · have e := cutOperator_eq_add (G := G) a ν (cubeCut G (box q)) α'
      have e0 := cutOperator_eq_add (G := G) a ν (cubeCut G (box q)) α
      have h1 : (cubeH G a ν α' q *ᵥ u) x = (cutOperator G a ν (cubeCut G (box q)) 0 *ᵥ u) x +
          α' x * u x := by
        unfold cubeH; rw [e, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      have h2 : (cubeH G a ν α q *ᵥ u) x = (cutOperator G a ν (cubeCut G (box q)) 0 *ᵥ u) x +
          α x * u x := by
        unfold cubeH; rw [e0, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      rw [h1, ← hαα x hxb, ← h2, hH]
    · rw [cD_mulVec]
      simp only [hxb, ↓reduceIte]
      exact cutOperator_mulVec_apply_of_not_mem G
        (box_blockAligned S.aligned S.cover_sep (by have := S.hL; omega) hq) α'
        (fun z hz => hsupp z hz) x hxb
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 (cubeH_isUnit S hα' hq)
  rw [cubeG_mulVec]
  have : cubeH G a ν α' q *ᵥ u = cD G q *ᵥ f := hH'
  rw [hu] at this
  calc cubeG G a ν α q *ᵥ f = u := rfl
    _ = (cubeH G a ν α' q)⁻¹ *ᵥ (cubeH G a ν α' q *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet', Matrix.one_mulVec]
    _ = (cubeH G a ν α' q)⁻¹ *ᵥ (cD G q *ᵥ f) := by rw [hH']

open Classical in
/-- The centres whose interaction cube lies inside `Y`. -/
noncomputable def innerCentres (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Y : Finset (CTorus d L N₁ m₁ K)) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun q => box q ⊆ Y

/-- If every summand either lives inside `Y` (commutes with `P`) or is annihilated by `P` on both
sides, then the sum commutes with `P` and `P (∑ B) = ∑_{inner} B`. -/
theorem sum_block_facts {Y : Finset (CTorus d L N₁ m₁ K)} (B : ℕ × CTorus d L N₁ m₁ K →
    Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (hin : ∀ q ∈ innerCentres G Y, indY G Y * B q = B q ∧ B q * indY G Y = B q)
    (hout : ∀ q ∈ cubeIdx G, q ∉ innerCentres G Y → indY G Y * B q = 0 ∧ B q * indY G Y = 0) :
    indY G Y * (∑ q ∈ cubeIdx G, B q) = ∑ q ∈ innerCentres G Y, B q ∧
    (∑ q ∈ cubeIdx G, B q) * indY G Y = ∑ q ∈ innerCentres G Y, B q := by
  classical
  have hsub : innerCentres G Y ⊆ cubeIdx G := Finset.filter_subset _ _
  constructor
  · rw [Matrix.mul_sum]
    rw [← Finset.sum_subset hsub (f := fun q => indY G Y * B q)]
    · exact Finset.sum_congr rfl fun q hq => (hin q hq).1
    · intro q hq hnq; exact (hout q hq hnq).1
  · rw [Matrix.sum_mul]
    rw [← Finset.sum_subset hsub (f := fun q => B q * indY G Y)]
    · exact Finset.sum_congr rfl fun q hq => (hin q hq).2
    · intro q hq hnq; exact (hout q hq hnq).2

theorem blk_conditions {Y : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (M : ℕ × CTorus d L N₁ m₁ K → Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (hM : ∀ q ∈ cubeIdx G, RowSupp (M q) (box q) ∧ M q * cD G q = M q)
    (hdich : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → box q ⊆ Y ∨ Disjoint (box q) Y) :
    (∀ q ∈ innerCentres G Y, indY G Y * (sProd G s q • M q) = sProd G s q • M q ∧
      (sProd G s q • M q) * indY G Y = sProd G s q • M q) ∧
    (∀ q ∈ cubeIdx G, q ∉ innerCentres G Y →
      indY G Y * (sProd G s q • M q) = 0 ∧ (sProd G s q • M q) * indY G Y = 0) := by
  classical
  constructor
  · intro q hq
    have hq' := Finset.mem_filter.1 hq
    obtain ⟨h1, h2⟩ := hM q hq'.1
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_smul, indY_mul_of_rowSupp h1 hq'.2]
    · rw [Matrix.smul_mul]
      congr 1
      calc M q * indY G Y = (M q * cD G q) * indY G Y := by rw [h2]
        _ = M q * (cD G q * indY G Y) := by rw [Matrix.mul_assoc]
        _ = M q := by rw [cD_mul_indY_of_subset hq'.2, h2]
  · intro q hq hnq
    obtain ⟨h1, h2⟩ := hM q hq
    by_cases hc : sProd G s q = 0
    · simp [hc]
    · have hdis : Disjoint (box q) Y := by
        rcases hdich q hq hc with h | h
        · exact absurd (Finset.mem_filter.2 ⟨hq, h⟩) hnq
        · exact h
      refine ⟨?_, ?_⟩
      · rw [Matrix.mul_smul, indY_mul_of_rowSupp_disjoint h1 hdis, smul_zero]
      · rw [Matrix.smul_mul]
        have : M q * indY G Y = 0 := by
          calc M q * indY G Y = (M q * cD G q) * indY G Y := by rw [h2]
            _ = M q * (cD G q * indY G Y) := by rw [Matrix.mul_assoc]
            _ = 0 := by rw [cD_mul_indY_of_disjoint hdis, Matrix.mul_zero]
        rw [this, smul_zero]

/-- **Locality of `G_s(A) f`** (the algebraic core of (DG5), (DG5')): if every interaction cube
with a non-zero factor lies inside `Y` or outside `Y`, the factors agree on the cubes inside `Y`,
and `A`, `f` agree on `Y`, then `G_s(A) f = G_{s'}(A') f'` on `Y`. -/
theorem Gs_local (S : DGSetting G a ν) {Y : Finset (CTorus d L N₁ m₁ K)}
    {α α' : G.Ω 1 → ℂ} (hα : AdmPot G α) (hα' : AdmPot G α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal G a ν α s)) (hU' : IsUnit (1 - Kcal G a ν α' s'))
    (hdich : ∀ q ∈ cubeIdx G, (sProd G s q ≠ 0 ∨ sProd G s' q ≠ 0) →
      box q ⊆ Y ∨ Disjoint (box q) Y)
    (hagree : ∀ q ∈ cubeIdx G, box q ⊆ Y → sProd G s q = sProd G s' q)
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → α x = α' x)
    {f f' : G.Ω 1 → ℂ} (hf : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → f x = f' x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (Gs G a ν α s *ᵥ f) x = (Gs G a ν α' s' *ᵥ f') x := by
  classical
  intro x hxY
  have hd0 : (3 : ℕ) ≤ d := S.hd
  -- the hypotheses of `block_locality`
  have hMX : ∀ q ∈ cubeIdx G, RowSupp (chiD G q * cubeG G a ν α q) (box q) ∧
      chiD G q * cubeG G a ν α q * cD G q = chiD G q * cubeG G a ν α q := by
    intro q hq
    exact ⟨rowSupp_chi_cubeG S hα hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hMX' : ∀ q ∈ cubeIdx G, RowSupp (chiD G q * cubeG G a ν α' q) (box q) ∧
      chiD G q * cubeG G a ν α' q * cD G q = chiD G q * cubeG G a ν α' q := by
    intro q hq
    exact ⟨rowSupp_chi_cubeG S hα' hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hMK : ∀ q ∈ cubeIdx G, RowSupp (Kz G a ν q * cubeG G a ν α q) (box q) ∧
      Kz G a ν q * cubeG G a ν α q * cD G q = Kz G a ν q * cubeG G a ν α q := by
    intro q hq
    exact ⟨rowSupp_Kz_cubeG S hα hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hMK' : ∀ q ∈ cubeIdx G, RowSupp (Kz G a ν q * cubeG G a ν α' q) (box q) ∧
      Kz G a ν q * cubeG G a ν α' q * cD G q = Kz G a ν q * cubeG G a ν α' q := by
    intro q hq
    exact ⟨rowSupp_Kz_cubeG S hα' hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  have hd1 : ∀ q ∈ cubeIdx G, sProd G s q ≠ 0 → box q ⊆ Y ∨ Disjoint (box q) Y :=
    fun q hq hc => hdich q hq (Or.inl hc)
  have hd2 : ∀ q ∈ cubeIdx G, sProd G s' q ≠ 0 → box q ⊆ Y ∨ Disjoint (box q) Y :=
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
  have hinnerK : ∑ q ∈ innerCentres G Y, sProd G s q • (Kz G a ν q * cubeG G a ν α q) =
      ∑ q ∈ innerCentres G Y, sProd G s' q • (Kz G a ν q * cubeG G a ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    rw [hagree q hq'.1 hq'.2, cubeG_congr S hα hα' hq'.1 (fun z hz => hA z (hq'.2 hz))]
  have hinnerX : ∑ q ∈ innerCentres G Y, sProd G s q • (chiD G q * cubeG G a ν α q) =
      ∑ q ∈ innerCentres G Y, sProd G s' q • (chiD G q * cubeG G a ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    rw [hagree q hq'.1 hq'.2, cubeG_congr S hα hα' hq'.1 (fun z hz => hA z (hq'.2 hz))]
  set P := indY G Y with hPdef
  have hKdef : Kcal G a ν α s = ∑ q ∈ cubeIdx G, sProd G s q • (Kz G a ν q * cubeG G a ν α q) := rfl
  have hKdef' : Kcal G a ν α' s' =
      ∑ q ∈ cubeIdx G, sProd G s' q • (Kz G a ν q * cubeG G a ν α' q) := rfl
  have hXdef : Gstar G a ν α s = ∑ q ∈ cubeIdx G, sProd G s q • (chiD G q * cubeG G a ν α q) := rfl
  have hXdef' : Gstar G a ν α' s' =
      ∑ q ∈ cubeIdx G, sProd G s' q • (chiD G q * cubeG G a ν α' q) := rfl
  have hP : P * P = P := indY_mul_self Y
  have hKP : P * Kcal G a ν α s = Kcal G a ν α s * P := by rw [hKdef, hK1, hK2]
  have hKP' : P * Kcal G a ν α' s' = Kcal G a ν α' s' * P := by rw [hKdef', hK1', hK2']
  have hcol : ∀ M : Matrix (G.Ω 1) (G.Ω 1) ℂ, P * M = M * P → P * M * P = P * M := by
    intro M hM
    calc P * M * P = P * (M * P) := Matrix.mul_assoc _ _ _
      _ = P * (P * M) := by rw [hM]
      _ = (P * P) * M := (Matrix.mul_assoc _ _ _).symm
      _ = P * M := by rw [hP]
  have hXc : P * Gstar G a ν α s = Gstar G a ν α s * P := by rw [hXdef, hX1, hX2]
  have hXc' : P * Gstar G a ν α' s' = Gstar G a ν α' s' * P := by rw [hXdef', hX1', hX2']
  have hXP : P * Gstar G a ν α s = P * Gstar G a ν α s * P := (hcol _ hXc).symm
  have hXP' : P * Gstar G a ν α' s' = P * Gstar G a ν α' s' * P := (hcol _ hXc').symm
  have hPK : P * Kcal G a ν α s * P = P * Kcal G a ν α' s' * P := by
    rw [hcol _ hKP, hcol _ hKP', hKdef, hKdef', hK1, hK1', hinnerK]
  have hPX : P * Gstar G a ν α s * P = P * Gstar G a ν α' s' * P := by
    rw [hcol _ hXc, hcol _ hXc', hXdef, hXdef', hX1, hX1', hinnerX]
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdetK' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  have hg : (1 - Kcal G a ν α s) *ᵥ ((1 - Kcal G a ν α s)⁻¹ *ᵥ f) = f := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have hg' : (1 - Kcal G a ν α' s') *ᵥ ((1 - Kcal G a ν α' s')⁻¹ *ᵥ f') = f' := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK', Matrix.one_mulVec]
  have hPf : P *ᵥ f = P *ᵥ f' := by
    funext y
    rw [hPdef, indY_mulVec, indY_mulVec]
    by_cases hy : (y : CTorus d L N₁ m₁ K) ∈ Y
    · simp [hy, hf y hy]
    · simp [hy]
  have hKP1 : P * (1 - Kcal G a ν α s) = (1 - Kcal G a ν α s) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hKP]
  have key := block_locality (P := P) (K := Kcal G a ν α s) (K' := Kcal G a ν α' s')
    (X := Gstar G a ν α s) (X' := Gstar G a ν α' s') hP hKP hKP' hXP hXP' hPK hPX hU hPf hg hg'
  have e1 := congrFun key x
  rw [hPdef, indY_mulVec, indY_mulVec] at e1
  simp only [hxY, ↓reduceIte] at e1
  unfold Gs
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact e1

end Cubes

end Balaban.Localization
