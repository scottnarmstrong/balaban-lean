/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2XGreen
public import Balaban.Localization.Decoupled2Geometry
public import Balaban.Localization.DecoupledXLocal

/-!
# (DG5), (DG5'): locality of the x-variant decoupled Green's operator, for a cover `C`

`XCoverLocal` adds to `XCover` the geometry of the cover (`CoverLocalGeom`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Setting

variable (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (a : ℕ → ℝ) (aT ν Cx : ℝ)

/-- `XCover` together with the geometry of the cover used by the locality. -/
structure XCoverLocal : Prop extends XCover C H a aT ν Cx, CoverLocalGeom C H a ν Cx

end Setting

variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ}

theorem rowSupp_chi_cubeGx (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) (hα : AdmPot H α)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) :
    RowSupp (chiD C H q * cubeGx H a aT x ν α q) (intBox q) := by
  intro f y hy
  rw [← Matrix.mulVec_mulVec, chiD_mulVec, cubeGx_supp S hα hx hq f y hy, mul_zero]

theorem rowSupp_Kzx_cubeGx (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) : RowSupp (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) (intBox q) := by
  intro f y hy
  by_contra hne
  rw [← Matrix.mulVec_mulVec] at hne
  exact hy (inner_of_Kzx_ne_zero S hq _ y hne).self

/-- The cube Green's function only depends on the potential inside the cube. -/
theorem cubeGx_congr (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α)
    (hα' : AdmPot H α') {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx)
    (hαα : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q → α y = α' y) :
    cubeGx H a aT x ν α q = cubeGx H a aT x ν α' q := by
  refine matrix_ext_mulVec fun f => ?_
  set u : H.Ω 1 → ℂ := cubeGx H a aT x ν α q *ᵥ f with hu
  have hsupp : ∀ z : H.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → u z = 0 :=
    fun z hz => cubeGx_supp S hα hx hq f z hz
  have hH : cubeHx H a aT x ν α q *ᵥ u = cD H q *ᵥ f := cubeHx_cubeGx S hα hx hq f
  have hH' : cubeHx H a aT x ν α' q *ᵥ u = cD H q *ᵥ f := by
    funext y
    by_cases hyb : (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q
    · have e := cutXOperator_eq_add (G := H) a aT x ν (cubeCut H (intBox q)) α'
      have e0 := cutXOperator_eq_add (G := H) a aT x ν (cubeCut H (intBox q)) α
      have h1 : (cubeHx H a aT x ν α' q *ᵥ u) y = (cutXOperator H a aT x ν (cubeCut H (intBox q)) 0 *ᵥ u) y +
          α' y * u y := by
        unfold cubeHx; rw [e, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      have h2 : (cubeHx H a aT x ν α q *ᵥ u) y = (cutXOperator H a aT x ν (cubeCut H (intBox q)) 0 *ᵥ u) y +
          α y * u y := by
        unfold cubeHx; rw [e0, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
      rw [h1, ← hαα y hyb, ← h2, hH]
    · rw [cD_mulVec]
      simp only [hyb, ↓reduceIte]
      exact cutXOperator_mulVec_apply_of_not_mem (G := H) (a := a) (aT := aT) (x := x) (ν := ν)
        (α := α') (S.blockAligned q hq)
        (fun z hz => hsupp z hz) y hyb
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 (cubeHx_isUnit S hα' hx hq)
  rw [cubeGx_mulVec]
  have : cubeHx H a aT x ν α' q *ᵥ u = cD H q *ᵥ f := hH'
  rw [hu] at this
  calc cubeGx H a aT x ν α q *ᵥ f = u := rfl
    _ = (cubeHx H a aT x ν α' q)⁻¹ *ᵥ (cubeHx H a aT x ν α' q *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet', Matrix.one_mulVec]
    _ = (cubeHx H a aT x ν α' q)⁻¹ *ᵥ (cD H q *ᵥ f) := by rw [hH']


/-- **Locality of `G_s(A) f`** (the algebraic core of (DG5), (DG5')): if every interaction cube
with a non-zero factor lies inside `Y` or outside `Y`, the factors agree on the cubes inside `Y`,
and `A`, `f` agree on `Y`, then `G_s(A) f = G_{s'}(A') f'` on `Y`. -/
theorem Gsx_local (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C H a aT x ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, (C.sProd s q ≠ 0 ∨ C.sProd s' q ≠ 0) →
      SubI H (intBox q) Y ∨ DisjI H (intBox q) Y)
    (hagree : ∀ q ∈ C.cubeIdx, SubI H (intBox q) Y → C.sProd s q = C.sProd s' q)
    (hA : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → α y = α' y)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → f y = f' y) :
    ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      (Gsx C H a aT x ν α s *ᵥ f) y = (Gsx C H a aT x ν α' s' *ᵥ f') y := by
  classical
  intro y hyY
  have hd0 : (3 : ℕ) ≤ d := S.hd
  -- the hypotheses of `block_locality`
  have hMX : ∀ q ∈ C.cubeIdx, RowSupp (chiD C H q * cubeGx H a aT x ν α q) (intBox q) ∧
      chiD C H q * cubeGx H a aT x ν α q * cD H q = chiD C H q * cubeGx H a aT x ν α q := by
    intro q hq
    exact ⟨rowSupp_chi_cubeGx S hx hα hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  have hMX' : ∀ q ∈ C.cubeIdx, RowSupp (chiD C H q * cubeGx H a aT x ν α' q) (intBox q) ∧
      chiD C H q * cubeGx H a aT x ν α' q * cD H q = chiD C H q * cubeGx H a aT x ν α' q := by
    intro q hq
    exact ⟨rowSupp_chi_cubeGx S hx hα' hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  have hMK : ∀ q ∈ C.cubeIdx, RowSupp (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) (intBox q) ∧
      Kzx C H a aT x ν q * cubeGx H a aT x ν α q * cD H q = Kzx C H a aT x ν q * cubeGx H a aT x ν α q := by
    intro q hq
    exact ⟨rowSupp_Kzx_cubeGx S hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  have hMK' : ∀ q ∈ C.cubeIdx, RowSupp (Kzx C H a aT x ν q * cubeGx H a aT x ν α' q) (intBox q) ∧
      Kzx C H a aT x ν q * cubeGx H a aT x ν α' q * cD H q = Kzx C H a aT x ν q * cubeGx H a aT x ν α' q := by
    intro q hq
    exact ⟨rowSupp_Kzx_cubeGx S hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
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
  have hinnerK : ∑ q ∈ innerCentres C H Y, C.sProd s q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) =
      ∑ q ∈ innerCentres C H Y, C.sProd s' q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    rw [hagree q hq'.1 hq'.2, cubeGx_congr S hx hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
  have hinnerX : ∑ q ∈ innerCentres C H Y, C.sProd s q • (chiD C H q * cubeGx H a aT x ν α q) =
      ∑ q ∈ innerCentres C H Y, C.sProd s' q • (chiD C H q * cubeGx H a aT x ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    rw [hagree q hq'.1 hq'.2, cubeGx_congr S hx hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
  set P := indY H Y with hPdef
  have hKdef : Kcalx C H a aT x ν α s = ∑ q ∈ C.cubeIdx, C.sProd s q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) := rfl
  have hKdef' : Kcalx C H a aT x ν α' s' =
      ∑ q ∈ C.cubeIdx, C.sProd s' q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α' q) := rfl
  have hXdef : Gstarx C H a aT x ν α s = ∑ q ∈ C.cubeIdx, C.sProd s q • (chiD C H q * cubeGx H a aT x ν α q) := rfl
  have hXdef' : Gstarx C H a aT x ν α' s' =
      ∑ q ∈ C.cubeIdx, C.sProd s' q • (chiD C H q * cubeGx H a aT x ν α' q) := rfl
  have hP : P * P = P := indY_mul_self Y
  have hKP : P * Kcalx C H a aT x ν α s = Kcalx C H a aT x ν α s * P := by rw [hKdef, hK1, hK2]
  have hKP' : P * Kcalx C H a aT x ν α' s' = Kcalx C H a aT x ν α' s' * P := by rw [hKdef', hK1', hK2']
  have hcol : ∀ M : Matrix (H.Ω 1) (H.Ω 1) ℂ, P * M = M * P → P * M * P = P * M := by
    intro M hM
    calc P * M * P = P * (M * P) := Matrix.mul_assoc _ _ _
      _ = P * (P * M) := by rw [hM]
      _ = (P * P) * M := (Matrix.mul_assoc _ _ _).symm
      _ = P * M := by rw [hP]
  have hXc : P * Gstarx C H a aT x ν α s = Gstarx C H a aT x ν α s * P := by rw [hXdef, hX1, hX2]
  have hXc' : P * Gstarx C H a aT x ν α' s' = Gstarx C H a aT x ν α' s' * P := by rw [hXdef', hX1', hX2']
  have hXP : P * Gstarx C H a aT x ν α s = P * Gstarx C H a aT x ν α s * P := (hcol _ hXc).symm
  have hXP' : P * Gstarx C H a aT x ν α' s' = P * Gstarx C H a aT x ν α' s' * P := (hcol _ hXc').symm
  have hPK : P * Kcalx C H a aT x ν α s * P = P * Kcalx C H a aT x ν α' s' * P := by
    rw [hcol _ hKP, hcol _ hKP', hKdef, hKdef', hK1, hK1', hinnerK]
  have hPX : P * Gstarx C H a aT x ν α s * P = P * Gstarx C H a aT x ν α' s' * P := by
    rw [hcol _ hXc, hcol _ hXc', hXdef, hXdef', hX1, hX1', hinnerX]
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdetK' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  have hg : (1 - Kcalx C H a aT x ν α s) *ᵥ ((1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f) = f := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have hg' : (1 - Kcalx C H a aT x ν α' s') *ᵥ ((1 - Kcalx C H a aT x ν α' s')⁻¹ *ᵥ f') = f' := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK', Matrix.one_mulVec]
  have hPf : P *ᵥ f = P *ᵥ f' := by
    funext y
    rw [hPdef, indY_mulVec, indY_mulVec]
    by_cases hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y
    · simp [hy, hf y hy]
    · simp [hy]
  have hKP1 : P * (1 - Kcalx C H a aT x ν α s) = (1 - Kcalx C H a aT x ν α s) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hKP]
  have key := block_locality (P := P) (K := Kcalx C H a aT x ν α s) (K' := Kcalx C H a aT x ν α' s')
    (X := Gstarx C H a aT x ν α s) (X' := Gstarx C H a aT x ν α' s') hP hKP hKP' hXP hXP' hPK hPX hU hPf hg hg'
  have e1 := congrFun key y
  rw [hPdef, indY_mulVec, indY_mulVec] at e1
  simp only [hyY, ↓reduceIte] at e1
  unfold Gsx
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact e1


/-- **(DG5), support.** `G_{k,x,s}(A) f` vanishes outside `Core(ℛ)`. -/
theorem dg5x_support (S : CoverLocalGeom C H a ν Cx) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (f : H.Ω 1 → ℂ) (y : H.Ω 1)
    (hy : (Gsx C H a aT x ν α s *ᵥ f) y ≠ 0) : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Core C s := by
  classical
  set g : H.Ω 1 → ℂ := (1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f with hg
  have e : Gsx C H a aT x ν α s *ᵥ f = Gstarx C H a aT x ν α s *ᵥ g := Gsx_mulVec f
  rw [e] at hy
  have h1 : zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) y ≠ 0 := by
    rw [zeroExt_mem' _ y.2]; exact hy
  rw [zeroExt_Gstarx] at h1
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hc : C.sProd s q ≠ 0 := left_ne_zero_of_mul hne
  have hchi : ((C.chi q y : ℝ) : ℂ) ≠ 0 := by
    have := right_ne_zero_of_mul hne
    exact left_ne_zero_of_mul this
  have hchi' : C.chi q y ≠ 0 := fun h0 => hchi (by simp [h0])
  unfold Core
  rw [Finset.mem_biUnion]
  refine ⟨q, Finset.mem_filter.2 ⟨hq, hc⟩, ?_⟩
  unfold coreBox
  rw [mem_boxSet]
  exact S.chi_supp q hq _ hchi'

/-- **(DG5), locality on a nearest-neighbour component.** -/
theorem dg5x_local (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) (hconn : HatConn C H) {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α)
    (hα' : AdmPot H α') {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C H a aT x ν α' s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg C H s) Y')
    (hA : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → f y = f' y) :
    ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' →
      (Gsx C H a aT x ν α s *ᵥ f) y = (Gsx C H a aT x ν α' s *ᵥ f') y := by
  classical
  refine Gsx_local S hx hα hα' hU hU' ?_ (fun _ _ _ => rfl) hA hf
  intro z hz hact
  have hzs : C.sProd s z ≠ 0 := by rcases hact with h | h <;> exact h
  have hzZ : z ∈ Zs C s := Finset.mem_filter.2 ⟨hz, hzs⟩
  have hsub : hatI H z ⊆ Yreg C H s := by
    intro y hy
    unfold hatI at hy
    rw [Finset.mem_filter] at hy
    unfold Yreg
    rw [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨⟨z, hzZ, hy.1⟩, hy.2⟩
  rcases connIn_dichotomy (hconn z hz) hsub hY with h | h
  · left
    intro y hy
    exact h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox z hy, y.2⟩)
  · right
    intro y hy hyY
    exact Finset.disjoint_left.1 h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox z hy, y.2⟩) hyY


/-- **(DG5'), termwise comparison.**  Let `𝒞 ⊂ cubeIdx`, `Y` a union of nearest-neighbour
components of `V(𝒞) ∩ Ω₁`; `s, s'` equal to `1` off `𝔓` and `0` on `𝔓 ∖ 𝒞`, agreeing on the cubes of
`𝒞` inside `Y`; `A = A'`, `f = f'` on `Y`.  Then `G_s(A) f = G_{s'}(A') f'` on
`Core_Y = ⋃_{z ∈ Z_Y} C_z`. -/
theorem dg5x' (S : XCoverLocal C H a aT ν Cx) (hx : 0 ≤ x) (hconn : HatConn C H) {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun y => y ∈ H.Ω 1) Y)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C H a aT x ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → s P = s' P)
    (hA : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → α y = α' y)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → f y = f' y) :
    ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (ZY C H X₁ 𝒞 Y).biUnion coreBox →
      (Gsx C H a aT x ν α s *ᵥ f) y = (Gsx C H a aT x ν α' s' *ᵥ f') y := by
  classical
  -- active centres only see parameter cubes of `𝒞`
  have hact : ∀ (u : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ), (∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) →
      ∀ z, C.sProd u z ≠ 0 → ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
    intro u hu z hz P hP hPP
    by_contra hPC
    exact (sProd_ne_zero_iff u z |>.1 hz) P hP (hu P hPP hPC)
  -- the thickened cube of an active centre lies in `V(𝒞) ∩ Ω₁`
  have hhat : ∀ z ∈ C.cubeIdx, (∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞) →
      hatI H z ⊆ (Vset X₁ 𝒞).filter fun y => y ∈ H.Ω 1 := by
    intro z hz hP y hy
    unfold hatI at hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hxh, hxΩ⟩ := hy
    obtain ⟨P, hown, hyP⟩ := S.own_cover y hxΩ
    have hQ : P ∈ C.Qset z := C.mem_Qset.2 ⟨hown, y, mem_cubeP.1 hyP, mem_boxSet.1 hxh⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hxΩ⟩
    unfold Vset
    rw [Finset.mem_union]
    by_cases hPP : P ∈ C.parCubes X₁
    · right
      rw [Finset.mem_biUnion]
      exact ⟨_, hP _ hQ hPP, hyP⟩
    · left
      have : cubeP P ⊆ X₁ := by
        by_contra hc
        exact hPP (Finset.mem_filter.2 ⟨hown, hc⟩)
      exact this hyP
  have hdich : ∀ z ∈ C.cubeIdx, (C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) →
      SubI H (intBox z) Y ∨ DisjI H (intBox z) Y := by
    intro z hz hactive
    have hP : ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
      rcases hactive with h | h
      · exact hact s (fun P hP hPC => (hs0 P hP hPC).1) z h
      · exact hact s' (fun P hP hPC => (hs0 P hP hPC).2) z h
    rcases connIn_dichotomy (hconn z hz) (hhat z hz hP) hY with h | h
    · left
      intro y hy
      exact h (by
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨box_subset_hatBox z hy, y.2⟩)
    · right
      intro y hy hyY
      exact Finset.disjoint_left.1 h (by
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨box_subset_hatBox z hy, y.2⟩) hyY
  have hagree : ∀ z ∈ C.cubeIdx, SubI H (intBox z) Y → C.sProd s z = C.sProd s' z := by
    intro z hz hbox
    by_cases hactive : C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0
    · have hP : ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
        rcases hactive with h | h
        · exact hact s (fun P hP hPC => (hs0 P hP hPC).1) z h
        · exact hact s' (fun P hP hPC => (hs0 P hP hPC).2) z h
      -- the base point of `z` lies in `□_z ∩ Ω₁`, hence in `Y`
      have hbaseΩ : z.2 ∈ H.Ω 1 := S.cubeP_sub z hz z.2 (mem_cubeP.2 (SameCell.refl _ _))
      have hbasebox : z.2 ∈ intBox z := by
        rw [mem_intBox]
        intro μ
        refine ⟨0, ?_⟩
        have hB : (1 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) :=
          one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
        simp only [Int.cast_zero, zero_mul, add_zero]
        rw [abs_lt]
        constructor <;> nlinarith
      have hbaseY : z.2 ∈ Y := hbox ⟨z.2, hbaseΩ⟩ hbasebox
      have hhatY : hatI H z ⊆ Y := by
        rcases connIn_dichotomy (hconn z hz) (hhat z hz hP) hY with h | h
        · exact h
        · exfalso
          exact Finset.disjoint_left.1 h (by
            unfold hatI
            rw [Finset.mem_filter]
            exact ⟨box_subset_hatBox z hbasebox, hbaseΩ⟩) hbaseY
      unfold DecCover.sProd
      refine Finset.prod_congr rfl fun P hPQ => ?_
      by_cases hPP : P ∈ C.parCubes X₁
      · by_cases hPC : P ∈ 𝒞
        · obtain ⟨hPi, y, hy, hyhat⟩ := C.mem_Qset.1 hPQ
          have hyP : y ∈ cubeP P := mem_cubeP.2 hy
          have hyΩ : y ∈ H.Ω 1 := cubeP_subset_Ω' S.toCoverLocalGeom hPi hyP
          have hyY : y ∈ Y := hhatY (by
            unfold hatI
            rw [Finset.mem_filter]
            exact ⟨mem_boxSet.2 hyhat, hyΩ⟩)
          have hsubV : cubeP P ⊆ (Vset X₁ 𝒞).filter fun y => y ∈ H.Ω 1 := by
            intro y hy
            rw [Finset.mem_filter]
            refine ⟨?_, cubeP_subset_Ω' S.toCoverLocalGeom hPi hy⟩
            unfold Vset
            rw [Finset.mem_union]
            right
            exact Finset.mem_biUnion.2 ⟨P, hPC, hy⟩
          have hsubY : SubI H (cubeP P) Y := by
            rcases connIn_dichotomy (cubeP_connIn' S.toCoverLocalGeom hPi) hsubV hY with h | h
            · intro y hy; exact h hy
            · exfalso; exact Finset.disjoint_left.1 h hyP hyY
          exact hag P hPC hsubY
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P (C.mem_Qset.1 hPQ).1 hPP).1, (hs1 P (C.mem_Qset.1 hPQ).1 hPP).2]
    · push Not at hactive
      rw [hactive.1, hactive.2]
  intro y hy
  obtain ⟨z, hzZ, hyz⟩ := Finset.mem_biUnion.1 hy
  have hzZ' := Finset.mem_filter.1 hzZ
  have hsub := hzZ'.2.2
  have hybox : (y : CTorus d L N₁ m₁ (k + 1)) ∈ hatBox z := by
    refine box_subset_hatBox z (coreBox_subset_box hyz)
  have hyY : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y := hsub y hybox
  exact Gsx_local S.toXCover hx hα hα' hU hU' hdich hagree hA hf y hyY


end Balaban.Localization.Dec2
