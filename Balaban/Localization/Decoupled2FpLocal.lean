/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpGeometry
public import Balaban.Localization.Decoupled2Geometry

/-!
# Footprint locality of the decoupled Green's operator (VMOD-4)

`Gs_local_fp` (factor agreement at live centres only), `dg5_support_fp` (needs only `chi_core`),
the combinatorics of the incidence graph (`fp_dichT`, `fp_agreeT`, `fp_vanish`) and the
re-proved `dg5'_inner_fp`, `dg5'_fp`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- **Locality of `G_s(A) f`, live centres only** (the algebraic core of (DG5), (DG5')): as
`Gs_local`, but the factors are required to agree only at the centres whose interaction cube
contains an operator site (a centre without operator sites has `cubeG = 0`, `cubeG_dead`). -/
theorem Gs_local_fp (S : CoverBase C H a ν Kc Cx) {Y : Finset (CTorus d L N₁ m₁ K)}
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, (C.sProd s q ≠ 0 ∨ C.sProd s' q ≠ 0) →
      SubI H (intBox q) Y ∨ DisjI H (intBox q) Y)
    (hagree : ∀ q ∈ C.cubeIdx, LiveI H q → SubI H (intBox q) Y → C.sProd s q = C.sProd s' q)
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
    by_cases hl : LiveI H q
    · rw [hagree q hq'.1 hl hq'.2, cubeG_congr S hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
    · rw [cubeG_dead hl α, cubeG_dead hl α']
      simp
  have hinnerX : ∑ q ∈ innerCentres C H Y, C.sProd s q • (chiD C H q * cubeG H a ν α q) =
      ∑ q ∈ innerCentres C H Y, C.sProd s' q • (chiD C H q * cubeG H a ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    by_cases hl : LiveI H q
    · rw [hagree q hq'.1 hl hq'.2, cubeG_congr S hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
    · rw [cubeG_dead hl α, cubeG_dead hl α']
      simp
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


/-- **(DG5), support, from `chi_core` only.** `G_s(A) f` vanishes outside `Core(ℛ)`. -/
theorem dg5_support_fp (S : FootLocalGeom C) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (f : H.Ω 1 → ℂ)
    (x : H.Ω 1) (hx : (Gs C H a ν α s *ᵥ f) x ≠ 0) : (x : CTorus d L N₁ m₁ K) ∈ Core C s := by
  classical
  set g : H.Ω 1 → ℂ := (1 - Kcal C H a ν α s)⁻¹ *ᵥ f with hg
  have e : Gs C H a ν α s *ᵥ f = Gstar C H a ν α s *ᵥ g := by
    rw [hg, Gs, ← Matrix.mulVec_mulVec]
  rw [e] at hx
  have h1 : zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) x ≠ 0 := by
    rw [zeroExt_of_mem' x.2]; exact hx
  rw [Gstar_apply] at h1
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hc : C.sProd s q ≠ 0 := left_ne_zero_of_mul hne
  have hchi : ((C.chi q x : ℝ) : ℂ) ≠ 0 := by
    have := right_ne_zero_of_mul hne
    exact left_ne_zero_of_mul this
  have hchi' : C.chi q x ≠ 0 := fun h0 => hchi (by simp [h0])
  unfold Core
  rw [Finset.mem_biUnion]
  refine ⟨q, Finset.mem_filter.2 ⟨hq, hc⟩, ?_⟩
  unfold coreBox
  rw [mem_boxSet]
  exact S.chi_core q hq _ hchi'

open Classical in
/-- `Z_Y^F`: the eligible live centres whose footprint lies in `Y`. -/
noncomputable def ZYF (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (a : ℕ → ℝ) (ν : ℝ) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (C.cubeIdx).filter fun z =>
    EligC C X₁ 𝒞 z ∧ LiveI H z ∧ ∀ x ∈ footprint H a ν z, x ∈ Y

/-- `S_Y^F = ⋃_{z ∈ Z_Y^F} □_z`. -/
noncomputable def SYF (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (a : ℕ → ℝ) (ν : ℝ) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  (ZYF C H a ν X₁ 𝒞 Y).biUnion intBox

section Comb

variable {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
  {A : Finset (ℕ × CTorus d L N₁ m₁ K)}

/-- The operator sites of `S_Y^F` lie in `Y`. -/
theorem SYF_subset_Y {x : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y) :
    (x : CTorus d L N₁ m₁ K) ∈ Y := by
  classical
  unfold SYF at hx
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  exact (Finset.mem_filter.1 hz).2.2.2 x (mem_footprint_self hxz)

/-- A centre with a non-zero factor is eligible. -/
theorem eligC_of_active {u : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hu : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ C.cubeIdx) (h : C.sProd u z ≠ 0) : EligC C X₁ 𝒞 z := by
  refine ⟨hz, fun P hP hPP => ?_⟩
  by_contra hPC
  exact (sProd_ne_zero_iff u z |>.1 h) P hP (hu P hPP hPC)

/-- **The dichotomy for the interaction cubes**: an active interaction cube lies inside `S_Y^F` or
meets no operator site of it. -/
theorem fp_dichT (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ C.cubeIdx)
    (hact : C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) :
    SubI H (intBox z) (SYF C H a ν X₁ 𝒞 Y) ∨ DisjI H (intBox z) (SYF C H a ν X₁ 𝒞 Y) := by
  classical
  have hE : EligC C X₁ 𝒞 z := by
    rcases hact with h | h
    · exact eligC_of_active (fun P hP hPC => (hs0 P hP hPC).1) hz h
    · exact eligC_of_active (fun P hP hPC => (hs0 P hP hPC).2) hz h
  by_cases hL : LiveI H z
  · rcases hY.dichotomy hE hL with ⟨hfp, -⟩ | hd
    · left
      intro x hx
      exact Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, hE, hL, hfp⟩, hx⟩
    · right
      intro x hx hxS
      exact hd _ (mem_footprint_self hx) (SYF_subset_Y hxS)
  · left
    intro x hx
    exact absurd ⟨x, hx⟩ hL

/-- **Agreement of the factors at live centres inside `S_Y^F`.** -/
theorem fp_agreeT (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → s P = s' P)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ C.cubeIdx) (hL : LiveI H z)
    (hsub : SubI H (intBox z) (SYF C H a ν X₁ 𝒞 Y)) : C.sProd s z = C.sProd s' z := by
  classical
  by_cases hactive : C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0
  · have hE : EligC C X₁ 𝒞 z := by
      rcases hactive with h | h
      · exact eligC_of_active (fun P hP hPC => (hs0 P hP hPC).1) hz h
      · exact eligC_of_active (fun P hP hPC => (hs0 P hP hPC).2) hz h
    obtain ⟨b, hb⟩ := hL
    rcases hY.dichotomy hE ⟨b, hb⟩ with ⟨-, hQA⟩ | hd
    · unfold DecCover.sProd
      refine Finset.prod_congr rfl fun P hPQ => ?_
      by_cases hPP : P ∈ C.parCubes X₁
      · by_cases hPC : P ∈ 𝒞
        · exact hag P hPC (hQA P hPQ hPC)
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P (C.mem_Qset.1 hPQ).1 hPP).1, (hs1 P (C.mem_Qset.1 hPQ).1 hPP).2]
    · exact absurd (SYF_subset_Y (hsub b hb)) (hd _ (mem_footprint_self hb))
  · push Not at hactive
    rw [hactive.1, hactive.2]

/-- **Vanishing outside `S_Y^F`**: an active centre whose core contains a site of `Y` is in
`Z_Y^F`. -/
theorem fp_vanish (hY : IsIncUnion C H a ν X₁ 𝒞 Y A) {u : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hu : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ C.cubeIdx) (h : C.sProd u z ≠ 0) {x : H.Ω 1}
    (hxb : (x : CTorus d L N₁ m₁ K) ∈ intBox z) (hxY : (x : CTorus d L N₁ m₁ K) ∈ Y) :
    (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y := by
  classical
  have hE := eligC_of_active hu hz h
  rcases hY.dichotomy hE ⟨x, hxb⟩ with ⟨hfp, -⟩ | hd
  · exact Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, hE, ⟨x, hxb⟩, hfp⟩, hxb⟩
  · exact absurd hxY (hd _ (mem_footprint_self hxb))

end Comb

section Dg5

variable {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
  {A : Finset (ℕ × CTorus d L N₁ m₁ K)}

/-- **(DG5'), the version with data agreeing on `S_Y^F` only, footprint form.**  Let `(Y, A)` be a
union of components of the incidence graph, `S_Y^F = ⋃_{z ∈ Z_Y^F} □_z`.  If `α = α'` and `f = f'`
on `S_Y^F`, the parameters equal `1` off `𝔓`, vanish on `𝔓 ∖ 𝒞` and agree on `𝒞 ∩ A`, then
`G_s(α) f = G_{s'}(α') f'` on all of `Y ∩ Ω₁`. -/
theorem dg5'_inner_fp (S : FootLocal C H a ν Kc Cx)
    (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → s P = s' P)
    (hA : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → α x = α' x)
    {f f' : H.Ω 1 → ℂ}
    (hf : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → f x = f' x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (Gs C H a ν α s *ᵥ f) x = (Gs C H a ν α' s' *ᵥ f') x := by
  classical
  intro x hxY
  by_cases hxT : (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y
  · exact Gs_local_fp S.toCoverBase hα hα' hU hU'
      (fun z hz hact => fp_dichT hY hs0 hz hact)
      (fun z hz hL hsub => fp_agreeT hY hs1 hs0 hag hz hL hsub) hA hf x hxT
  · have hz0 : ∀ {u : ℕ × CTorus d L N₁ m₁ K → ℂ} {β : H.Ω 1 → ℂ} {g : H.Ω 1 → ℂ},
        (∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) →
        (Gs C H a ν β u *ᵥ g) x = 0 := by
      intro u β g hu
      by_contra hne
      have hc := dg5_support_fp S.toFootLocalGeom u g x hne
      unfold Core at hc
      obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hc
      have hzZ' := Finset.mem_filter.1 hzZ
      exact hxT (fp_vanish hY hu hzZ'.1 hzZ'.2 (coreBox_subset_box hxz) hxY)
    rw [hz0 (fun P hP hPC => (hs0 P hP hPC).1), hz0 (fun P hP hPC => (hs0 P hP hPC).2)]

/-- **(DG5'), footprint form, data agreeing on `Y`.**  The conclusion holds on all of
`Y ∩ Ω₁`; in particular on the cores of the centres of `Z_Y^F`. -/
theorem dg5'_fp (S : FootLocal C H a ν Kc Cx)
    (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → s P = s' P)
    (hA : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → α x = α' x)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → f x = f' x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (Gs C H a ν α s *ᵥ f) x = (Gs C H a ν α' s' *ᵥ f') x :=
  dg5'_inner_fp S hY hα hα' hU hU' hs1 hs0 hag (fun x hx => hA x (SYF_subset_Y hx))
    (fun x hx => hf x (SYF_subset_Y hx))

end Dg5

end Balaban.Localization.Dec2
