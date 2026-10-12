/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpLocal
public import Balaban.Localization.Decoupled2XLocal

/-!
# Footprint locality of the x-variant decoupled Green's operator (VMOD-4)

`Gsx_local_fp`, `dg5x_support_fp`, `dg5x'_inner_fp` and `dg5x'_fp`: the x-variants of the footprint
locality of `Decoupled2FpLocal.lean`; the combinatorics of the incidence graph is the same
(`fp_dichT`, `fp_agreeT`, `fp_vanish`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Setting

variable (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (a : ℕ → ℝ) (aT ν Cx : ℝ)

/-- `XCover` together with the geometry of the cover used by the footprint locality. -/
structure XFootLocal : Prop extends XCover C H a aT ν Cx, FootLocalGeom C

end Setting

/-- **Inhabitation of `XFootLocal`** at the pair `(coverOf G, G)` of the landed setting. -/
theorem xFootLocal_nonempty {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ}
    {aT ν : ℝ} (S : XSetting G a aT ν) :
    Nonempty (XFootLocal (coverOf G) G a aT ν (Cchi d L)) :=
  ⟨{ toXCover := xCover_self S
     chi_core := (footLocalGeom_coverOf G).chi_core }⟩

variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- A centre without operator sites has `cubeGx = 0`. -/
theorem cubeGx_dead {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : ¬ LiveI H z) (α : H.Ω 1 → ℂ) :
    cubeGx H a aT x ν α z = 0 := by
  unfold cubeGx
  rw [cD_dead hz, Matrix.mul_zero]

/-- **Locality of `G_s(A) f`, live centres only** (x-variant of `Gs_local_fp`). -/
theorem Gsx_local_fp (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C H a aT x ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, (C.sProd s q ≠ 0 ∨ C.sProd s' q ≠ 0) →
      SubI H (intBox q) Y ∨ DisjI H (intBox q) Y)
    (hagree : ∀ q ∈ C.cubeIdx, LiveI H q → SubI H (intBox q) Y → C.sProd s q = C.sProd s' q)
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
    by_cases hl : LiveI H q
    · rw [hagree q hq'.1 hl hq'.2, cubeGx_congr S hx hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
    · rw [cubeGx_dead hl α, cubeGx_dead hl α']
      simp
  have hinnerX : ∑ q ∈ innerCentres C H Y, C.sProd s q • (chiD C H q * cubeGx H a aT x ν α q) =
      ∑ q ∈ innerCentres C H Y, C.sProd s' q • (chiD C H q * cubeGx H a aT x ν α' q) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    by_cases hl : LiveI H q
    · rw [hagree q hq'.1 hl hq'.2, cubeGx_congr S hx hα hα' hq'.1 (fun z hz => hA z (hq'.2 z hz))]
    · rw [cubeGx_dead hl α, cubeGx_dead hl α']
      simp
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
theorem dg5x_support_fp (S : FootLocalGeom C) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (f : H.Ω 1 → ℂ) (y : H.Ω 1)
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
  exact S.chi_core q hq _ hchi'

section Dg5x

variable {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
  {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {A : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}

/-- **(DG5'), x-variant, data agreeing on `S_Y^F` only, footprint form.** -/
theorem dg5x'_inner_fp (S : XFootLocal C H a aT ν Cx) (hx : 0 ≤ x)
    (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C H a aT x ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → s P = s' P)
    (hA : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SYF C H a ν X₁ 𝒞 Y → α y = α' y)
    {f f' : H.Ω 1 → ℂ}
    (hf : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SYF C H a ν X₁ 𝒞 Y → f y = f' y) :
    ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      (Gsx C H a aT x ν α s *ᵥ f) y = (Gsx C H a aT x ν α' s' *ᵥ f') y := by
  classical
  intro y hyY
  by_cases hyT : (y : CTorus d L N₁ m₁ (k + 1)) ∈ SYF C H a ν X₁ 𝒞 Y
  · exact Gsx_local_fp S.toXCover hx hα hα' hU hU'
      (fun z hz hact => fp_dichT hY hs0 hz hact)
      (fun z hz hL hsub => fp_agreeT hY hs1 hs0 hag hz hL hsub) hA hf y hyT
  · have hz0 : ∀ {u : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {β : H.Ω 1 → ℂ} {g : H.Ω 1 → ℂ},
        (∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) →
        (Gsx C H a aT x ν β u *ᵥ g) y = 0 := by
      intro u β g hu
      by_contra hne
      have hc := dg5x_support_fp S.toFootLocalGeom u g y hne
      unfold Core at hc
      obtain ⟨z, hzZ, hyz⟩ := Finset.mem_biUnion.1 hc
      have hzZ' := Finset.mem_filter.1 hzZ
      exact hyT (fp_vanish hY hu hzZ'.1 hzZ'.2 (coreBox_subset_box hyz) hyY)
    rw [hz0 (fun P hP hPC => (hs0 P hP hPC).1), hz0 (fun P hP hPC => (hs0 P hP hPC).2)]

/-- **(DG5'), x-variant, data agreeing on `Y`, footprint form.** -/
theorem dg5x'_fp (S : XFootLocal C H a aT ν Cx) (hx : 0 ≤ x)
    (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C H a aT x ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → s P = s' P)
    (hA : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → α y = α' y)
    {f f' : H.Ω 1 → ℂ}
    (hf : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → f y = f' y) :
    ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      (Gsx C H a aT x ν α s *ᵥ f) y = (Gsx C H a aT x ν α' s' *ᵥ f') y :=
  dg5x'_inner_fp S hx hY hα hα' hU hU' hs1 hs0 hag (fun y hy => hA y (SYF_subset_Y hy))
    (fun y hy => hf y (SYF_subset_Y hy))

end Dg5x

end Balaban.Localization.Dec2
