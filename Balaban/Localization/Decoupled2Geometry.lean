/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Local
public import Balaban.Localization.DecoupledGeometry

/-!
# (DG5), (DG5'): locality in terms of the parameters, for a cover `C` and an operator `H`

`CoverLocal C H a ν Kc Cx` adds to `CoverBase` the facts about the pair that the geometry of the
parameter cubes needs: the centres are cube bases, `supp χ_z ⊂ C_z`, the `π¹`-cubes of the centres
lie in `Ω₁(H)` and cover `Ω₁(H)`.
-/

@[expose] public section

namespace Balaban.Localization

open Classical in
/-- The parameter cubes `𝔓` of the cover `C`: the cubes of the cover that are not contained in
`X₁`. -/
noncomputable def DecCover.parCubes {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]
    (C : DecCover d L N₁ m₁ K) (X₁ : Finset (CTorus d L N₁ m₁ K)) :
    Finset (ℕ × CTorus d L N₁ m₁ K) :=
  C.cubeIdx.filter fun q => ¬ cubeP q ⊆ X₁

end Balaban.Localization

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

section Pair

variable (C H a ν Kc Cx)

/-- **The geometry of the cover used by the locality of the parameters** (extends `CoverGeom`):
the centres are cube bases of layers `1 ≤ j ≤ K`, `supp χ_z ⊂ C_z`, and the `π¹`-cubes of the
centres lie in `Ω₁(H)` and cover `Ω₁(H)`. -/
structure CoverLocalGeom : Prop extends CoverGeom C H a ν Cx where
  idx_range : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ K
  idx_base : ∀ q ∈ C.cubeIdx, CubeBase m₁ q.1 q.2
  chi_supp : ∀ q ∈ C.cubeIdx, ∀ x, C.chi q x ≠ 0 →
    InBox m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁)) x
  cubeP_sub : ∀ q ∈ C.cubeIdx, ∀ x ∈ cubeP q, x ∈ H.Ω 1
  own_cover : ∀ x ∈ H.Ω 1, ∃ P ∈ C.cubeIdx, x ∈ cubeP P

/-- **The properties of the pair used by the locality of the parameters** (extends `CoverBase` and
`CoverLocalGeom`): in addition, the rows of the operator `H_D(α)` at the points of `□_z` lie in
the thickened cube `□̂_z` (the operator footprint of a cover cube). -/
structure CoverLocal : Prop extends CoverBase C H a ν Kc Cx, CoverLocalGeom C H a ν Cx where
  row_mem_hat : ∀ z ∈ C.cubeIdx, ∀ (α : H.Ω 1 → ℂ) {x : H.Ω 1}, (x : CTorus d L N₁ m₁ K) ∈ intBox z →
    ∀ {y : H.Ω 1}, dirichletOperator H a ν α x y ≠ 0 → (y : CTorus d L N₁ m₁ K) ∈ hatBox z

end Pair

theorem cubeP_eq_boxSet' (S : CoverLocalGeom C H a ν Cx) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) :
    cubeP q = boxSet m₁ q.1 q.2 (1 / 2 * (L : ℝ) ^ (q.1 + m₁)) := by
  obtain ⟨hm1, hmK⟩ := S.idx_range q hq
  have hb := S.idx_base q hq
  ext x
  rw [mem_cubeP, mem_boxSet, inBox_half_iff_sameCell hmK hb]

theorem cubeP_subset_Ω' (S : CoverLocalGeom C H a ν Cx) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) {x : CTorus d L N₁ m₁ K} (hx : x ∈ cubeP q) : x ∈ H.Ω 1 :=
  S.cubeP_sub q hq x hx

theorem cubeP_connIn' (S : CoverLocalGeom C H a ν Cx) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) : ConnIn (cubeP q) := by
  obtain ⟨hm1, hmK⟩ := S.idx_range q hq
  rw [cubeP_eq_boxSet' S hq]
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hB : (2 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by
    calc (2 : ℝ) ≤ L := by linarith
      _ = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ (q.1 + m₁) := pow_le_pow_right₀ (by linarith) (by omega)
  exact boxSet_connected q.2 (by linarith)

/-- The thickened interaction cubes are nearest-neighbour connected inside `Ω₁` (automatic if
`□̂_z ⊂ Ω₁`; a regularity condition on the generating set at layer 1). -/
def HatConn (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) : Prop :=
  ∀ q ∈ C.cubeIdx, ConnIn (hatI H q)

open Classical in
/-- `Z_ℛ = {z : 𝒬(z) ∩ ℛ = ∅}`, `ℛ = {P : s_P = 0}` (`sProd_ne_zero_iff`). -/
noncomputable def Zs (C : DecCover d L N₁ m₁ K)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (C.cubeIdx).filter fun z => C.sProd s z ≠ 0

open Classical in
/-- `Y(ℛ) ∩ Ω₁`, `Y(ℛ) = ⋃_{z ∈ Z_ℛ} □̂_z`. -/
noncomputable def Yreg (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Finset (CTorus d L N₁ m₁ K) :=
  ((Zs C s).biUnion hatBox).filter fun x => x ∈ H.Ω 1

/-- `Core(ℛ) = ⋃_{z ∈ Z_ℛ} C_z`. -/
noncomputable def Core (C : DecCover d L N₁ m₁ K)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Finset (CTorus d L N₁ m₁ K) :=
  (Zs C s).biUnion coreBox

theorem sProd_ne_zero_iff (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (z : ℕ × CTorus d L N₁ m₁ K) :
    C.sProd s z ≠ 0 ↔ ∀ P ∈ C.Qset z, s P ≠ 0 := by
  unfold DecCover.sProd
  rw [Finset.prod_ne_zero_iff]

/-- **(DG5), support.** `G_s(A) f` vanishes outside `Core(ℛ)`. -/
theorem dg5_support (S : CoverLocalGeom C H a ν Cx) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (f : H.Ω 1 → ℂ) (x : H.Ω 1)
    (hx : (Gs C H a ν α s *ᵥ f) x ≠ 0) : (x : CTorus d L N₁ m₁ K) ∈ Core C s := by
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
  exact S.chi_supp q hq _ hchi'

/-- **(DG5), locality on a nearest-neighbour component.** -/
theorem dg5_local (S : CoverBase C H a ν Kc Cx) (hconn : HatConn C H) {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α)
    (hα' : AdmPot H α') {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s))
    {Y' : Finset (CTorus d L N₁ m₁ K)} (hY : IsNnComp (Yreg C H s) Y')
    (hA : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → α x = α' x)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' → f x = f' x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y' →
      (Gs C H a ν α s *ᵥ f) x = (Gs C H a ν α' s *ᵥ f') x := by
  classical
  refine Gs_local S hα hα' hU hU' ?_ (fun _ _ _ => rfl) hA hf
  intro z hz hact
  have hzs : C.sProd s z ≠ 0 := by rcases hact with h | h <;> exact h
  have hzZ : z ∈ Zs C s := Finset.mem_filter.2 ⟨hz, hzs⟩
  have hsub : hatI H z ⊆ Yreg C H s := by
    intro x hx
    unfold hatI at hx
    rw [Finset.mem_filter] at hx
    unfold Yreg
    rw [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨⟨z, hzZ, hx.1⟩, hx.2⟩
  rcases connIn_dichotomy (hconn z hz) hsub hY with h | h
  · left
    intro x hx
    exact h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox z hx, x.2⟩)
  · right
    intro x hx hxY
    exact Finset.disjoint_left.1 h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox z hx, x.2⟩) hxY

/-! ### (DG5') -/


open Classical in
/-- `Z_Y = {z : 𝒬(z) ∩ 𝔓 ⊂ 𝒞, □̂_z ⊂ Y}`. -/
noncomputable def ZY (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (C.cubeIdx).filter fun z =>
    (∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞) ∧ SubI H (hatBox z) Y

/-- **(DG5'), termwise comparison.**  Let `𝒞 ⊂ cubeIdx`, `Y` a union of nearest-neighbour
components of `V(𝒞) ∩ Ω₁`; `s, s'` equal to `1` off `𝔓` and `0` on `𝔓 ∖ 𝒞`, agreeing on the cubes of
`𝒞` inside `Y`; `A = A'`, `f = f'` on `Y`.  Then `G_s(A) f = G_{s'}(A') f'` on
`Core_Y = ⋃_{z ∈ Z_Y} C_z`. -/
theorem dg5' (S : CoverLocal C H a ν Kc Cx) (hconn : HatConn C H) {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → s P = s' P)
    (hA : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → α x = α' x)
    {f f' : H.Ω 1 → ℂ} (hf : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → f x = f' x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ (ZY C H X₁ 𝒞 Y).biUnion coreBox →
      (Gs C H a ν α s *ᵥ f) x = (Gs C H a ν α' s' *ᵥ f') x := by
  classical
  -- active centres only see parameter cubes of `𝒞`
  have hact : ∀ (u : ℕ × CTorus d L N₁ m₁ K → ℂ), (∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) →
      ∀ z, C.sProd u z ≠ 0 → ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
    intro u hu z hz P hP hPP
    by_contra hPC
    exact (sProd_ne_zero_iff u z |>.1 hz) P hP (hu P hPP hPC)
  -- the thickened cube of an active centre lies in `V(𝒞) ∩ Ω₁`
  have hhat : ∀ z ∈ C.cubeIdx, (∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞) →
      hatI H z ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1 := by
    intro z hz hP x hx
    unfold hatI at hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxh, hxΩ⟩ := hx
    obtain ⟨P, hown, hxP⟩ := S.own_cover x hxΩ
    have hQ : P ∈ C.Qset z := C.mem_Qset.2 ⟨hown, x, mem_cubeP.1 hxP, mem_boxSet.1 hxh⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hxΩ⟩
    unfold Vset
    rw [Finset.mem_union]
    by_cases hPP : P ∈ C.parCubes X₁
    · right
      rw [Finset.mem_biUnion]
      exact ⟨_, hP _ hQ hPP, hxP⟩
    · left
      have : cubeP P ⊆ X₁ := by
        by_contra hc
        exact hPP (Finset.mem_filter.2 ⟨hown, hc⟩)
      exact this hxP
  have hdich : ∀ z ∈ C.cubeIdx, (C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) →
      SubI H (intBox z) Y ∨ DisjI H (intBox z) Y := by
    intro z hz hactive
    have hP : ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
      rcases hactive with h | h
      · exact hact s (fun P hP hPC => (hs0 P hP hPC).1) z h
      · exact hact s' (fun P hP hPC => (hs0 P hP hPC).2) z h
    rcases connIn_dichotomy (hconn z hz) (hhat z hz hP) hY with h | h
    · left
      intro x hx
      exact h (by
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨box_subset_hatBox z hx, x.2⟩)
    · right
      intro x hx hxY
      exact Finset.disjoint_left.1 h (by
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨box_subset_hatBox z hx, x.2⟩) hxY
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
          have hsubV : cubeP P ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1 := by
            intro x hx
            rw [Finset.mem_filter]
            refine ⟨?_, cubeP_subset_Ω' S.toCoverLocalGeom hPi hx⟩
            unfold Vset
            rw [Finset.mem_union]
            right
            exact Finset.mem_biUnion.2 ⟨P, hPC, hx⟩
          have hsubY : SubI H (cubeP P) Y := by
            rcases connIn_dichotomy (cubeP_connIn' S.toCoverLocalGeom hPi) hsubV hY with h | h
            · intro x hx; exact h hx
            · exfalso; exact Finset.disjoint_left.1 h hyP hyY
          exact hag P hPC hsubY
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P (C.mem_Qset.1 hPQ).1 hPP).1, (hs1 P (C.mem_Qset.1 hPQ).1 hPP).2]
    · push Not at hactive
      rw [hactive.1, hactive.2]
  intro x hx
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hx
  have hzZ' := Finset.mem_filter.1 hzZ
  have hsub := hzZ'.2.2
  have hxbox : (x : CTorus d L N₁ m₁ K) ∈ hatBox z := by
    refine box_subset_hatBox z (coreBox_subset_box hxz)
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := hsub x hxbox
  exact Gs_local S.toCoverBase hα hα' hU hU' hdich hagree hA hf x hxY

end Balaban.Localization.Dec2
