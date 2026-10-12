/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctStep
public import Balaban.Localization.Decoupled2Local
public import Balaban.Localization.Decoupled2FieldLocal
import Mathlib.Tactic.Linarith

/-!
# The geometry of the fluctuation pair `(C, H⁻)` against the background `H⁺`

The locality of the background field (Theorem I-4b (iv)) is formulated on nearest-neighbour
components `Y` of `V(𝒞) ∩ Ω₁(H⁺)`; the locality of the fluctuation (Theorem I-4a (e), footprint
form) on unions of components `(Y, A)` of the parameter-incidence graph of `(C, H⁻)`.  This file
shows that the former are the latter, for a pair with `Ω₁(H⁻) ⊆ Ω₁(H⁺)` and the rows of `H⁻_D(α)`
at the sites of `□_z` inside `□̂_z` (`incUnion_of_nnComp`), and that the footprint sites `S_Y^F` of
`H⁻` lie in the sites `S_Y` of `H⁺` (`SYF_subset_SY`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Geom

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {C : DecCover d L N₁ m₁ K} {Hp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a : ℕ → ℝ} {ν Kc Cx : ℝ}

variable (C Hm a ν) in
/-- **The rows of the operator `H⁻_D(α)` at the sites of the interaction cube `□_z` stay in the
thickened cube `□̂_z`** (the operator footprint of a cover cube, for the pair `(C, H⁻)`). -/
def RowInHat : Prop :=
  ∀ z ∈ C.cubeIdx, ∀ (α : Hm.Ω 1 → ℂ) {x : Hm.Ω 1}, (x : CTorus d L N₁ m₁ K) ∈ intBox z →
    ∀ {y : Hm.Ω 1}, dirichletOperator Hm a ν α x y ≠ 0 → (y : CTorus d L N₁ m₁ K) ∈ hatBox z

theorem footprint_sub_hat (hrow : RowInHat C Hm a ν) {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ C.cubeIdx) {x : CTorus d L N₁ m₁ K} (hx : x ∈ Dec2.footprint Hm a ν z) :
    x ∈ hatBox z ∧ x ∈ Hm.Ω 1 := by
  obtain ⟨b, hb, hxb | ⟨y, hy, hxy⟩⟩ := hx
  · subst hxb; exact ⟨box_subset_hatBox z hb, b.2⟩
  · subst hxy; exact ⟨hrow z hz 0 hb hy, y.2⟩

end Geom

section Inc

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {C : DecCover d L N₁ m₁ K} {Hp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **A nearest-neighbour component of `V(𝒞) ∩ Ω₁(H⁺)` is a union of components of the
parameter-incidence graph of `(C, H⁻)`**, with the parameter set `A` of the cubes attached to the
centres inside it; the cubes of `A` lie in `Y`. -/
theorem incUnion_of_nnComp (SL : Dec2.CoverLocal C Hp a ν Kc Cx) (hconn : Dec2.HatConn C Hp)
    (hsub : ∀ x, x ∈ Hm.Ω 1 → x ∈ Hp.Ω 1) (hrow : RowInHat C Hm a ν)
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ C.cubeIdx)
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Hp.Ω 1) Y) :
    ∃ A, Dec2.IsIncUnion C Hm a ν X₁ 𝒞 Y A ∧ ∀ P ∈ A, P ∈ 𝒞 ∧ ∀ x ∈ cubeP P, x ∈ Y := by
  classical
  set Ucen : Set (ℕ × CTorus d L N₁ m₁ K) := {z | Dec2.EligC C X₁ 𝒞 z ∧ Dec2.LiveI Hm z ∧
    ∃ x ∈ Dec2.footprint Hm a ν z, x ∈ Y} with hUcen
  set Upar : Set (ℕ × CTorus d L N₁ m₁ K) := {P | ∃ z ∈ Ucen, P ∈ C.Qset z ∧ P ∈ 𝒞} with hUpar
  -- eligible centres: the thickened cube is inside or outside `Y`
  have F2 : ∀ z, Dec2.EligC C X₁ 𝒞 z → SubI Hp (hatBox z) Y ∨ DisjI Hp (hatBox z) Y :=
    fun z hz => Dec2.hdich_aux SL hconn hY z hz.1 hz.2
  have F3 : ∀ z, Dec2.EligC C X₁ 𝒞 z → ∀ x ∈ Dec2.footprint Hm a ν z, x ∈ Y →
      SubI Hp (hatBox z) Y := by
    intro z hz x hx hxY
    rcases F2 z hz with h | h
    · exact h
    · exfalso
      obtain ⟨h1, h2⟩ := footprint_sub_hat hrow hz.1 hx
      exact h ⟨x, hsub x h2⟩ h1 hxY
  have F4 : ∀ z ∈ Ucen, ∀ x ∈ Dec2.footprint Hm a ν z, x ∈ Y := by
    rintro z ⟨hz, -, x0, hx0, hx0Y⟩ x hx
    obtain ⟨h1, h2⟩ := footprint_sub_hat hrow hz.1 hx
    exact F3 z hz x0 hx0 hx0Y ⟨x, hsub x h2⟩ h1
  have F5 : ∀ z ∈ Ucen, ∀ P ∈ C.Qset z, P ∈ 𝒞 → ∀ x ∈ cubeP P, x ∈ Y := by
    intro z hzU P hP hP𝒞
    obtain ⟨hz, -, x0, hx0, hx0Y⟩ := hzU
    have hq : P ∈ C.cubeIdx := h𝒞 P hP𝒞
    obtain ⟨y, hyc, hyb⟩ := (C.mem_Qset).1 hP |>.2
    have hycube : y ∈ cubeP P := mem_cubeP.2 hyc
    have hyHp : y ∈ Hp.Ω 1 := SL.cubeP_sub P hq y hycube
    have hyhat : y ∈ hatBox z := by
      unfold hatBox; exact mem_boxSet.2 hyb
    have hyY : y ∈ Y := F3 z hz x0 hx0 hx0Y ⟨y, hyHp⟩ hyhat
    have hcs : cubeP P ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ Hp.Ω 1 := by
      intro x hx
      rw [Finset.mem_filter]
      refine ⟨?_, SL.cubeP_sub P hq x hx⟩
      unfold Vset
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨P, hP𝒞, hx⟩)
    rcases connIn_dichotomy (Dec2.cubeP_connIn' SL.toCoverLocalGeom hq) hcs hY with h | h
    · exact fun x hx => h hx
    · exact absurd hyY (Finset.disjoint_left.1 h hycube)
  have F6 : ∀ z', Dec2.EligC C X₁ 𝒞 z' → Dec2.LiveI Hm z' → ∀ P ∈ C.Qset z', P ∈ 𝒞 →
      (∀ x ∈ cubeP P, x ∈ Y) → z' ∈ Ucen := by
    intro z' hz' hlive P hP hP𝒞 hcube
    obtain ⟨b, hb⟩ := hlive
    obtain ⟨y, hyc, hyb⟩ := (C.mem_Qset).1 hP |>.2
    have hq : P ∈ C.cubeIdx := h𝒞 P hP𝒞
    have hycube : y ∈ cubeP P := mem_cubeP.2 hyc
    have hyHp : y ∈ Hp.Ω 1 := SL.cubeP_sub P hq y hycube
    have hyhat : y ∈ hatBox z' := by
      unfold hatBox; exact mem_boxSet.2 hyb
    have hbY : (b : CTorus d L N₁ m₁ K) ∈ Y := by
      rcases F2 z' hz' with h | h
      · exact h ⟨b, hsub b b.2⟩ (box_subset_hatBox z' hb)
      · exact absurd (hcube y hycube) (h ⟨y, hyHp⟩ hyhat)
    exact ⟨hz', ⟨b, hb⟩, b, Dec2.mem_footprint_self hb, hbY⟩
  refine ⟨𝒞.filter (· ∈ Upar), ⟨{v | match v with
      | .inl x => x ∈ Y
      | .inr (.inl z) => z ∈ Ucen
      | .inr (.inr P) => P ∈ Upar}, ?_, fun x => Iff.rfl, fun P => ?_⟩, fun P hP => ?_⟩
  · -- closure under adjacency
    have Fsite : ∀ y ∈ Dec2.incSites C Hm a ν X₁ 𝒞,
        y ∈ (Vset X₁ 𝒞).filter fun x => x ∈ Hp.Ω 1 := by
      rintro y ⟨hyΩ, hyX | ⟨z, hzE, hzL, hyf⟩⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_union_left _ hyX, hsub y hyΩ⟩
      · obtain ⟨h1, h2⟩ := footprint_sub_hat hrow hzE.1 hyf
        have := Dec2.hhat_aux SL (X₁ := X₁) (𝒞 := 𝒞) z hzE.2
        refine this ?_
        unfold hatI
        rw [Finset.mem_filter]
        exact ⟨h1, hsub y h2⟩
    have g1 : ∀ x y, x ∈ Y → (x ∈ Dec2.incSites C Hm a ν X₁ 𝒞 ∧ y ∈ Dec2.incSites C Hm a ν X₁ 𝒞 ∧
        Adj x y) → y ∈ Y := fun x y hx h => hY.2 x hx y (Fsite y h.2.1) h.2.2
    have g1' : ∀ x y, x ∈ Y → (y ∈ Dec2.incSites C Hm a ν X₁ 𝒞 ∧ x ∈ Dec2.incSites C Hm a ν X₁ 𝒞 ∧
        Adj y x) → y ∈ Y := fun x y hx h => hY.2 x hx y (Fsite y h.1) h.2.2.symm
    have g2 : ∀ x z, x ∈ Y → (Dec2.EligC C X₁ 𝒞 z ∧ Dec2.LiveI Hm z ∧
        x ∈ Dec2.footprint Hm a ν z) → z ∈ Ucen := fun x z hx h => ⟨h.1, h.2.1, x, h.2.2, hx⟩
    have g3 : ∀ z y, z ∈ Ucen → (Dec2.EligC C X₁ 𝒞 z ∧ Dec2.LiveI Hm z ∧
        y ∈ Dec2.footprint Hm a ν z) → y ∈ Y := fun z y hz h => F4 z hz y h.2.2
    have g4 : ∀ z P, z ∈ Ucen → (Dec2.EligC C X₁ 𝒞 z ∧ Dec2.LiveI Hm z ∧ P ∈ C.Qset z ∧ P ∈ 𝒞) →
        P ∈ Upar := fun z P hz h => ⟨z, hz, h.2.2.1, h.2.2.2⟩
    have g5 : ∀ z' P, P ∈ Upar → (Dec2.EligC C X₁ 𝒞 z' ∧ Dec2.LiveI Hm z' ∧ P ∈ C.Qset z' ∧
        P ∈ 𝒞) → z' ∈ Ucen := by
      rintro z' P ⟨z, hz, hPz, hP𝒞⟩ h
      exact F6 z' h.1 h.2.1 P h.2.2.1 h.2.2.2 (F5 z hz P hPz hP𝒞)
    intro u v hadj hu
    obtain ⟨-, h | h⟩ := hadj
    · rcases u with x | z | P <;> rcases v with y | z' | P' <;> simp only [Dec2.incRel] at h <;>
        (first
          | exact g1 _ _ hu h
          | exact g2 _ _ hu h
          | exact g3 _ _ hu h
          | exact g4 _ _ hu h)
    · rcases u with x | z | P <;> rcases v with y | z' | P' <;> simp only [Dec2.incRel] at h <;>
        (first
          | exact g1' _ _ hu h
          | exact g2 _ _ hu h
          | exact g3 _ _ hu h
          | exact g4 _ _ hu h
          | exact g5 _ _ hu h)
  · simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      obtain ⟨z, -, -, hP𝒞⟩ := id h
      exact ⟨hP𝒞, h⟩
  · rw [Finset.mem_filter] at hP
    obtain ⟨z, hz, hPz, hP𝒞⟩ := hP.2
    exact ⟨hP.1, F5 z hz P hPz hP𝒞⟩

/-- **The sites `S_Y^F` of `H⁻` lie in the sites `S_Y` of `H⁺`**, for a nearest-neighbour
component `Y` of `V(𝒞) ∩ Ω₁(H⁺)`: an eligible centre with an operator site of `H⁻` and footprint in
`Y` has its whole thickened cube (in `Ω₁(H⁺)`) in `Y`. -/
theorem SYF_subset_SY (SL : Dec2.CoverLocal C Hp a ν Kc Cx) (hconn : Dec2.HatConn C Hp)
    (hsub : ∀ x, x ∈ Hm.Ω 1 → x ∈ Hp.Ω 1) {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Hp.Ω 1) Y) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ Dec2.SYF C Hm a ν X₁ 𝒞 Y) : x ∈ Dec2.SY C Hp X₁ 𝒞 Y := by
  classical
  unfold Dec2.SYF at hx
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨hzc, hE, ⟨b, hb⟩, hfp⟩ := Finset.mem_filter.1 hz
  unfold Dec2.SY
  refine Finset.mem_biUnion.2 ⟨z, ?_, hxz⟩
  refine Finset.mem_filter.2 ⟨hzc, hE.2, ?_⟩
  rcases Dec2.hdich_aux SL hconn hY z hzc hE.2 with h | h
  · exact h
  · exact absurd (hfp _ (Dec2.mem_footprint_self hb)) (h ⟨b, hsub b b.2⟩ (box_subset_hatBox z hb))

end Inc

end Balaban.Localization
