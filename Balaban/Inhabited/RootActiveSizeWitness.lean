/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Localization.TreeLengthPaperExample
import Mathlib.Tactic.Linarith

/-!
# Non-vacuity of the active-size dichotomy: a circle of four sites

On the circle of four sites of `Localization.PaperExample` (`d = 1`, `L = 2`, `N₁ = 4`,
`m₀ = m₁ = K = 0`; the level-`0` cubes are the four sites) we exhibit

* the non-empty set `T = {0, 1}` of cubes, not the set of all cubes, with
  `dOmega ≠ ⊤`, `IsPolyDom`, and `dExt T = sizeJ (sitesOf T) = 0` (both sides of (R1));
* the set `{0, 2}`, whose sites are not connected, with `dOmega = ⊤`, so that `dExt` is `Mbig`
  and every `interpCoeff` vanishes there.

The landed `Thm31Witness` marks use one whole-torus label, so their interpolation coefficient can be
non-zero only at the set of all cubes (`exists_blocksOf_subset_of_interpCoeff_ne_zero`); they are
not instantiated here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Localization.PaperExample Balaban.SmallField.Def6

namespace RootActiveSizeWitness

local notation "𝔅" => CubeB (d := 1) (L := 2) (N₁ := 4) (m₁ := 0) (K := 0) 0 0 Set.univ

/-- The cube at site `k`. -/
def cube (k : ℕ) : 𝔅 := ⟨pt k, aligned_one _, Set.subset_univ _⟩

theorem mem_box_one (b x : T) : x ∈ box b (cellSide 2 0 0 0) ↔ x = b := by
  rw [cellSide_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := hw 0
    have h0 : w 0 = 0 := by omega
    funext μ; simp [h0, Subsingleton.elim μ 0]
  · rintro rfl
    exact ⟨fun _ => 0, fun _ => by norm_num, by funext μ; simp⟩

theorem pt_one : pt 1 = pt 0 + e1 := by funext μ; simp [pt, e1]

theorem mem_sitesOf_pair (a c : ℕ) (x : T) :
    x ∈ sitesOf ({cube a, cube c} : Finset 𝔅) ↔ x = pt a ∨ x = pt c := by
  classical
  rw [mem_sitesOf]
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
  simp only [cube, mem_box_one]

/-- The connected pair of cubes `{0, 1}`. -/
def T01 : Finset 𝔅 := {cube 0, cube 1}

/-- The disconnected pair of cubes `{0, 2}`. -/
def T02 : Finset 𝔅 := {cube 0, cube 2}

theorem T01_nonempty : T01.Nonempty := ⟨cube 0, by simp [T01]⟩

theorem T01_mem (x : T) : x ∈ sitesOf T01 ↔ x = pt 0 ∨ x = pt 0 + e1 := by
  rw [T01, mem_sitesOf_pair, pt_one]

theorem chosen_T01 : ChosenOne 0 0 (sitesOf T01) {pt 0} := by
  refine ⟨fun b hb => ⟨aligned_one b, ?_⟩, fun z hz => ?_⟩
  · rw [Set.mem_singleton_iff.1 hb]
    intro x hx
    exact (T01_mem x).2 ((box_mem_iff _ _).1 hx)
  · exact ⟨pt 0, rfl, (box_mem_iff _ _).2 ((T01_mem z).1 hz)⟩

theorem isPolyDom_T01 : IsPolyDom 0 0 (sitesOf T01) := by
  classical
  refine ⟨⟨pt 0, (T01_mem _).2 (Or.inl rfl)⟩, ⟨{pt 0}, chosen_T01⟩, ?_⟩
  intro x hx y hy
  have hv : ∀ z, z ∈ sitesOf T01 → z = pt 0 ∨ z = pt 1 := by
    intro z hz; rw [T01, mem_sitesOf_pair] at hz; exact hz
  have h01 : Relation.ReflTransGen
      (fun u v : T => u ∈ sitesOf T01 ∧ v ∈ sitesOf T01 ∧ Nbr u v) (pt 0) (pt 1) :=
    Relation.ReflTransGen.single ⟨(T01_mem _).2 (Or.inl rfl), (T01_mem _).2 (Or.inr pt_one),
      step_pt 0⟩
  have h10 : Relation.ReflTransGen
      (fun u v : T => u ∈ sitesOf T01 ∧ v ∈ sitesOf T01 ∧ Nbr u v) (pt 1) (pt 0) :=
    Relation.ReflTransGen.single ⟨(T01_mem _).2 (Or.inr pt_one), (T01_mem _).2 (Or.inl rfl),
      (step_pt 0).symm⟩
  rcases hv x hx with rfl | rfl <;> rcases hv y hy with rfl | rfl
  all_goals first | exact Relation.ReflTransGen.refl | exact h01 | exact h10

theorem T01_ne_univ : T01 ≠ Finset.univ := by
  intro h
  have : cube 2 ∈ T01 := h ▸ Finset.mem_univ _
  simp only [T01, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h2 | h2
  · have := congrArg Subtype.val h2
    revert this; decide +kernel
  · have := congrArg Subtype.val h2
    revert this; decide +kernel

theorem sizeJ_T01 : sizeJ 0 0 (sitesOf T01) = 0 := by
  classical
  unfold sizeJ
  refine le_antisymm ?_ (treeLenCovOne_nonneg _ _ _)
  have := treeLenCovOne_le_of_chosen (m₀ := 0) (j := 0) chosen_T01 (connStruct_singleton (pt 0))
    (by intro x hx; simp at hx; subst hx; exact (T01_mem _).2 (Or.inl rfl))
    (by
      rintro b hb
      rw [Set.mem_singleton_iff.1 hb]
      exact ⟨pt 0, by simp, (box_mem_iff _ _).2 (Or.inl rfl)⟩)
  rw [cost_eq] at this
  simpa using this

/-- **Both sides of (R1) at a non-trivial active set**: `{0,1}` is a non-empty proper set of
cubes with finite size, `sitesOf` is a polymer, and `dExt = sizeJ = 0`. -/
theorem active_example :
    T01.Nonempty ∧ T01 ≠ Finset.univ ∧ dOmega 0 0 Set.univ (sitesOf T01) ≠ ⊤ ∧
      IsPolyDom 0 0 (sitesOf T01) ∧ dExt T01 = 0 ∧ sizeJ 0 0 (sitesOf T01) = 0 := by
  have hne := (isPolyDom_iff_dOmega_ne_top.1 isPolyDom_T01).2
  refine ⟨T01_nonempty, T01_ne_univ, hne, isPolyDom_T01, ?_, sizeJ_T01⟩
  rw [(isPolyDom_and_dExt_eq_sizeJ T01_nonempty hne).2, sizeJ_T01]

theorem not_siteConnected_T02 : ¬ SiteConnected (sitesOf T02) := by
  classical
  intro hc
  have hv : ∀ z, z ∈ sitesOf T02 ↔ z = pt 0 ∨ z = pt 2 := by
    intro z; rw [T02, mem_sitesOf_pair]
  have hno : ∀ a b : T, a ∈ sitesOf T02 → b ∈ sitesOf T02 → ¬ Nbr a b := by
    intro a b ha hb hab
    rw [nbr_iff] at hab
    rw [hv] at ha hb
    revert hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +kernel
  have h := hc (pt 0) ((hv _).2 (Or.inl rfl)) (pt 2) ((hv _).2 (Or.inr rfl))
  rw [Relation.reflTransGen_iff_eq] at h
  · revert h; decide +kernel
  · rintro b ⟨ha, hb, hab⟩
    exact hno _ _ ha hb hab

/-- **A set of cubes with `dOmega = ⊤`**: `{0,2}` is disconnected, so `dOmega = ⊤`, `dExt` is
`Mbig`, and it is not a polymer. -/
theorem inactive_example :
    dOmega 0 0 Set.univ (sitesOf T02) = ⊤ ∧ dExt T02 = Mbig 1 2 4 0 0 ∧
      ¬ IsPolyDom 0 0 (sitesOf T02) := by
  have htop : dOmega 0 0 Set.univ (sitesOf T02) = ⊤ := by
    by_contra h
    exact not_siteConnected_T02 (siteConnected_of_dOmega_ne_top h).1
  refine ⟨htop, dExt_eq_Mbig htop, fun hp => ?_⟩
  exact (dOmega_ne_top_of_isPolyDom hp) htop

end RootActiveSizeWitness

end Balaban.Fluctuation
