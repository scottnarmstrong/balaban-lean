/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.StepGlueMain
public import Balaban.LargeField.History.InhabitedRemoval

/-!
# Gluing separated steps without a common witness (A6-4, the history factorization)

The large-field half of the last integral sums over the histories of the representation; for the
gas of P7 (4.11) the histories with region `Z_k` must be the families of local histories of the
components of `Z_k`, glued (`notes/phase1/A64-DESIGN.md` §2). The landed gluing `glue_step` asks,
at every point, for one step of which all members near the point are restrictions (a common
witness): the members of the removed clusters of one history have it, members coming from different
histories do not, and the separation `ω_{k+1} ≥ 2⌊R_k⌋ + L + 11` of the components allows two
members within the locality radius `L + 2⌊R_k⌋ + 6` of one point.

This file proves the gluing without a witness, from the separation of the `Z^pre` of the members
alone and `2L < ω`. The point: every set read by the set functions of a step near a point lies,
with a neighbourhood of the radius at which it is read minus at most `L`, in the `Z^pre` of its
member (the neighbourhood margins below), so two members can never both be read at one point.

* Margins (from Lemma I.3.5, `Region/Inclusions`): `nbhd (⌊R_k⌋+4) U' ⊆ Z^pre`, `nbhd 3 P ⊆ Z^pre`, `nbhd (⌊R_k⌋+2) Q ⊆ Z^pre`,
  `nbhd (2⌊R_k⌋+4) R ⊆ Z^pre`, `nbhd (⌊2R_k⌋+6) Ω''ᶜ ⊆ Z^pre`, `nbhd (⌊2R_k⌋+3) S ⊆ Z^pre`
  (and `Ω'ᶜ, Ωᶜ ⊆ Z^pre`, landed).
* `false_of_sep`: two sets of two members with neighbourhood margins `s, t` in their `Z^pre` are
  at distance `> s + c + t` when `c < ω`.
* The four identities `compl_OmegaPrime_biUnion_of_sep`, `compl_Omega_biUnion_of_sep`,
  `compl_OmegaDD_biUnion_of_sep`, `eq_Z0_biUnion_of_sep`: the derived sets of the union of the data
  are the unions (of the complements) of those of the members.
* `glue_step_of_sep`: the union of the data is a step, with `Z^{(0)}` and `Z^pre` the unions and the
  restriction to the `Z^pre` of a member the member (through the core `glue_step_of_identities` of
  the landed `glue_step`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban


namespace PreStep

variable {d L n0 n1 : ℕ} {Rprev Rk : ℝ}

/-- The data of one member. -/
theorem biUnion_singleton {ι : Type*} (i : ι)
    (p : ι → PreStep d L n0 n1 Rprev Rk) : biUnion {i} p = p i := by
  refine PreStep.ext ?_ ?_ ?_ ?_ ?_ <;> simp [biUnion]

variable [NeZero n1] {ι : Type*} (p : ι → PreStep d L n0 n1 Rprev Rk) (hL : 0 < L)
include hL

omit [NeZero n1] in
theorem biUnion_empty_OmegaPrime : (biUnion ∅ p).OmegaPrime = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  have hU : (biUnion ∅ p).Uprime = ∅ := by
    ext u
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hu
    obtain ⟨i, hi, -⟩ := mem_Uprime_biUnion.mp hu
    simp at hi
  show y ∈ Region.OmegaPrime L ⌊Rk⌋₊ (biUnion ∅ p).Uprime
  rw [hU, Region.OmegaPrime, nbhd_empty, Witness.opening_empty_eq_univ hL]
  trivial

theorem biUnion_empty_Omega : (biUnion ∅ p).Omega = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  show y ∈ Region.Omega L (biUnion ∅ p).P (biUnion ∅ p).OmegaPrime
  rw [biUnion_empty_OmegaPrime p hL]
  have hP : (biUnion ∅ p).P = ∅ := by simp [biUnion]
  rw [hP, Region.Omega, nbhd_empty, Witness.openingIn_empty_univ hL]
  trivial

theorem biUnion_empty_OmegaDD : (biUnion ∅ p).OmegaDD = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  show y ∈ Region.OmegaDD L (Region.FDD ⌊Rk⌋₊ (biUnion ∅ p).Q (biUnion ∅ p).R) (biUnion ∅ p).Omega
  rw [biUnion_empty_Omega p hL]
  have hQ : (biUnion ∅ p).Q = ∅ := by simp [biUnion]
  have hR : (biUnion ∅ p).R = ∅ := by simp [biUnion]
  rw [hQ, hR, Region.OmegaDD, Region.FDD, nbhd_empty, nbhd_empty, Set.union_empty,
    Witness.openingIn_empty_univ hL]
  trivial

theorem biUnion_empty_Z0 : (biUnion ∅ p).Z0 = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  show y ∉ Region.Z0 L ⌊2 * Rk⌋₊ (Region.FZ (biUnion ∅ p).OmegaDD (biUnion ∅ p).S)
  rw [biUnion_empty_OmegaDD p hL]
  have hS : (biUnion ∅ p).S = ∅ := by simp [biUnion]
  rw [hS, Region.Z0, Region.FZ, Set.compl_univ, nbhd_empty, nbhd_empty, Set.union_empty,
    Witness.opening_empty_eq_univ hL]
  simp

end PreStep

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk) (ω : ℕ) (crit : Option ℕ)

/-- The margin of `U'`: `nbhd (⌊R_k⌋+4) U' ⊆ Ω'ᶜ ⊆ Z^pre` (Lemma I.3.5 (a)). -/
theorem nbhd_Uprime_subset_Zpre : nbhd (⌊Rk⌋₊ + 4) st.Uprime ⊆ st.Zpre ω crit :=
  st.nbhd_Uprime_subset.trans (st.OmegaPrime_compl_subset_Zpre ω crit)

/-- The margin of `P`: `nbhd 3 P ⊆ Ωᶜ ⊆ Z^pre`. -/
theorem nbhd_P_subset_Zpre : nbhd 3 st.P ⊆ st.Zpre ω crit :=
  fun _ hy => st.Omega_compl_subset_Zpre ω crit
    (Set.disjoint_right.mp st.Omega_disjoint_nbhd_P hy)

/-- The margins of `Q` and `R`: `F'' ⊆ Ω''ᶜ ⊆ Z^pre`. -/
theorem FDD_subset_Zpre : st.FDD ⊆ st.Zpre ω crit :=
  fun _ hy => st.OmegaDD_compl_subset_Zpre ω crit (Set.disjoint_right.mp st.OmegaDD_disjoint_FDD hy)

theorem nbhd_Q_subset_Zpre : nbhd (⌊Rk⌋₊ + 2) st.Q ⊆ st.Zpre ω crit :=
  fun _ hy => st.FDD_subset_Zpre ω crit (Or.inl hy)

theorem nbhd_R_subset_Zpre : nbhd (2 * ⌊Rk⌋₊ + 4) st.R ⊆ st.Zpre ω crit :=
  fun _ hy => st.FDD_subset_Zpre ω crit (Or.inr hy)

/-- The margin of `Ω''ᶜ`: `nbhd (⌊2R_k⌋+6) Ω''ᶜ ⊆ Z^pre`. -/
theorem nbhd_OmegaDD_compl_subset_Zpre : nbhd (⌊2 * Rk⌋₊ + 6) st.OmegaDDᶜ ⊆ st.Zpre ω crit := by
  intro y hy
  have h1 : y ∈ nbhd (⌊2 * Rk⌋₊ + 2) (nbhd 4 st.OmegaDDᶜ) := by
    rw [nbhd_nbhd]; convert hy using 2; omega
  have h2 : y ∈ nbhd (⌊2 * Rk⌋₊ + 2) st.FZ := nbhd_mono le_rfl (fun _ h => Or.inl h) h1
  exact st.Z0_subset_Zpre ω crit (st.nbhd_FZ_subset_Z0 h2)

/-- The margin of `S`: `nbhd (⌊2R_k⌋+3) S ⊆ Z^pre`. -/
theorem nbhd_S_subset_Zpre : nbhd (⌊2 * Rk⌋₊ + 3) st.S ⊆ st.Zpre ω crit := by
  intro y hy
  have h1 : y ∈ nbhd (⌊2 * Rk⌋₊ + 2) (nbhd 1 st.S) := by
    rw [nbhd_nbhd]; convert hy using 2; omega
  have h2 : y ∈ nbhd (⌊2 * Rk⌋₊ + 2) st.FZ := nbhd_mono le_rfl (fun _ h => Or.inr h) h1
  exact st.Z0_subset_Zpre ω crit (st.nbhd_FZ_subset_Z0 h2)

end RegionStep

section Sep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ} {ι : Type*}
  {ω : ℕ} {crit : Option ℕ} {F : Finset ι} {st : ι → RegionStep d L n0 n1 Rprev Rk}

omit [NeZero n0] in
/-- **Two members are never read at one point**: sets `A`, `B` of two members whose neighbourhoods
of radii `s`, `t` lie in their `Z^pre` are at distance `> s + c + t` for `c < ω`. -/
theorem false_of_sep (hsep : SepFam ω F (fun i => (st i).Zpre ω crit)) {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) {A B : Set (Torus d n1)} {s t c : ℕ}
    (hA : nbhd s A ⊆ (st i).Zpre ω crit) (hB : nbhd t B ⊆ (st j).Zpre ω crit) (hc : c < ω)
    {u v : Torus d n1} (hu : u ∈ A) (hv : v ∈ B) (huv : supDist u v ≤ s + c + t) : False := by
  obtain ⟨y, h1, h2⟩ := exists_split (x := u) (z := v) (a := s) (b := c + t) (by omega)
  obtain ⟨z, h3, h4⟩ := exists_split (x := y) (z := v) (a := c) (b := t) h2
  have hy : y ∈ (st i).Zpre ω crit := hA (mem_nbhd.mpr ⟨u, hu, by rw [supDist_comm]; exact h1⟩)
  have hz : z ∈ (st j).Zpre ω crit := hB (mem_nbhd.mpr ⟨v, hv, h4⟩)
  have := hsep i hi j hj hij y hy z hz
  omega

omit [NeZero n0] in
/-- Two points within `a` and `b` of `x` are within `a + b` of each other. -/
theorem supDist_le_of_near {x u v : Torus d n1} {a b : ℕ} (hu : supDist x u ≤ a)
    (hv : supDist x v ≤ b) : supDist u v ≤ a + b := by
  have := supDist_triangle u x v
  rw [supDist_comm u x] at this
  omega

omit [NeZero n0] [NeZero n1] in
/-- From a subfamily with at most one member: a point outside a derived set of its union is outside
the derived set of a member (the empty family reads the whole torus). -/
theorem exists_not_mem_of_subsingleton (D : PreStep d L n0 n1 Rprev Rk → Set (Torus d n1))
    (hD : ∀ y, y ∈ D (PreStep.biUnion ∅ (fun i => (st i).toPre))) {C : Finset ι} (hCF : C ⊆ F)
    (hC : ∀ i ∈ C, ∀ j ∈ C, i = j) {x : Torus d n1}
    (hx : x ∉ D (PreStep.biUnion C (fun i => (st i).toPre))) :
    ∃ i ∈ F, x ∉ D (st i).toPre := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · exact absurd (hD x) hx
  · have hCi : C = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j hj => hC j hj i hi⟩
    rw [hCi, PreStep.biUnion_singleton] at hx
    exact ⟨i, hCF hi, hx⟩

variable (hsep : SepFam ω F (fun i => (st i).Zpre ω crit)) (hω : 2 * L < ω) (hL : 2 ≤ L)
include hsep hω hL

/-- **`Ω'ᶜ` of the union of separated steps is the union of the `Ω'ᶜ`** (no witness). -/
theorem compl_OmegaPrime_biUnion_of_sep :
    (PreStep.biUnion F (fun i => (st i).toPre)).OmegaPrimeᶜ = ⋃ i ∈ F, (st i).OmegaPrimeᶜ := by
  classical
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · set C := F.filter fun i => ∃ u ∈ (st i).Uprime, supDist x u ≤ L + ⌊Rk⌋₊ + 3 with hCdef
    have hCF : C ⊆ F := Finset.filter_subset _ _
    have hloc := PreStep.not_mem_OmegaPrime_of_local (by omega : 1 ≤ L)
      (p := PreStep.biUnion C (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun u hu hd => by
        obtain ⟨i, hi, hui⟩ := PreStep.mem_Uprime_biUnion.mp hu
        exact PreStep.mem_Uprime_biUnion.mpr ⟨i, Finset.mem_filter.2 ⟨hi, u, hui, hd⟩, hui⟩) hx
    have hC : ∀ i ∈ C, ∀ j ∈ C, i = j := by
      intro i hi j hj
      by_contra hij
      obtain ⟨hiF, u, hu, hxu⟩ := Finset.mem_filter.1 hi
      obtain ⟨hjF, v, hv, hxv⟩ := Finset.mem_filter.1 hj
      exact false_of_sep hsep hiF hjF hij ((st i).nbhd_Uprime_subset_Zpre ω crit)
        ((st j).nbhd_Uprime_subset_Zpre ω crit) (c := 2 * L - 2) (by omega) hu hv
        (by have := supDist_le_of_near hxu hxv; omega)
    obtain ⟨i, hi, hxi⟩ := exists_not_mem_of_subsingleton (fun p => p.OmegaPrime)
      (fun y => by simp only [PreStep.biUnion_empty_OmegaPrime _ (show 0 < L by omega), Set.mem_univ]) hCF hC hloc
    exact Set.mem_biUnion hi hxi
  · exact Set.compl_subset_compl.mpr (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).OmegaPrime

/-- **`Ωᶜ` of the union of separated steps is the union of the `Ωᶜ`** (no witness). -/
theorem compl_Omega_biUnion_of_sep :
    (PreStep.biUnion F (fun i => (st i).toPre)).Omegaᶜ = ⋃ i ∈ F, (st i).Omegaᶜ := by
  classical
  have hG1 := compl_OmegaPrime_biUnion_of_sep hsep hω hL
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · set C := F.filter fun i => (∃ y, y ∉ (st i).OmegaPrime ∧ supDist x y ≤ L - 1) ∨
      ∃ u ∈ (st i).P, supDist x u ≤ L + 2 with hCdef
    have hCF : C ⊆ F := Finset.filter_subset _ _
    have hloc := PreStep.not_mem_Omega_of_local (by omega : 1 ≤ L)
      (p := PreStep.biUnion C (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun y hd hy => by
        have hy' : y ∈ (PreStep.biUnion F (fun i => (st i).toPre)).OmegaPrimeᶜ := hy
        rw [hG1] at hy'
        simp only [Set.mem_iUnion, exists_prop] at hy'
        obtain ⟨i, hi, hyi⟩ := hy'
        have hiC : i ∈ C := Finset.mem_filter.2 ⟨hi, Or.inl ⟨y, hyi, hd⟩⟩
        exact fun h => hyi ((PreStep.le_biUnion (p := fun i => (st i).toPre) hiC).OmegaPrime h))
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, Finset.mem_filter.2 ⟨hi, Or.inr ⟨u, hui, hd⟩⟩, hui⟩) hx
    have hC : ∀ i ∈ C, ∀ j ∈ C, i = j := by
      intro i hi j hj
      by_contra hij
      obtain ⟨hiF, hi'⟩ := Finset.mem_filter.1 hi
      obtain ⟨hjF, hj'⟩ := Finset.mem_filter.1 hj
      have hO : ∀ l, nbhd 0 (st l).OmegaPrimeᶜ ⊆ (st l).Zpre ω crit := fun l => by
        rw [nbhd_zero]; exact (st l).OmegaPrime_compl_subset_Zpre ω crit
      rcases hi' with ⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩ <;> rcases hj' with ⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩
      · exact false_of_sep hsep hiF hjF hij (hO i) (hO j) (c := 2 * L - 2) (by omega)
          (show u ∈ (st i).OmegaPrimeᶜ from hu) (show v ∈ (st j).OmegaPrimeᶜ from hv)
          (by have := supDist_le_of_near hxu hxv; omega)
      · exact false_of_sep hsep hiF hjF hij (hO i) ((st j).nbhd_P_subset_Zpre ω crit)
          (c := 2 * L - 2) (by omega) (show u ∈ (st i).OmegaPrimeᶜ from hu) hv
          (by have := supDist_le_of_near hxu hxv; omega)
      · exact false_of_sep hsep hiF hjF hij ((st i).nbhd_P_subset_Zpre ω crit) (hO j)
          (c := 2 * L - 2) (by omega) hu (show v ∈ (st j).OmegaPrimeᶜ from hv)
          (by have := supDist_le_of_near hxu hxv; omega)
      · exact false_of_sep hsep hiF hjF hij ((st i).nbhd_P_subset_Zpre ω crit)
          ((st j).nbhd_P_subset_Zpre ω crit) (c := 2 * L - 2) (by omega) hu hv
          (by have := supDist_le_of_near hxu hxv; omega)
    obtain ⟨i, hi, hxi⟩ := exists_not_mem_of_subsingleton (fun p => p.Omega)
      (fun y => by simp only [PreStep.biUnion_empty_Omega _ (show 0 < L by omega), Set.mem_univ]) hCF hC hloc
    exact Set.mem_biUnion hi hxi
  · exact Set.compl_subset_compl.mpr (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).Omega

/-- **`Ω''ᶜ` of the union of separated steps is the union of the `Ω''ᶜ`** (no witness). -/
theorem compl_OmegaDD_biUnion_of_sep :
    (PreStep.biUnion F (fun i => (st i).toPre)).OmegaDDᶜ = ⋃ i ∈ F, (st i).OmegaDDᶜ := by
  classical
  have hG2 := compl_Omega_biUnion_of_sep hsep hω hL
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · set C := F.filter fun i => (∃ y, y ∉ (st i).Omega ∧ supDist x y ≤ L - 1) ∨
      (∃ u ∈ (st i).Q, supDist x u ≤ L + ⌊Rk⌋₊ + 1) ∨
      ∃ u ∈ (st i).R, supDist x u ≤ L + 2 * ⌊Rk⌋₊ + 3 with hCdef
    have hCF : C ⊆ F := Finset.filter_subset _ _
    have hloc := PreStep.not_mem_OmegaDD_of_local (by omega : 1 ≤ L)
      (p := PreStep.biUnion C (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun y hd hy => by
        have hy' : y ∈ (PreStep.biUnion F (fun i => (st i).toPre)).Omegaᶜ := hy
        rw [hG2] at hy'
        simp only [Set.mem_iUnion, exists_prop] at hy'
        obtain ⟨i, hi, hyi⟩ := hy'
        have hiC : i ∈ C := Finset.mem_filter.2 ⟨hi, Or.inl ⟨y, hyi, hd⟩⟩
        exact fun h => hyi ((PreStep.le_biUnion (p := fun i => (st i).toPre) hiC).Omega h))
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, Finset.mem_filter.2 ⟨hi, Or.inr (Or.inl ⟨u, hui, hd⟩)⟩, hui⟩)
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, Finset.mem_filter.2 ⟨hi, Or.inr (Or.inr ⟨u, hui, hd⟩)⟩, hui⟩) hx
    have hC : ∀ i ∈ C, ∀ j ∈ C, i = j := by
      intro i hi j hj
      by_contra hij
      obtain ⟨hiF, hi'⟩ := Finset.mem_filter.1 hi
      obtain ⟨hjF, hj'⟩ := Finset.mem_filter.1 hj
      have hO : ∀ l, nbhd 0 (st l).Omegaᶜ ⊆ (st l).Zpre ω crit := fun l => by
        rw [nbhd_zero]; exact (st l).Omega_compl_subset_Zpre ω crit
      -- the three kinds of read sets with their margins and reading radii
      have key : ∀ l ∈ F, (∃ y, y ∉ (st l).Omega ∧ supDist x y ≤ L - 1) ∨
          (∃ u ∈ (st l).Q, supDist x u ≤ L + ⌊Rk⌋₊ + 1) ∨
          (∃ u ∈ (st l).R, supDist x u ≤ L + 2 * ⌊Rk⌋₊ + 3) →
          ∃ (A : Set (Torus d n1)) (s : ℕ) (u : Torus d n1), nbhd s A ⊆ (st l).Zpre ω crit ∧
            u ∈ A ∧ supDist x u ≤ s + (L - 1) := by
        intro l _ hl
        rcases hl with ⟨y, hy, hxy⟩ | ⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩
        · exact ⟨_, 0, y, hO l, hy, by omega⟩
        · exact ⟨_, ⌊Rk⌋₊ + 2, u, (st l).nbhd_Q_subset_Zpre ω crit, hu, by omega⟩
        · exact ⟨_, 2 * ⌊Rk⌋₊ + 4, u, (st l).nbhd_R_subset_Zpre ω crit, hu, by omega⟩
      obtain ⟨A, s, u, hA, hu, hxu⟩ := key i hiF hi'
      obtain ⟨B, t, v, hB, hv, hxv⟩ := key j hjF hj'
      exact false_of_sep hsep hiF hjF hij hA hB (c := 2 * L - 2) (by omega) hu hv
        (by have := supDist_le_of_near hxu hxv; omega)
    obtain ⟨i, hi, hxi⟩ := exists_not_mem_of_subsingleton (fun p => p.OmegaDD)
      (fun y => by simp only [PreStep.biUnion_empty_OmegaDD _ (show 0 < L by omega), Set.mem_univ]) hCF hC hloc
    exact Set.mem_biUnion hi hxi
  · exact Set.compl_subset_compl.mpr (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).OmegaDD

/-- **`Z^{(0)}` of the union of separated steps is the union of the `Z^{(0)}`** (no witness). -/
theorem eq_Z0_biUnion_of_sep :
    (PreStep.biUnion F (fun i => (st i).toPre)).Z0 = ⋃ i ∈ F, (st i).Z0 := by
  classical
  have hG3 := compl_OmegaDD_biUnion_of_sep hsep hω hL
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · set C := F.filter fun i => (∃ g, g ∉ (st i).OmegaDD ∧ supDist x g ≤ L + ⌊2 * Rk⌋₊ + 5) ∨
      ∃ u ∈ (st i).S, supDist x u ≤ L + ⌊2 * Rk⌋₊ + 3 with hCdef
    have hCF : C ⊆ F := Finset.filter_subset _ _
    have hloc := PreStep.mem_Z0_of_local (by omega : 1 ≤ L)
      (p := PreStep.biUnion C (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun g hd hg => by
        have hg' : g ∈ (PreStep.biUnion F (fun i => (st i).toPre)).OmegaDDᶜ := hg
        rw [hG3] at hg'
        simp only [Set.mem_iUnion, exists_prop] at hg'
        obtain ⟨i, hi, hgi⟩ := hg'
        have hiC : i ∈ C := Finset.mem_filter.2 ⟨hi, Or.inl ⟨g, hgi, hd⟩⟩
        exact fun h => hgi ((PreStep.le_biUnion (p := fun i => (st i).toPre) hiC).OmegaDD h))
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, Finset.mem_filter.2 ⟨hi, Or.inr ⟨u, hui, hd⟩⟩, hui⟩) hx
    have hC : ∀ i ∈ C, ∀ j ∈ C, i = j := by
      intro i hi j hj
      by_contra hij
      obtain ⟨hiF, hi'⟩ := Finset.mem_filter.1 hi
      obtain ⟨hjF, hj'⟩ := Finset.mem_filter.1 hj
      have key : ∀ l ∈ F, (∃ g, g ∉ (st l).OmegaDD ∧ supDist x g ≤ L + ⌊2 * Rk⌋₊ + 5) ∨
          (∃ u ∈ (st l).S, supDist x u ≤ L + ⌊2 * Rk⌋₊ + 3) →
          ∃ (A : Set (Torus d n1)) (s : ℕ) (u : Torus d n1), nbhd s A ⊆ (st l).Zpre ω crit ∧
            u ∈ A ∧ supDist x u ≤ s + L := by
        intro l _ hl
        rcases hl with ⟨g, hg, hxg⟩ | ⟨u, hu, hxu⟩
        · exact ⟨_, ⌊2 * Rk⌋₊ + 6, g, (st l).nbhd_OmegaDD_compl_subset_Zpre ω crit, hg,
            by omega⟩
        · exact ⟨_, ⌊2 * Rk⌋₊ + 3, u, (st l).nbhd_S_subset_Zpre ω crit, hu, by omega⟩
      obtain ⟨A, s, u, hA, hu, hxu⟩ := key i hiF hi'
      obtain ⟨B, t, v, hB, hv, hxv⟩ := key j hjF hj'
      exact false_of_sep hsep hiF hjF hij hA hB (c := 2 * L) hω hu hv
        (by have := supDist_le_of_near hxu hxv; omega)
    have hmem : x ∈ (PreStep.biUnion C (fun i => (st i).toPre)).Z0 := hloc
    obtain ⟨i, hi, hxi⟩ := exists_not_mem_of_subsingleton (fun p => p.Z0ᶜ)
      (fun y => by simp only [PreStep.biUnion_empty_Z0 _ (show 0 < L by omega), Set.compl_empty, Set.mem_univ]) hCF hC (not_not.mpr hmem)
    exact Set.mem_biUnion hi (not_not.mp hxi)
  · exact (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).Z0

/-- **Gluing separated steps without a common witness**: the union of the data of steps whose
`Z^pre` are pairwise `ω`-separated, `2L < ω`, `L ≥ 2`, is a step whose `Z^{(0)}` and `Z^pre` are the unions
and whose restriction to the `Z^pre` of a member is the member. -/
theorem glue_step_of_sep :
    ∃ u : RegionStep d L n0 n1 Rprev Rk,
      u.Z = ⋃ i ∈ F, (st i).Z ∧ u.P = ⋃ i ∈ F, (st i).P ∧ u.Q = ⋃ i ∈ F, (st i).Q ∧
      u.R = ⋃ i ∈ F, (st i).R ∧ u.S = ⋃ i ∈ F, (st i).S ∧
      u.Z0 = ⋃ i ∈ F, (st i).Z0 ∧ u.Zpre ω crit = ⋃ i ∈ F, (st i).Zpre ω crit ∧
      ∀ i ∈ F, u.restrict ((st i).Zpre ω crit) = st i :=
  glue_step_of_identities hsep (by omega) (compl_OmegaPrime_biUnion_of_sep hsep hω hL)
    (compl_Omega_biUnion_of_sep hsep hω hL) (compl_OmegaDD_biUnion_of_sep hsep hω hL)
    (eq_Z0_biUnion_of_sep hsep hω hL)

end Sep

end Balaban.LargeField
