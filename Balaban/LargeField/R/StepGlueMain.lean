module

public import Balaban.LargeField.R.StepGlue
public import Balaban.LargeField.Budget.Injective
import Mathlib.Tactic.Linarith

/-!
# Gluing local steps: the main theorem (the step-level core of Lemma III.10.2)

See `R/StepGlue.lean`.  `glue_step`: let `st i`, `i ∈ F`, be steps whose `Z^pre` are pairwise
`ω`-separated, and such that for every point `x` the members with `Z^pre` within `ϱ` of `x` are
witnessed by one step.  Then the union of the data is a step `u` with
`u.Z^{(0)} = ⋃ (st i).Z^{(0)}`, `u.Z^pre = ⋃ (st i).Z^pre`, and `u.restrict ((st i).Z^pre) = st i`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk) (ω : ℕ) (crit : Option ℕ)

theorem Uprime_subset_Zpre : st.Uprime ⊆ st.Zpre ω crit :=
  st.Uprime_subset_Z0.trans (st.Z0_subset_Zpre ω crit)

theorem P_subset_Zpre : st.P ⊆ st.Zpre ω crit := fun _ hx =>
  st.Z0_subset_Zpre ω crit (st.newCubes_subset_Z0 (Or.inl (Or.inl (Or.inl hx))))

theorem Q_subset_Zpre : st.Q ⊆ st.Zpre ω crit := fun _ hx =>
  st.Z0_subset_Zpre ω crit (st.newCubes_subset_Z0 (Or.inl (Or.inl (Or.inr hx))))

theorem R_subset_Zpre : st.R ⊆ st.Zpre ω crit := fun _ hx =>
  st.Z0_subset_Zpre ω crit (st.newCubes_subset_Z0 (Or.inl (Or.inr hx)))

theorem S_subset_Zpre : st.S ⊆ st.Zpre ω crit := fun _ hx =>
  st.Z0_subset_Zpre ω crit (st.newCubes_subset_Z0 (Or.inr hx))

theorem OmegaPrime_compl_subset_Zpre : st.OmegaPrimeᶜ ⊆ st.Zpre ω crit :=
  st.OmegaPrime_compl_subset_Z0.trans (st.Z0_subset_Zpre ω crit)

theorem Omega_compl_subset_Zpre : st.Omegaᶜ ⊆ st.Zpre ω crit :=
  st.Omega_compl_subset_Z0.trans (st.Z0_subset_Zpre ω crit)

theorem OmegaDD_compl_subset_Zpre : st.OmegaDDᶜ ⊆ st.Zpre ω crit :=
  st.OmegaDD_compl_subset_Z0.trans (st.Z0_subset_Zpre ω crit)

end RegionStep

section Witness

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ} {ι : Type*}

theorem linkClosed_biUnion {ω : ℕ} {Xc : Set (Torus d n1)} {V : ι → Set (Torus d n1)}
    {C : Finset ι} (h : ∀ i ∈ C, LinkClosed ω Xc (V i)) : LinkClosed ω Xc (⋃ i ∈ C, V i) := by
  intro x hx y hy hxy
  simp only [Set.mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hi, h i hi x hxi y hy hxy⟩

/-- The steps `st i`, `i ∈ C`, are the restrictions of one step `big` to link-closed sets. -/
def Witness (ω : ℕ) (crit : Option ℕ) (st : ι → RegionStep d L n0 n1 Rprev Rk) (C : Finset ι) :
    Prop :=
  ∃ (big : RegionStep d L n0 n1 Rprev Rk) (V : ι → Set (Torus d n1)),
    (∀ i ∈ C, LinkClosed ω (big.Zpre ω crit) (V i)) ∧ ∀ i ∈ C, st i = big.restrict (V i)

theorem biUnion_restrict (C : Finset ι) (big : RegionStep d L n0 n1 Rprev Rk)
    (V : ι → Set (Torus d n1)) :
    PreStep.biUnion C (fun i => (big.restrict (V i)).toPre) =
      (big.restrict (⋃ i ∈ C, V i)).toPre := by
  refine PreStep.ext ?_ ?_ ?_ ?_ ?_
  · ext z
    simp [PreStep.biUnion, RegionStep.toPre, RegionStep.restrict, RegionStep.sub]
  all_goals
    ext z
    simp [PreStep.biUnion, RegionStep.toPre, RegionStep.restrict, RegionStep.sub]

variable {ω r : ℕ} (hn : n0 = L * n1) (rad : StepRadii L ω r Rprev Rk) {crit : Option ℕ}
  {st : ι → RegionStep d L n0 n1 Rprev Rk} {C : Finset ι}

include hn rad

theorem Witness.compl_OmegaPrime (hW : Witness ω crit st C) :
    (PreStep.biUnion C (fun i => (st i).toPre)).OmegaPrimeᶜ = ⋃ i ∈ C, (st i).OmegaPrimeᶜ := by
  obtain ⟨big, V, hcl, hst⟩ := hW
  rw [PreStep.biUnion_congr (fun i hi => by rw [hst i hi]), biUnion_restrict]
  have hW' := linkClosed_biUnion hcl
  show (big.restrict _).OmegaPrimeᶜ = _
  rw [← big.OmegaPrime_compl_inter_closed crit hn rad hW', Set.inter_iUnion₂]
  refine Set.iUnion₂_congr fun i hi => ?_
  rw [hst i hi, big.OmegaPrime_compl_inter_closed crit hn rad (hcl i hi)]

theorem Witness.compl_Omega (hW : Witness ω crit st C) :
    (PreStep.biUnion C (fun i => (st i).toPre)).Omegaᶜ = ⋃ i ∈ C, (st i).Omegaᶜ := by
  obtain ⟨big, V, hcl, hst⟩ := hW
  rw [PreStep.biUnion_congr (fun i hi => by rw [hst i hi]), biUnion_restrict]
  have hW' := linkClosed_biUnion hcl
  show (big.restrict _).Omegaᶜ = _
  rw [← big.Omega_compl_inter_closed crit hn rad hW', Set.inter_iUnion₂]
  refine Set.iUnion₂_congr fun i hi => ?_
  rw [hst i hi, big.Omega_compl_inter_closed crit hn rad (hcl i hi)]

theorem Witness.compl_OmegaDD (hW : Witness ω crit st C) :
    (PreStep.biUnion C (fun i => (st i).toPre)).OmegaDDᶜ = ⋃ i ∈ C, (st i).OmegaDDᶜ := by
  obtain ⟨big, V, hcl, hst⟩ := hW
  rw [PreStep.biUnion_congr (fun i hi => by rw [hst i hi]), biUnion_restrict]
  have hW' := linkClosed_biUnion hcl
  show (big.restrict _).OmegaDDᶜ = _
  rw [← big.OmegaDD_compl_inter_closed crit hn rad hW', Set.inter_iUnion₂]
  refine Set.iUnion₂_congr fun i hi => ?_
  rw [hst i hi, big.OmegaDD_compl_inter_closed crit hn rad (hcl i hi)]

theorem Witness.eq_Z0 (hW : Witness ω crit st C) :
    (PreStep.biUnion C (fun i => (st i).toPre)).Z0 = ⋃ i ∈ C, (st i).Z0 := by
  obtain ⟨big, V, hcl, hst⟩ := hW
  rw [PreStep.biUnion_congr (fun i hi => by rw [hst i hi]), biUnion_restrict]
  have hW' := linkClosed_biUnion hcl
  show (big.restrict _).Z0 = _
  rw [← big.Z0_inter_closed crit hn rad hW', Set.inter_iUnion₂]
  refine Set.iUnion₂_congr fun i hi => ?_
  rw [hst i hi, big.Z0_inter_closed crit hn rad (hcl i hi)]

end Witness

/-! ### The global identities -/

section Global

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ} {ι : Type*}
  {ω r : ℕ} (crit : Option ℕ) (F : Finset ι) (st : ι → RegionStep d L n0 n1 Rprev Rk)

/-- The locality radius `ϱ = L + 2⌊R_k⌋ + 6` of the set functions of one step. -/
noncomputable def glueRadius (L : ℕ) (Rk : ℝ) : ℕ := L + 2 * ⌊Rk⌋₊ + 6

open Classical in
/-- The members of `F` whose `Z^pre` comes within `ϱ` of `x`. -/
noncomputable def near (ω : ℕ) (x : Torus d n1) : Finset ι :=
  F.filter fun i => ∃ w ∈ (st i).Zpre ω crit, supDist x w ≤ glueRadius L Rk

variable {crit F st}

theorem mem_near {x : Torus d n1} {i : ι} (hi : i ∈ F) {w : Torus d n1}
    (hw : w ∈ (st i).Zpre ω crit) (hd : supDist x w ≤ glueRadius L Rk) :
    i ∈ near crit F st ω x := by
  classical
  simp only [near, Finset.mem_filter]
  exact ⟨hi, w, hw, hd⟩

theorem near_subset (x : Torus d n1) : near crit F st ω x ⊆ F := by
  classical
  intro i hi
  simp only [near, Finset.mem_filter] at hi
  exact hi.1

variable (hn : n0 = L * n1) (rad : StepRadii L ω r Rprev Rk)
  (hwit : ∀ x : Torus d n1, Witness ω crit st (near crit F st ω x))

include hn rad hwit

private theorem rho2_bound : ⌊2 * Rk⌋₊ ≤ 2 * ⌊Rk⌋₊ + 1 := rad.rho2_le'

theorem compl_OmegaPrime_biUnion (hL : 1 ≤ L) :
    (PreStep.biUnion F (fun i => (st i).toPre)).OmegaPrimeᶜ = ⋃ i ∈ F, (st i).OmegaPrimeᶜ := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · have hV := (hwit x).compl_OmegaPrime hn rad
    have hle : PreStep.Le (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre))
        (PreStep.biUnion F (fun i => (st i).toPre)) := PreStep.biUnion_le (near_subset x) _
    have h := PreStep.not_mem_OmegaPrime_of_local hL (p := PreStep.biUnion (near crit F st ω x)
      (fun i => (st i).toPre)) (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun u hu hd => by
        obtain ⟨i, hi, hui⟩ := PreStep.mem_Uprime_biUnion.mp hu
        have hz : u ∈ (st i).Zpre ω crit := (st i).Uprime_subset_Zpre ω crit hui
        have hi' := mem_near (x := x) hi hz (by unfold glueRadius; omega)
        exact PreStep.mem_Uprime_biUnion.mpr ⟨i, hi', hui⟩) hx
    have h2 : x ∈ (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre)).OmegaPrimeᶜ := h
    rw [hV] at h2
    simp only [Set.mem_iUnion, exists_prop] at h2 ⊢
    obtain ⟨i, hi, hxi⟩ := h2
    exact ⟨i, near_subset x hi, hxi⟩
  · exact Set.compl_subset_compl.mpr (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).OmegaPrime

theorem compl_Omega_biUnion (hL : 1 ≤ L) :
    (PreStep.biUnion F (fun i => (st i).toPre)).Omegaᶜ = ⋃ i ∈ F, (st i).Omegaᶜ := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · have hV := (hwit x).compl_Omega hn rad
    have h := PreStep.not_mem_Omega_of_local hL
      (p := PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun y hd hy => by
        have hy' : y ∈ (PreStep.biUnion F (fun i => (st i).toPre)).OmegaPrimeᶜ := hy
        rw [compl_OmegaPrime_biUnion hn rad hwit hL] at hy'
        simp only [Set.mem_iUnion, exists_prop] at hy'
        obtain ⟨i, hi, hyi⟩ := hy'
        have hz := (st i).OmegaPrime_compl_subset_Zpre ω crit hyi
        have hi' := mem_near (x := x) hi hz (by unfold glueRadius; omega)
        have : y ∈ (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre)).OmegaPrimeᶜ := by
          rw [(hwit x).compl_OmegaPrime hn rad]; exact Set.mem_biUnion hi' hyi
        exact this)
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, mem_near (x := x) hi ((st i).P_subset_Zpre ω crit hui)
          (by unfold glueRadius; omega), hui⟩) hx
    have h2 : x ∈ (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre)).Omegaᶜ := h
    rw [hV] at h2
    simp only [Set.mem_iUnion, exists_prop] at h2 ⊢
    obtain ⟨i, hi, hxi⟩ := h2
    exact ⟨i, near_subset x hi, hxi⟩
  · exact Set.compl_subset_compl.mpr (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).Omega

theorem compl_OmegaDD_biUnion (hL : 1 ≤ L) :
    (PreStep.biUnion F (fun i => (st i).toPre)).OmegaDDᶜ = ⋃ i ∈ F, (st i).OmegaDDᶜ := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · have hV := (hwit x).compl_OmegaDD hn rad
    have h := PreStep.not_mem_OmegaDD_of_local hL
      (p := PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun y hd hy => by
        have hy' : y ∈ (PreStep.biUnion F (fun i => (st i).toPre)).Omegaᶜ := hy
        rw [compl_Omega_biUnion hn rad hwit hL] at hy'
        simp only [Set.mem_iUnion, exists_prop] at hy'
        obtain ⟨i, hi, hyi⟩ := hy'
        have hz := (st i).Omega_compl_subset_Zpre ω crit hyi
        have hi' := mem_near (x := x) hi hz (by unfold glueRadius; omega)
        have : y ∈ (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre)).Omegaᶜ := by
          rw [(hwit x).compl_Omega hn rad]; exact Set.mem_biUnion hi' hyi
        exact this)
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, mem_near (x := x) hi ((st i).Q_subset_Zpre ω crit hui)
          (by unfold glueRadius; omega), hui⟩)
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, mem_near (x := x) hi ((st i).R_subset_Zpre ω crit hui)
          (by unfold glueRadius; omega), hui⟩) hx
    have h2 : x ∈ (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre)).OmegaDDᶜ := h
    rw [hV] at h2
    simp only [Set.mem_iUnion, exists_prop] at h2 ⊢
    obtain ⟨i, hi, hxi⟩ := h2
    exact ⟨i, near_subset x hi, hxi⟩
  · exact Set.compl_subset_compl.mpr (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).OmegaDD

theorem eq_Z0_biUnion (hL : 1 ≤ L) :
    (PreStep.biUnion F (fun i => (st i).toPre)).Z0 = ⋃ i ∈ F, (st i).Z0 := by
  have hρ := rho2_bound hn rad hwit
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => ?_)
  · have hV := (hwit x).eq_Z0 hn rad
    have h := PreStep.mem_Z0_of_local hL
      (p := PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre))
      (q := PreStep.biUnion F (fun i => (st i).toPre)) (x := x)
      (fun y hd hy => by
        have hy' : y ∈ (PreStep.biUnion F (fun i => (st i).toPre)).OmegaDDᶜ := hy
        rw [compl_OmegaDD_biUnion hn rad hwit hL] at hy'
        simp only [Set.mem_iUnion, exists_prop] at hy'
        obtain ⟨i, hi, hyi⟩ := hy'
        have hz := (st i).OmegaDD_compl_subset_Zpre ω crit hyi
        have hi' := mem_near (x := x) hi hz (by unfold glueRadius; omega)
        have : y ∈ (PreStep.biUnion (near crit F st ω x) (fun i => (st i).toPre)).OmegaDDᶜ := by
          rw [(hwit x).compl_OmegaDD hn rad]; exact Set.mem_biUnion hi' hyi
        exact this)
      (fun u hu hd => by
        simp only [PreStep.biUnion, RegionStep.toPre, Set.mem_iUnion, exists_prop] at hu ⊢
        obtain ⟨i, hi, hui⟩ := hu
        exact ⟨i, mem_near (x := x) hi ((st i).S_subset_Zpre ω crit hui)
          (by unfold glueRadius; omega), hui⟩) hx
    rw [hV] at h
    simp only [Set.mem_iUnion, exists_prop] at h ⊢
    obtain ⟨i, hi, hxi⟩ := h
    exact ⟨i, near_subset x hi, hxi⟩
  · exact (PreStep.le_biUnion (p := fun i => (st i).toPre) hi).Z0

omit hn rad hwit in
theorem not_mem_iUnion_of_sep {A : ι → Set (Torus d n1)}
    (hA : ∀ i ∈ F, A i ⊆ (st i).Zpre ω crit) (hsep : SepFam ω F (fun i => (st i).Zpre ω crit))
    (h3 : 3 < ω) {i : ι} (hi : i ∈ F) {q y : Torus d n1} (hq : q ∈ (st i).Zpre ω crit)
    (hqy : supDist q y ≤ 3) (hy : y ∉ A i) : y ∉ ⋃ i' ∈ F, A i' := by
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
  intro i' hi' hyi'
  by_cases h : i' = i
  · subst h; exact hy hyi'
  · have := hsep i hi i' hi' (Ne.symm h) q hq y (hA i' hi' hyi')
    omega

omit hn rad hwit in
theorem inter_iUnion_eq_of_sep {A : ι → Set (Torus d n1)}
    (hA : ∀ i ∈ F, A i ⊆ (st i).Zpre ω crit) (hsep : SepFam ω F (fun i => (st i).Zpre ω crit))
    (h1 : 1 ≤ ω) {i0 : ι} (hi0 : i0 ∈ F) :
    (⋃ i ∈ F, A i) ∩ (st i0).Zpre ω crit = A i0 := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨i, hi, hyi⟩, hy0⟩
    by_cases h : i = i0
    · subst h; exact hyi
    · have := hsep i hi i0 hi0 h y (hA i hi hyi) y hy0
      rw [supDist_self] at this
      omega
  · intro hy
    exact ⟨⟨i0, hi0, hy⟩, hA i0 hi0 hy⟩

/-- **Gluing local steps** (the step-level core of Lemma III.10.2).  The union of the data of
steps whose `Z^pre` are pairwise `ω`-separated is a step, provided that near every point the
members are witnessed by one step.  Its `Z^{(0)}` and `Z^pre` are the unions, and it restricts to
each member on the `Z^pre` of the member. -/
theorem glue_step (hsep : SepFam ω F (fun i => (st i).Zpre ω crit)) :
    ∃ u : RegionStep d L n0 n1 Rprev Rk,
      u.Z = ⋃ i ∈ F, (st i).Z ∧ u.P = ⋃ i ∈ F, (st i).P ∧ u.Q = ⋃ i ∈ F, (st i).Q ∧
      u.R = ⋃ i ∈ F, (st i).R ∧ u.S = ⋃ i ∈ F, (st i).S ∧
      u.Z0 = ⋃ i ∈ F, (st i).Z0 ∧ u.Zpre ω crit = ⋃ i ∈ F, (st i).Zpre ω crit ∧
      ∀ i ∈ F, u.restrict ((st i).Zpre ω crit) = st i := by
  have hL : 1 ≤ L := by have := rad.L_two; omega
  have h3 : 3 < ω := by have := rad.L_two; have := rad.omega_rho; omega
  have hG1 := compl_OmegaPrime_biUnion hn rad hwit hL
  have hG2 := compl_Omega_biUnion hn rad hwit hL
  have hG3 := compl_OmegaDD_biUnion hn rad hwit hL
  have hG4 := eq_Z0_biUnion hn rad hwit hL
  -- validity
  have hP : (⋃ i ∈ F, (st i).P) ⊆ (PreStep.biUnion F (fun i => (st i).toPre)).OmegaPrime := by
    intro p hp
    simp only [Set.mem_iUnion, exists_prop] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    have := not_mem_iUnion_of_sep (A := fun i' => (st i').OmegaPrimeᶜ)
      (fun i' _ => (st i').OmegaPrime_compl_subset_Zpre ω crit) hsep h3 hi
      ((st i).P_subset_Zpre ω crit hpi) (by rw [supDist_self]; omega)
      (fun h => h ((st i).P_sub hpi))
    rw [← hG1] at this
    exact Set.notMem_compl_iff.mp this
  have hR : (⋃ i ∈ F, (st i).R) ⊆ (PreStep.biUnion F (fun i => (st i).toPre)).Omega := by
    intro p hp
    simp only [Set.mem_iUnion, exists_prop] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    have := not_mem_iUnion_of_sep (A := fun i' => (st i').Omegaᶜ)
      (fun i' _ => (st i').Omega_compl_subset_Zpre ω crit) hsep h3 hi
      ((st i).R_subset_Zpre ω crit hpi) (by rw [supDist_self]; omega)
      (fun h => h ((st i).R_sub hpi))
    rw [← hG2] at this
    exact Set.notMem_compl_iff.mp this
  have hQ : (⋃ i ∈ F, (st i).Q) ⊆ nbhd 3 (PreStep.biUnion F (fun i => (st i).toPre)).Omega := by
    intro q hq
    simp only [Set.mem_iUnion, exists_prop] at hq
    obtain ⟨i, hi, hqi⟩ := hq
    obtain ⟨y, hy, hqy⟩ := mem_nbhd.mp ((st i).Q_sub hqi)
    refine mem_nbhd.mpr ⟨y, ?_, hqy⟩
    have := not_mem_iUnion_of_sep (A := fun i' => (st i').Omegaᶜ)
      (fun i' _ => (st i').Omega_compl_subset_Zpre ω crit) hsep h3 hi
      ((st i).Q_subset_Zpre ω crit hqi) hqy (fun h => h hy)
    rw [← hG2] at this
    exact Set.notMem_compl_iff.mp this
  have hS : (⋃ i ∈ F, (st i).S) ⊆ nbhdNeg 3 (PreStep.biUnion F (fun i => (st i).toPre)).OmegaDD := by
    intro s hs
    simp only [Set.mem_iUnion, exists_prop] at hs
    obtain ⟨i, hi, hsi⟩ := hs
    refine mem_nbhdNeg.mpr fun y hy => ?_
    have hyi := mem_nbhdNeg.mp ((st i).S_sub hsi) y hy
    have := not_mem_iUnion_of_sep (A := fun i' => (st i').OmegaDDᶜ)
      (fun i' _ => (st i').OmegaDD_compl_subset_Zpre ω crit) hsep h3 hi
      ((st i).S_subset_Zpre ω crit hsi) hy (fun h => h hyi)
    rw [← hG3] at this
    exact Set.notMem_compl_iff.mp this
  refine ⟨⟨⋃ i ∈ F, (st i).Z, ⋃ i ∈ F, (st i).P, ⋃ i ∈ F, (st i).Q, ⋃ i ∈ F, (st i).R,
    ⋃ i ∈ F, (st i).S, hP, hQ, hR, hS⟩, rfl, rfl, rfl, rfl, rfl, hG4, ?_, ?_⟩
  · -- Zpre
    show Region.Zpre ω crit (PreStep.biUnion F (fun i => (st i).toPre)).Z0 = _
    rw [hG4]
    cases crit with
    | none => rfl
    | some b =>
      exact hullClosure_iUnion_sep hsep
  · intro i0 hi0
    have h1 : 1 ≤ ω := by omega
    refine RegionStep.eq_of_fields ?_ ?_ ?_ ?_ ?_
    · show {z | z ∈ (⋃ i ∈ F, (st i).Z) ∧ blockMap L n1 z ∈ (st i0).Zpre ω crit} = (st i0).Z
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨⟨i, hi, hzi⟩, hz0⟩
        by_cases h : i = i0
        · subst h; exact hzi
        · have hzW := (st i).Uprime_subset_Zpre ω crit ((st i).blockMap_Z_subset_Uprime hzi)
          have := hsep i hi i0 hi0 h _ hzW _ hz0
          rw [supDist_self] at this
          omega
      · intro hz
        exact ⟨⟨i0, hi0, hz⟩, (st i0).Uprime_subset_Zpre ω crit ((st i0).blockMap_Z_subset_Uprime hz)⟩
    · exact inter_iUnion_eq_of_sep (A := fun i => (st i).P)
        (fun i _ => (st i).P_subset_Zpre ω crit) hsep h1 hi0
    · exact inter_iUnion_eq_of_sep (A := fun i => (st i).Q)
        (fun i _ => (st i).Q_subset_Zpre ω crit) hsep h1 hi0
    · exact inter_iUnion_eq_of_sep (A := fun i => (st i).R)
        (fun i _ => (st i).R_subset_Zpre ω crit) hsep h1 hi0
    · exact inter_iUnion_eq_of_sep (A := fun i => (st i).S)
        (fun i _ => (st i).S_subset_Zpre ω crit) hsep h1 hi0

end Global

end Balaban.LargeField
