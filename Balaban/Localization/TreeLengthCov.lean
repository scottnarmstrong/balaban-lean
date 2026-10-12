/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLength
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The covering size functional and (GM2), version 3 (LOCALIZATION.md §4.0, §4.2, Def-L8)

P1's tree lengths `d̃` (`dTilde`) and `d_j` (`dScale`) ask for a connected structure meeting
*every* `π'_n`-cube contained in the domain.  For these, (GM2) is false in general
(`notes/phase1/CHECKS1-astra.md` §1).  The repaired size functionals are the *covering*
functionals: the infimum is taken jointly over a *chosen family* of cubes (cubes contained in
`Y ∩ Λ_n` whose union is `Y ∩ Λ_n`) and a connected structure meeting every chosen cube.

* `ChosenOne`, `ChosenFamily`: chosen families (single scale, all scales).
* `treeLenCovOne`, `treeLenCov`: the functionals `d^cov_j`, `d̃^cov_{k+1}`.
* `CovSetup`, `Q0`, `X1`: the data of (GM2) v3 (`𝒦_X`, `𝒬₀`, `X₁ = ⋃𝒬₀`); no hypothesis that
  every coarse cube inside `X₁` contains a fine cube of `X`.
* `KY`, `chosen_KY`: the family `𝒦_Y` is a chosen family of `Y[𝒞]`.
* `gm2_tree`, `gm2`: the corrected (GM2).
* `treeLenCov_le_dTilde`: `d̃^cov ≤ d̃`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Cov

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- `𝒦` is a *chosen family* of `X` at scale `j`: a set of `π'_j`-cubes (aligned bases), each
contained in `X`, whose union is `X`. -/
def ChosenOne (j : ℕ) (X : Set (CTorus d L N₁ m₁ K)) (𝒦 : Set (CTorus d L N₁ m₁ K)) : Prop :=
  (∀ b ∈ 𝒦, Aligned (cellSide L m₀ m₁ j) b ∧ box b (L * cellSide L m₀ m₁ j) ⊆ X) ∧
    ∀ z ∈ X, ∃ b ∈ 𝒦, z ∈ box b (L * cellSide L m₀ m₁ j)

/-- `𝒦 = (𝒦_n)` is a *chosen family* of `Y`: for `1 ≤ n ≤ K`, `𝒦_n` is a set of `π'_n`-cubes
contained in `Y ∩ Λ_n` whose union is `Y ∩ Λ_n`. -/
def ChosenFamily (Y : Set (CTorus d L N₁ m₁ K)) (𝒦 : ℕ → Set (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ n, 1 ≤ n → n ≤ K →
    (∀ b ∈ 𝒦 n, Aligned (cellSide L m₀ m₁ n) b ∧ box b (L * cellSide L m₀ m₁ n) ⊆ Y ∧
      box b (L * cellSide L m₀ m₁ n) ⊆ (G.layer n : Set (CTorus d L N₁ m₁ K))) ∧
    ∀ z ∈ Y, z ∈ (G.layer n : Set (CTorus d L N₁ m₁ K)) →
      ∃ b ∈ 𝒦 n, z ∈ box b (L * cellSide L m₀ m₁ n)

/-- `W` meets every cube of the one-scale family `𝒦`. -/
def MeetsOne (j : ℕ) (𝒦 : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ b ∈ 𝒦, ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ j)

/-- `W` meets every cube of the family `𝒦 = (𝒦_n)`. -/
def MeetsFam (𝒦 : ℕ → Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ n, 1 ≤ n → n ≤ K → ∀ b ∈ 𝒦 n, ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ n)

/-- **The covering size functional `d̃^cov(Y)`** (`K = k+1`; Def-L8): the infimum of
`∑ bondW` over chosen families of `Y` and connected structures in `Y` meeting every chosen cube. -/
noncomputable def treeLenCov (Y : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  sInf {x | ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧ MeetsFam m₀ 𝒦 W ∧
    x = bondCost (bondW G m₀) E}

/-- **The single-scale covering functional `d^cov_j(X)`**: the infimum of `M⁻¹ℓ_j⁻¹ ·` (number of
bonds) over chosen families of `X` at scale `j` and connected structures in `X` meeting every
chosen cube. -/
noncomputable def treeLenCovOne (j : ℕ) (X : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  sInf {x | ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W ∧
    x = bondCost (scaleW L m₀ m₁ j) E}

omit [NeZero N₁] [NeZero L] in
theorem treeLenCovOne_nonneg (j : ℕ) (X : Set (CTorus d L N₁ m₁ K)) :
    0 ≤ treeLenCovOne m₀ j X := by
  refine Real.sInf_nonneg ?_
  rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
  refine Finset.sum_nonneg fun p _ => ?_
  unfold scaleW; positivity

theorem treeLenCov_nonneg (Y : Set (CTorus d L N₁ m₁ K)) : 0 ≤ treeLenCov G m₀ Y := by
  refine Real.sInf_nonneg ?_
  rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
  exact Finset.sum_nonneg fun p _ => bondW_nonneg G m₀ _ _

/-- The infimum defining `treeLenCovOne` is attained, when the set is nonempty (the index
type is finite). -/
theorem treeLenCovOne_attained (j : ℕ) (X : Set (CTorus d L N₁ m₁ K))
    (hX : ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W) :
    ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W ∧
      bondCost (scaleW L m₀ m₁ j) E = treeLenCovOne m₀ j X := by
  classical
  set S := {x | ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W ∧
    x = bondCost (scaleW L m₀ m₁ j) E} with hS
  have hfin : S.Finite := by
    have : S ⊆ Set.range (fun p : Set (CTorus d L N₁ m₁ K) × Finset (CTorus d L N₁ m₁ K) ×
        Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K) => bondCost (scaleW L m₀ m₁ j) p.2.2) := by
      rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
      exact ⟨(𝒦, W, E), rfl⟩
    exact (Set.finite_range _).subset this
  obtain ⟨𝒦, W, E, h1, h2, h3, h4⟩ := hX
  have hne : S.Nonempty := ⟨_, 𝒦, W, E, h1, h2, h3, h4, rfl⟩
  obtain ⟨𝒦', W', E', h1', h2', h3', h4', he⟩ := hne.csInf_mem hfin
  exact ⟨𝒦', W', E', h1', h2', h3', h4', he.symm⟩

end Cov

/-! ### The data of (GM2), version 3 -/

section GM2

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- `𝒬₀`: the `π'_K`-cubes inside `Λ_K` that contain a cube of the chosen family `𝒦_X`. -/
def Q0 (j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {b | Aligned (cellSide L m₀ m₁ K) b ∧
    box b (L * cellSide L m₀ m₁ K) ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)) ∧
    ∃ q ∈ 𝒦X, box q (L * cellSide L m₀ m₁ j) ⊆ box b (L * cellSide L m₀ m₁ K)}

/-- `X₁ = ⋃ 𝒬₀`. -/
def X1 (j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  ⋃ b ∈ Q0 G m₀ j 𝒦X, box b (L * cellSide L m₀ m₁ K)

/-- The geometric data of (GM2) v3: `X` has the chosen family `𝒦_X` of `π'_j`-cubes (`j < K`),
and each cube of `𝒦_X` lies in a `π'_K`-cube contained in `Λ_K` (this is `X ⊆ Ω_{k+1}` with the
cover `π'_{k+1}`).  Nothing is asserted about other coarse cubes inside `X₁`. -/
structure CovSetup (j : ℕ) (X : Set (CTorus d L N₁ m₁ K)) (𝒦X : Set (CTorus d L N₁ m₁ K)) :
    Prop where
  hU : LayerUnion G m₀
  hN : L ^ m₀ ∣ N₁
  hjK : j + 1 ≤ K
  chosen : ChosenOne m₀ j X 𝒦X
  nest : ∀ b ∈ 𝒦X, ∃ b', Aligned (cellSide L m₀ m₁ K) b' ∧
    box b (L * cellSide L m₀ m₁ j) ⊆ box b' (L * cellSide L m₀ m₁ K) ∧
    box b' (L * cellSide L m₀ m₁ K) ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K))

variable {G m₀}

section Basic

variable {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

theorem X1_layer : X1 G m₀ j 𝒦X ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)) := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
  exact hb.2.1 hxb

theorem X1_cubes : ∀ x ∈ X1 G m₀ j 𝒦X, ∃ b, Aligned (cellSide L m₀ m₁ K) b ∧
    x ∈ box b (L * cellSide L m₀ m₁ K) ∧ box b (L * cellSide L m₀ m₁ K) ⊆ X1 G m₀ j 𝒦X := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨b, hb.1, hxb, fun z hz => Set.mem_iUnion₂.2 ⟨b, hb, hz⟩⟩

theorem CovSetup.polySetup (hS : CovSetup G m₀ j X 𝒦X) : PolySetup G m₀ (X1 G m₀ j 𝒦X) :=
  ⟨hS.hU, hS.hN, X1_layer, X1_cubes⟩

theorem CovSetup.X_sub (hS : CovSetup G m₀ j X 𝒦X) : X ⊆ X1 G m₀ j 𝒦X := by
  intro z hz
  obtain ⟨q, hq, hzq⟩ := hS.chosen.2 z hz
  obtain ⟨b', hb'al, hqb', hb'L⟩ := hS.nest q hq
  exact Set.mem_iUnion₂.2 ⟨b', ⟨hb'al, hb'L, q, hq, hqb'⟩, hqb' hzq⟩

/-- A point of `X₁` is joined, inside `X₁`, to a point of the tree `Γ₀` at cost `2 d L`:
it lies in a cube `Q ∈ 𝒬₀`, which contains a cube of `𝒦_X`, which `Γ₀` meets. -/
theorem attach_none (hS : CovSetup G m₀ j X 𝒦X) {W₀ : Finset (CTorus d L N₁ m₁ K)}
    (hmeet : MeetsOne m₀ j 𝒦X W₀) {x : CTorus d L N₁ m₁ K} (hx : x ∈ X1 G m₀ j 𝒦X) :
    ∃ q ∈ W₀, Linked (X1 G m₀ j 𝒦X) (bondW G m₀) (2 * d * L) x q := by
  have hK : 1 ≤ K := by have := hS.hjK; omega
  obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨hbal, hbL, q, hq, hqb⟩ := hb
  obtain ⟨p, hpW, hpq⟩ := hmeet q hq
  have hpb : p ∈ box b (L * cellSide L m₀ m₁ K) := hqb hpq
  have hbX : box b (L * cellSide L m₀ m₁ K) ⊆ X1 G m₀ j 𝒦X := fun z hz =>
    Set.mem_iUnion₂.2 ⟨b, ⟨hbal, hbL, q, hq, hqb⟩, hz⟩
  have hc : ∀ x ∈ X1 G m₀ j 𝒦X, ∀ y ∈ X1 G m₀ j 𝒦X,
      bondW G m₀ x y ≤ ((cellSide L m₀ m₁ K : ℕ) : ℝ)⁻¹ :=
    fun x hx y hy => (bondW_of_layer G m₀ hK le_rfl (X1_layer hx) (X1_layer hy)).le
  refine ⟨p, hpW, ?_⟩
  have := linked_box_pair (bondW_nonneg G m₀) _ _ hbX hc hxb hpb
  refine Covers.mono_c this (le_of_eq ?_)
  have : ((cellSide L m₀ m₁ K : ℕ) : ℝ) ≠ 0 := by
    have := cellSide_pos (L := L) m₀ m₁ K; positivity
  push_cast
  field_simp

end Basic

/-! #### The nerve -/

section Nerve

variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ K}
variable {X 𝒦X : Set (CTorus d L N₁ m₁ K)} {j : ℕ} {C : Finset ι}

theorem Pset_subset_Ysites' (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G) {i : ι}
    (hi : i ∈ C) : Pset m₁ (c i) ⊆ Ysites G m₀ c (X1 G m₀ j 𝒦X) C :=
  (Pset_subset_Dsites hS.hU hS.hN (hc i)).trans (Dsites_subset_Ysites hi)

theorem link_some_none (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hmeet : MeetsOne m₀ j 𝒦X W₀) {i : ι} (hi : i ∈ C)
    (h : Nerve (X1 G m₀ j 𝒦X) c (some i) none) :
    ∃ a ∈ Dbases G m₀ (c i), ∃ b ∈ W₀,
      Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) (gm2Rho d L) a b := by
  obtain ⟨z, hz, z', hz', hzz⟩ := h
  have hz : z ∈ Pset m₁ (c i) := hz
  have hz' : z' ∈ X1 G m₀ j 𝒦X := hz'
  obtain ⟨q, hqW, hq⟩ := attach_none hS hmeet hz'
  refine ⟨cbase (cellSide L m₀ m₁ (c i).1) (c i).2, cbase_mem_Dbases hS.hU hS.hN (hc i), q, hqW, ?_⟩
  have hzR : z ∈ Ysites G m₀ c (X1 G m₀ j 𝒦X) C := Pset_subset_Ysites' hS hc hi hz
  have hz'R : z' ∈ Ysites G m₀ c (X1 G m₀ j 𝒦X) C :=
    subset_Ysites (G := G) (m₀ := m₀) (c := c) (X1 G m₀ j 𝒦X) C hz'
  have h1 : Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) d _ z :=
    (attach_some hS.hU hS.hN (hc i) hz).mono_R (Dsites_subset_Ysites hi)
  have h2 : Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) 1 z z' := by
    rcases hzz with rfl | hn
    · exact Linked.refl (by norm_num) hzR
    · exact Linked.step hn hzR hz'R (bondW_le_one G m₀ _ _)
  have h3 : Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) (2 * d * L) z' q :=
    hq.mono_R (subset_Ysites (G := G) (m₀ := m₀) (c := c) (X1 G m₀ j 𝒦X) C)
  have := ((h1.trans (bondW_nonneg G m₀) h2).trans (bondW_nonneg G m₀) h3)
  refine Covers.mono_c this ?_
  unfold gm2Rho; linarith

theorem link_some_some (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G) {i i' : ι}
    (hi : i ∈ C) (hi' : i' ∈ C) (h : Nerve (X1 G m₀ j 𝒦X) c (some i) (some i')) :
    ∃ a ∈ Dbases G m₀ (c i), ∃ b ∈ Dbases G m₀ (c i'),
      Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) (gm2Rho d L) a b := by
  obtain ⟨z, hz, z', hz', hzz⟩ := h
  have hz : z ∈ Pset m₁ (c i) := hz
  have hz' : z' ∈ Pset m₁ (c i') := hz'
  refine ⟨cbase (cellSide L m₀ m₁ (c i).1) (c i).2, cbase_mem_Dbases hS.hU hS.hN (hc i),
    cbase (cellSide L m₀ m₁ (c i').1) (c i').2, cbase_mem_Dbases hS.hU hS.hN (hc i'), ?_⟩
  have hzR : z ∈ Ysites G m₀ c (X1 G m₀ j 𝒦X) C := Pset_subset_Ysites' hS hc hi hz
  have hz'R : z' ∈ Ysites G m₀ c (X1 G m₀ j 𝒦X) C := Pset_subset_Ysites' hS hc hi' hz'
  have h1 : Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) d _ z :=
    (attach_some hS.hU hS.hN (hc i) hz).mono_R (Dsites_subset_Ysites hi)
  have h2 : Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) 1 z z' := by
    rcases hzz with rfl | hn
    · exact Linked.refl (by norm_num) hzR
    · exact Linked.step hn hzR hz'R (bondW_le_one G m₀ _ _)
  have h3 : Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) d _ z' :=
    (attach_some hS.hU hS.hN (hc i') hz').mono_R (Dsites_subset_Ysites hi')
  have := ((h1.trans (bondW_nonneg G m₀) h2).trans (bondW_nonneg G m₀) h3.symm)
  refine Covers.mono_c this ?_
  unfold gm2Rho; have : (0 : ℝ) ≤ 2 * d * L := by positivity
  linarith

theorem link_nerve (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hW₀X : ↑W₀ ⊆ X) (hne : W₀.Nonempty)
    (hmeet : MeetsOne m₀ j 𝒦X W₀) {u v : Option ι} (hu : u ∈ Finset.insertNone C)
    (hv : v ∈ Finset.insertNone C) (h : Nerve (X1 G m₀ j 𝒦X) c u v) :
    ∃ a ∈ nodeSet G m₀ c W₀ u, ∃ b ∈ nodeSet G m₀ c W₀ v,
      Linked (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (bondW G m₀) (gm2Rho d L) a b := by
  cases u with
  | none =>
    cases v with
    | none =>
      obtain ⟨q, hq⟩ := hne
      refine ⟨q, hq, q, hq, Linked.refl (by unfold gm2Rho; positivity)
        (subset_Ysites (G := G) (m₀ := m₀) (c := c) (X1 G m₀ j 𝒦X) C (hS.X_sub (hW₀X hq)))⟩
    | some j' =>
      have hj' : j' ∈ C := Finset.some_mem_insertNone.1 hv
      obtain ⟨a, ha, b, hb, hl⟩ := link_some_none hS hc hmeet hj' h.symm
      exact ⟨b, hb, a, ha, hl.symm⟩
  | some i =>
    have hi : i ∈ C := Finset.some_mem_insertNone.1 hu
    cases v with
    | none => exact link_some_none hS hc hmeet hi h
    | some j' => exact link_some_some hS hc hi (Finset.some_mem_insertNone.1 hv) h

/-- **The family `𝒦_Y`**: `𝒬₀` in layer `K`, together with the cubes `□' ∈ Dcubes (c i)` used to
form the sets `D(P_i)`, `i ∈ 𝒞`, in layer `(c i).1`. -/
def KY (c : ι → ℕ × CTorus d L N₁ m₁ K) (j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ K)) (C : Finset ι)
    (n : ℕ) : Set (CTorus d L N₁ m₁ K) :=
  {b | (n = K ∧ b ∈ Q0 G m₀ j 𝒦X) ∨ ∃ i ∈ C, (c i).1 = n ∧ b ∈ Dcubes G m₀ (c i)}

/-- **`𝒦_Y` is a chosen family of `Y[𝒞]`.** -/
theorem chosen_KY (hc : ∀ i, c i ∈ cubeIdx G) :
    ChosenFamily G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) (KY (G := G) (m₀ := m₀) c j 𝒦X C) := by
  intro n hn1 hnK
  refine ⟨?_, ?_⟩
  · rintro b (⟨rfl, hb⟩ | ⟨i, hi, rfl, hb⟩)
    · refine ⟨hb.1, fun z hz => Or.inl (Set.mem_iUnion₂.2 ⟨b, hb, hz⟩), hb.2.1⟩
    · refine ⟨hb.1, fun z hz => Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩), hb.2.2⟩
      exact Set.mem_iUnion₂.2 ⟨b, hb, hz⟩
  · intro z hzY hzn
    rcases hzY with hzX | hzD
    · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 hzX
      have hzK : z ∈ G.layer K := Finset.mem_coe.1 (hb.2.1 hzb)
      have hnK' : n = K := by
        by_contra hne
        have hK1 : 1 ≤ K := by omega
        exact G.layer_disjoint hn1 hnK hK1 le_rfl hne (Finset.mem_coe.1 hzn) hzK
      subst hnK'
      exact ⟨b, Or.inl ⟨rfl, hb⟩, hzb⟩
    · obtain ⟨i, hi, hzD⟩ := Set.mem_iUnion₂.1 hzD
      obtain ⟨⟨hi1, hiK⟩, -, -⟩ := (mem_cubeIdx G).1 (hc i)
      have hzi : z ∈ G.layer (c i).1 := Finset.mem_coe.1 (Dsites_subset_layer (c i) hzD)
      have hni : (c i).1 = n := by
        by_contra hne
        exact G.layer_disjoint hi1 hiK hn1 hnK hne hzi (Finset.mem_coe.1 hzn)
      obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 hzD
      subst hni
      exact ⟨b, Or.inr ⟨i, hi, rfl, hb⟩, hzb⟩

/-- A structure containing the nodes' covers meets every cube of `𝒦_Y`. -/
theorem meets_KY (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hmeet : MeetsOne m₀ j 𝒦X W₀)
    {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : (Finset.insertNone C).biUnion (nodeSet G m₀ c W₀) ⊆ W) :
    MeetsFam m₀ (KY (G := G) (m₀ := m₀) c j 𝒦X C) W := by
  intro n hn1 hnK b hb
  rcases hb with ⟨rfl, hb⟩ | ⟨i, hi, rfl, hb⟩
  · obtain ⟨hbal, hbL, q, hq, hqb⟩ := hb
    obtain ⟨p, hpW, hpq⟩ := hmeet q hq
    exact ⟨p, hW (Finset.mem_biUnion.2 ⟨none, Finset.none_mem_insertNone, hpW⟩), hqb hpq⟩
  · have hx := cbase_mem_Dbases hS.hU hS.hN (hc i)
    refine ⟨_, hW (Finset.mem_biUnion.2 ⟨some i, Finset.some_mem_insertNone.2 hi, hx⟩), ?_⟩
    exact hb.2.1 (mem_box_self _ (cellSide_pos m₀ m₁ (c i).1))

end Nerve

section Main

variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ K}
variable {X 𝒦X : Set (CTorus d L N₁ m₁ K)} {j : ℕ}

/-- **(GM2), tree form (version 3).**  Let `Γ₀ = (W₀, E₀)` be a connected structure in `X`
meeting every cube of the chosen family `𝒦_X`.  Then for every connected family `𝒞` there is a
connected structure `Γ` in `Y[𝒞]` meeting every cube of the chosen family `𝒦_Y` whose
`bondW`-cost is at most `L⁻¹ · (M⁻¹ ℓ_j⁻¹ |E₀|) + d (2L+1)^d |𝒞|`. -/
theorem gm2_tree [DecidableEq ι] (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hc : ∀ i, c i ∈ cubeIdx G) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} {E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΓ : ConnStruct W₀ E₀) (hΓX : ↑W₀ ⊆ X) (hmeet : MeetsOne m₀ j 𝒦X W₀) :
    ∃ (W : Finset (CTorus d L N₁ m₁ K)) (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W E ∧ (↑W ⊆ Ysites G m₀ c (X1 G m₀ j 𝒦X) C) ∧
        MeetsFam m₀ (KY (G := G) (m₀ := m₀) c j 𝒦X C) W ∧
        bondCost (bondW G m₀) E ≤ (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀ +
          d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  classical
  have hK : 1 ≤ K := by have := hS.hjK; omega
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  set X₁ := X1 G m₀ j 𝒦X with hX₁
  set R := Ysites G m₀ c X₁ C with hR
  set ω := bondW G m₀ with hω
  set σ₀ : ℝ := (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀ with hσ₀
  -- the cover of `Γ₀`
  have cov₀ : Covers R ω σ₀ W₀ := by
    refine ⟨W₀, E₀, hΓ, fun x hx => subset_Ysites (G := G) (m₀ := m₀) (c := c) X₁ C
      (hS.X_sub (hΓX hx)), subset_rfl, ?_⟩
    unfold bondCost
    rw [hσ₀]
    unfold bondCost
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, -⟩ := hΓ.2.1 p hp
    have h1' := X1_layer (hS.X_sub (hΓX h1))
    have h2' := X1_layer (hS.X_sub (hΓX h2))
    rw [hω, bondW_of_layer G m₀ hK le_rfl h1' h2']
    unfold scaleW cellSide
    push_cast
    rw [← mul_inv, ← pow_succ']
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hLR (by have := hS.hjK; omega)
  -- assembly along the nerve
  let σ : Option ι → ℝ := fun o => o.elim σ₀ (fun i => ((Dbases G m₀ (c i)).card : ℝ) - 1)
  have key := assemble (R := R) (ω := ω) (bondW_nonneg G m₀) (Finset.insertNone C)
    (Nerve X₁ c) none Finset.none_mem_insertNone (reach_nerve X₁ C hconn)
    (nodeSet G m₀ c W₀) σ ?_ (gm2Rho d L) ?_
  rotate_left
  · intro o ho
    cases o with
    | none => exact cov₀
    | some i =>
      exact (covers_Dbases hS.hU hS.hN (hc i)).mono_R
        (Dsites_subset_Ysites (Finset.some_mem_insertNone.1 ho))
  · intro u hu v hv h
    exact link_nerve hS hc hΓX hΓ.1 hmeet hu hv h
  obtain ⟨W, E, hconnW, hWR, hAW, hcost⟩ := key
  refine ⟨W, E, hconnW, hWR, meets_KY hS hc hmeet hAW, hcost.trans ?_⟩
  -- the cost bound
  have hsum : ∑ o ∈ Finset.insertNone C, σ o =
      σ₀ + ∑ i ∈ C, (((Dbases G m₀ (c i)).card : ℝ) - 1) := by
    rw [Finset.sum_insertNone]
    rfl
  have hcardS : ((Finset.insertNone C).card : ℝ) - 1 = C.card := by
    rw [Finset.card_insertNone]; push_cast; ring
  have hG : ∀ i ∈ C, ((Dbases G m₀ (c i)).card : ℝ) - 1 ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) - 1 := by
    intro i _
    have := card_Dbases_le (G := G) (m₀ := m₀) hS.hN (((mem_cubeIdx G).1 (hc i)).1.2)
    have : ((Dbases G m₀ (c i)).card : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hsum2 : ∑ i ∈ C, (((Dbases G m₀ (c i)).card : ℝ) - 1) ≤
      C.card * ((((2 * L + 1) ^ d : ℕ) : ℝ) - 1) := by
    calc _ ≤ ∑ _i ∈ C, ((((2 * L + 1) ^ d : ℕ) : ℝ) - 1) := Finset.sum_le_sum hG
      _ = _ := by simp; ring
  rw [hsum, hcardS]
  have ha := gm2_arith (L := L) hd hL1
  have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left ha hC0]

/-- **`d̃^cov(Y[𝒞]) ≤ L⁻¹ cost(Γ₀) + d (2L+1)^d |𝒞|`** for every connected structure `Γ₀` in `X`
meeting every cube of `𝒦_X`. -/
theorem treeLenCov_le_of_struct [DecidableEq ι] (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hc : ∀ i, c i ∈ cubeIdx G) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} {E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΓ : ConnStruct W₀ E₀) (hΓX : ↑W₀ ⊆ X) (hmeet : MeetsOne m₀ j 𝒦X W₀) :
    treeLenCov G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) ≤
      (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀ +
        d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  obtain ⟨W, E, hW1, hW2, hW3, hW4⟩ := gm2_tree hS hd hc C hconn hΓ hΓX hmeet
  have hbdd : BddBelow {x | ∃ 𝒦 W E, ChosenFamily G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) 𝒦 ∧
      ConnStruct W E ∧ (↑W ⊆ Ysites G m₀ c (X1 G m₀ j 𝒦X) C) ∧ MeetsFam m₀ 𝒦 W ∧
      x = bondCost (bondW G m₀) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    exact Finset.sum_nonneg fun p _ => bondW_nonneg G m₀ _ _
  exact (csInf_le hbdd ⟨_, W, E, chosen_KY hc, hW1, hW2, hW3, rfl⟩).trans hW4

/-- **(GM2), version 3.**  Let `𝒦_X` be a chosen family of `X` realizing `d^cov_j(X)` (i.e. some
connected structure in `X` meeting `𝒦_X` has cost `d^cov_j(X)`; such a family exists by
`treeLenCovOne_attained`), and `X₁ = ⋃ 𝒬₀`.  Then for every connected family `𝒞`,
`d̃^cov(Y[𝒞]) ≤ L⁻¹ d^cov_j(X) + d (2L+1)^d |𝒞|`; moreover `𝒦_Y` is a chosen family of `Y[𝒞]`
(`chosen_KY`). -/
theorem gm2 [DecidableEq ι] (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hc : ∀ i, c i ∈ cubeIdx G) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X) :
    treeLenCov G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) ≤
      (L : ℝ)⁻¹ * treeLenCovOne m₀ j X + d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  obtain ⟨W₀, E₀, h1, h2, h3, h4⟩ := hopt
  rw [← h4]
  exact treeLenCov_le_of_struct hS hd hc C hconn h1 h2 h3

end Main

end GM2

/-! ### Comparison with P1's tree length -/

section Compare

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- `d^cov ≤ d`: the family of all contained cubes is a chosen family of a domain `Y`
(a union of `π'_n`-cubes in each layer). -/
theorem treeLenCov_le_dTilde {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : ∀ n, 1 ≤ n → n ≤ K → ∀ z ∈ Y, z ∈ (G.layer n : Set (CTorus d L N₁ m₁ K)) →
      ∃ b, Aligned (cellSide L m₀ m₁ n) b ∧ z ∈ box b (L * cellSide L m₀ m₁ n) ∧
        box b (L * cellSide L m₀ m₁ n) ⊆ Y ∧
        box b (L * cellSide L m₀ m₁ n) ⊆ (G.layer n : Set (CTorus d L N₁ m₁ K)))
    (hne : ∃ W E, ConnStruct W E ∧ (↑W ⊆ Y) ∧ MeetsCubes G m₀ Y W) :
    treeLenCov G m₀ Y ≤ dTilde G m₀ Y := by
  have hbdd : BddBelow {x | ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧
      MeetsFam m₀ 𝒦 W ∧ x = bondCost (bondW G m₀) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    exact Finset.sum_nonneg fun p _ => bondW_nonneg G m₀ _ _
  obtain ⟨W₁, E₁, h1, h2, h3⟩ := hne
  refine le_csInf ⟨_, W₁, E₁, h1, h2, h3, rfl⟩ ?_
  rintro x ⟨W, E, hW1, hW2, hW3, rfl⟩
  refine csInf_le hbdd ⟨fun n => {b | Aligned (cellSide L m₀ m₁ n) b ∧
    box b (L * cellSide L m₀ m₁ n) ⊆ Y ∧
    box b (L * cellSide L m₀ m₁ n) ⊆ (G.layer n : Set (CTorus d L N₁ m₁ K))}, W, E, ?_, hW1, hW2, ?_,
    rfl⟩
  · intro n hn1 hnK
    refine ⟨fun b hb => hb, fun z hz hzn => ?_⟩
    obtain ⟨b, hb1, hzb, hb2, hb3⟩ := hY n hn1 hnK z hz hzn
    exact ⟨b, ⟨hb1, hb2, hb3⟩, hzb⟩
  · intro n hn1 hnK b hb
    exact hW3 n hn1 hnK b hb.1 hb.2.1 hb.2.2

end Compare

end Balaban.Localization
