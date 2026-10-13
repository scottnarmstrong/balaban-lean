/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6ActiveHalo
public import Balaban.Localization.MooreDegree
public import Balaban.Polymer.RootedAnimals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Counting patch families rooted at active cells for `F♯` (VMOD-33 §4, packages (4) and (5))

For the multiscale auxiliary cover `F♯ = p6FsharpC` of the P6 pair, a set of patches (vertices of
its Moore graph `mooreGraph`) is *rooted at* a set `A` of active top cells when every Moore
component of it contains a patch that Moore-touches the top cell of some `u ∈ A`.

* `fsharpRootNbhd`: the patches of `F♯` Moore-touching the top cell of `u`.
* `card_fsharpRootNbhd_le`, `layer_eq_of_mem_fsharpRootNbhd`: for an active `u` there are at most
  `3^d (L^m₀)^d` of them, and all have the top layer `k + 1`.
* `fsharp_rooted_sum_le`, `mem_rootedSets_fsharp_iff`, `fsharp_rooted_sum_le_of_rootCount`,
  `fsharp_rooted_fixed_support_sum_le`: the rooted sum
  `Σ_C t^|C| ≤ (1 / (1 - D² t))^|A|`, `D = max (3 (L+4)^d + 1) (3^d (L^m₀)^d)`, its
  characterization of rootedness and its exponential form.
* `walkIn_layer_le`, `rooted_layer_depth_le_card`: a member of a rooted set in layer `j` forces the
  set to have at least `k + 1 - j + 1` members (the layer changes by at most one along every edge).
* `fsharp_layer_tail_le`: for one active cell, the sum of `t^|C|` over rooted sets containing a
  patch of layer `j` is at most `z^(k + 1 - j + 1) / (1 - z)`, `z = D² t`.

**Counting only.**  That a non-zero coefficient of the actual P6 interpolation has all its
components rooted at active cells (`OPEN-P6-ACTIVE-COEF-ROOT`) is not proved here and is the subject
of a question to the author; neither are the count `|A_X| ≤ c_A (1 + Δ_X)`, the region casts that
make the cells of `X ∩ Ω_K` active (`OPEN-P6-ACTIVE-REGION-CAST`), or the H7 transfer.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Polymer

set_option linter.unusedSectionVars false

section Defs

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

open Classical in
/-- The patches (indices of `cubeIdx F♯`, as vertices of the Moore graph) whose parameter patch
Moore-touches the top cell of side `L^m₀ M₁ L^(k+1)` of the cover-torus cell `u`. -/
noncomputable def fsharpRootNbhd (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (m₀ : ℕ)
    (u : Localization.CTorus d L (c * n1) m₁ (k + 1)) :
    Finset {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)} :=
  (cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)).attach.filter
    fun P => MooreTouch (topCell m₀ (k + 1, u)) (Pset m₁ P.1)

theorem mem_fsharpRootNbhd (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (m₀ : ℕ)
    (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    {P : {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)}} :
    P ∈ fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc Z hM1 m₀ u ↔
      MooreTouch (topCell m₀ (k + 1, u)) (Pset m₁ P.1) := by
  classical
  simp [fsharpRootNbhd]

/-- The constant `D = max (3 (L+4)^d + 1) (3^d (L^m₀)^d)` (the same as `topD`). -/
def fsharpD (d L m₀ : ℕ) : ℕ := max (3 * (L + 4) ^ d + 1) (3 ^ d * (L ^ m₀) ^ d)

end Defs

section Count

variable {d M1 c n1 L k n0 m₁ m₀ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk) {ρ' : ℕ}

/-- **T1.**  For an active top cell `u` (hypotheses of `p6_root_patch_count`), the root
neighbourhood has at most `3^d (L^m₀)^d` patches. -/
theorem card_fsharpRootNbhd_le (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c)
    (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hu : LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega) :
    (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u).card ≤ 3 ^ d * (L ^ m₀) ^ d := by
  classical
  refine le_trans ?_ (p6_root_patch_count st hM1 hmc hn hL hρ hc u hu)
  refine Finset.card_le_card_of_injOn (fun P => P.1) (fun P hP => ?_) (fun P _ Q _ h => ?_)
  · rw [Finset.mem_coe, mem_fsharpRootNbhd] at hP
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨P.2, hP⟩)
  · exact Subtype.ext h

/-- **T1, layer.**  Every patch of the root neighbourhood of an active cell has the top layer. -/
theorem layer_eq_of_mem_fsharpRootNbhd (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c)
    (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hu : LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {P : {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)}}
    (hP : P ∈ fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u) : P.1.1 = k + 1 :=
  p6_touch_active_layer st hM1 hmc hn hL hρ hc u hu P.2 ((mem_fsharpRootNbhd _ _ _ _ _ _ _).1 hP)

open Classical in
/-- **T2 (2.2).**  For a finite set `A` of active top cells,
`Σ_{C rooted at the root neighbourhoods of A} t^|C| ≤ (1 / (1 - D² t))^|A|`. -/
theorem fsharp_rooted_sum_le (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (hA : ∀ u ∈ A, LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {t : ℝ} (ht : 0 ≤ t) (hz : ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (⋃ u ∈ A, (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Set _)),
        t ^ C.card
      ≤ (1 / (1 - ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * t)) ^ A.card := by
  have hG : CubeAligned (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1) m₁ :=
    GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned (M1 := M1) (c := c) (k := k)
      hn hρ hc st.Z hM1 hm₁)
  have key := sum_rooted_le (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
    (b := 3 * (L + 4) ^ d) (b_root := 3 ^ d * (L ^ m₀) ^ d)
    (fun P => mooreGraph_degree_le hG (p6_moore_premise hd) P)
    (fun u : {u // u ∈ A} => fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u.1)
    (fun u => card_fsharpRootNbhd_le st hM1 hmc hn hL hρ hc u.1 (hA u.1 u.2)) ht hz A.attach
  have hU : ((⋃ i ∈ A.attach, ((fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ i.1 : Finset _) : Set _)) : Set {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)})
      = ⋃ u ∈ A, ((fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Finset _) : Set _) := by
    ext x; simp
  rw [hU, Finset.card_attach] at key
  exact key

open Classical in
/-- **T2, characterization.**  A set of patches is rooted at the root neighbourhoods of `A` iff
every patch of it is joined, by a walk of the Moore graph inside the set, to a patch touching the top
cell of some `u ∈ A` (every Moore component touches `A`). -/
theorem mem_rootedSets_fsharp_iff (hn : n0 = L * n1) (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁)
    (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (C : Finset {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)}) :
    C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1))
        (⋃ u ∈ A, (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc Z hM1 m₀ u : Set _)) ↔
      ∀ v ∈ C, ∃ w, WalkIn (mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)) C v w ∧
        ∃ u ∈ A, MooreTouch (topCell m₀ (k + 1, u)) (Pset m₁ w.1) := by
  rw [mem_rootedSets]
  refine forall₂_congr fun v hv => ?_
  constructor
  · rintro ⟨w, hw, h⟩
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop] at hw
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨w, h, u, hu, (mem_fsharpRootNbhd _ _ _ _ _ _ _).1 hwu⟩
  · rintro ⟨w, h, u, hu, ht⟩
    refine ⟨w, ?_, h⟩
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    exact ⟨u, hu, (mem_fsharpRootNbhd _ _ _ _ _ _ _).2 ht⟩

open Classical in
/-- **T2, exponential form.**  With `t = exp (-κ₂)`, `z = D² t < 1`, `h = -log (1 - z)`: if
`|A| ≤ c_A (1 + Δ)` then the rooted sum is at most `exp (h c_A) exp (h c_A Δ)`. -/
theorem fsharp_rooted_sum_le_of_rootCount (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c)
    (hn : n0 = L * n1) (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁)
    (hd : d < 5 * L ^ 3 * M1) (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (hA : ∀ u ∈ A, LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {κ₂ Δ c_A : ℝ} (hz : ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (A.card : ℝ) ≤ c_A * (1 + Δ)) :
    ∑ C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (⋃ u ∈ A, (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Set _)),
        Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A) *
        Real.exp (-Real.log (1 - ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A * Δ) := by
  set z : ℝ := ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hpos : 0 < 1 - z := by linarith
  set h : ℝ := -Real.log (1 - z) with hh
  have hh0 : 0 ≤ h := by
    have : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have hsum := fsharp_rooted_sum_le st hM1 hmc hn hL hρ hc hm₁ hd A hA (Real.exp_pos (-κ₂)).le hz
  have hterm : ∀ C : Finset {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)},
      Real.exp (-κ₂ * C.card) = Real.exp (-κ₂) ^ C.card := fun C => by
    rw [← Real.exp_nat_mul]; ring_nf
  simp only [hterm]
  refine hsum.trans ?_
  have : 1 / (1 - z) = Real.exp h := by
    rw [hh, Real.exp_neg, Real.exp_log hpos, one_div]
  rw [this, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hR hh0]

open Classical in
/-- **T2, fixed support.**  For any map `supp` from patch sets to supports and any support `S`, the
sum over the rooted sets with `supp C = S` obeys the same bound. -/
theorem fsharp_rooted_fixed_support_sum_le {S₀ : Type*} [DecidableEq S₀]
    (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c)
    (hn : n0 = L * n1) (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁)
    (hd : d < 5 * L ^ 3 * M1) (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (hA : ∀ u ∈ A, LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {κ₂ Δ c_A : ℝ} (hz : ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (A.card : ℝ) ≤ c_A * (1 + Δ))
    (supp : Finset {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)} → S₀)
    (S : S₀) :
    ∑ C ∈ (rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (⋃ u ∈ A, (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Set _))).filter
          (fun C => supp C = S), Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A) *
        Real.exp (-Real.log (1 - ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A * Δ) :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => (Real.exp_pos _).le))
    (fsharp_rooted_sum_le_of_rootCount st hM1 hmc hn hL hρ hc hm₁ hd A hA hz hR)

end Count

section Layers

/-- **T3, generic.**  If a function `f` on the vertices of `G` grows by at most one along every
edge, then along a walk inside `C` from `v` to `w`, `f w + 1 ≤ f v + |C|`. -/
theorem walkIn_layer_le {V : Type*} {G : SimpleGraph V} [DecidableEq V] (f : V → ℕ)
    (hf : ∀ v w, G.Adj v w → f w ≤ f v + 1) {C : Finset V} {v w : V} (h : WalkIn G C v w) :
    f w + 1 ≤ f v + C.card := by
  obtain ⟨p, hp⟩ := h
  have hlen : ∀ {a b : V} (q : G.Walk a b), f b ≤ f a + q.length := by
    intro a b q
    induction q with
    | nil => simp
    | cons hadj q ih => simp only [SimpleGraph.Walk.length_cons]; have := hf _ _ hadj; omega
  set q := p.bypass with hq
  have hqp : q.IsPath := SimpleGraph.Walk.bypass_isPath p
  have hsub : ∀ x ∈ q.support, x ∈ C := fun x hx =>
    hp x (SimpleGraph.Walk.support_bypass_subset_support p hx)
  have hcard : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hqp.support_nodup, SimpleGraph.Walk.length_support]
  have : q.support.toFinset.card ≤ C.card :=
    Finset.card_le_card fun x hx => hsub x (List.mem_toFinset.1 hx)
  have := hlen q
  omega

variable {d M1 c n1 L k n0 m₁ m₀ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk) {ρ' : ℕ}

open Classical in
/-- **T3.**  Let `C` be a set of patches of `F♯` rooted at the root neighbourhoods of active cells.
Every member `P` of `C` satisfies `k + 1 - P.layer + 1 ≤ |C|`. -/
theorem rooted_layer_depth_le_card (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (hA : ∀ u ∈ A, LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {C : Finset {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)}}
    (hC : C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (⋃ u ∈ A, (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Set _)))
    {P : {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)}} (hP : P ∈ C) :
    k + 1 - P.1.1 + 1 ≤ C.card := by
  rw [mem_rootedSets] at hC
  obtain ⟨w, hw, hwalk⟩ := hC P hP
  simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop] at hw
  obtain ⟨u, hu, hwu⟩ := hw
  have hwl := layer_eq_of_mem_fsharpRootNbhd st hM1 hmc hn hL hρ hc u (hA u hu) hwu
  have h2 := walkIn_layer_le (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
    (fun P => P.1.1) (fun v w hvw => by
      have := cubeIdx_moore_layer_gap_p6 (m₁ := m₁) hn hρ hc st.Z hM1 hm₁ hd v.2 w.2 hvw.2
      exact this.2) hwalk
  have h3 : w.1.1 + 1 ≤ P.1.1 + C.card := h2
  have h4 : 0 < C.card := Finset.card_pos.2 ⟨P, hP⟩
  omega

open Classical in
/-- **T4 (2.3).**  For one active top cell `u`, a layer `j` and `t ≥ 0` with `z = D² t < 1`:
`Σ t^|C| ≤ z^(k + 1 - j + 1) / (1 - z)`, the sum over the sets `C` rooted at the root neighbourhood
of `u` that contain a patch of layer `j`. -/
theorem fsharp_layer_tail_le (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hu : LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega) (j : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (hz : ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ (rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Set _)).filter
          (fun C => ∃ P ∈ C, P.1.1 = j), t ^ C.card
      ≤ (((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * t) ^ (k + 1 - j + 1) /
          (1 - ((fsharpD d L m₀ : ℕ) : ℝ) ^ 2 * t) := by
  have hG : CubeAligned (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1) m₁ :=
    GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned (M1 := M1) (c := c) (k := k)
      hn hρ hc st.Z hM1 hm₁)
  have hb : ∀ v, (mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)).degree v
      ≤ 3 * (L + 4) ^ d := fun P => mooreGraph_degree_le hG (p6_moore_premise hd) P
  have hN := card_fsharpRootNbhd_le st hM1 hmc hn hL hρ hc u hu
  set Δ : ℕ := fsharpD d L m₀ with hΔ
  have hΔ' : Δ = max (3 * (L + 4) ^ d + 1) (3 ^ d * (L ^ m₀) ^ d) := rfl
  set z : ℝ := (Δ : ℝ) ^ 2 * t with hzdef
  have hz0 : 0 ≤ z := by positivity
  set m := k + 1 - j + 1 with hm
  set S := (rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u : Set _)).filter
          (fun C => ∃ P ∈ C, P.1.1 = j) with hS
  have hmaps : ∀ C ∈ S, C.card ∈ Finset.Ico m (Fintype.card {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)} + 1) := by
    intro C hC
    rw [hS, Finset.mem_filter] at hC
    obtain ⟨hr, P, hPC, hPj⟩ := hC
    have hr' : C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (⋃ u' ∈ ({u} : Finset _), (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u' :
          Set _)) := by simpa using hr
    have := rooted_layer_depth_le_card st hM1 hmc hn hL hρ hc hm₁ hd {u}
      (by simpa using hu) hr' hPC
    rw [hPj] at this
    rw [Finset.mem_Ico]
    exact ⟨this, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ n ∈ Finset.Ico m (Fintype.card {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)} + 1),
      ∑ C ∈ S.filter (fun C => C.card = n), t ^ C.card ≤ z ^ n := by
    intro n _
    rw [Finset.sum_congr rfl (g := fun _ => t ^ n) (fun C hC => by
      rw [(Finset.mem_filter.1 hC).2]), Finset.sum_const, nsmul_eq_mul]
    have hcnt : (S.filter (fun C => C.card = n)).card ≤ Δ ^ (2 * n) := by
      refine le_trans (Finset.card_le_card ?_)
        (card_rooted_le hb (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u) hN n)
      intro C hC
      rw [Finset.mem_filter] at hC ⊢
      exact ⟨(Finset.mem_filter.1 hC.1).1, hC.2⟩
    calc _ ≤ ((Δ ^ (2 * n) : ℕ) : ℝ) * t ^ n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcnt
      _ = z ^ n := by rw [hzdef, mul_pow, ← pow_mul]; push_cast; ring
  have hgeo : HasSum (fun n : ℕ => z ^ m * z ^ n) (z ^ m * (1 - z)⁻¹) :=
    (hasSum_geometric_of_lt_one hz0 hz).mul_left _
  calc _ ≤ ∑ n ∈ Finset.Ico m (Fintype.card {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)} + 1), z ^ n := Finset.sum_le_sum hfib
    _ = ∑ i ∈ Finset.range (Fintype.card {P // P ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)} + 1 - m), z ^ m * z ^ i := by
        rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
    _ ≤ z ^ m * (1 - z)⁻¹ := sum_le_hasSum _ (fun i _ => by positivity) hgeo
    _ = z ^ m / (1 - z) := by rw [div_eq_mul_inv]

end Layers

end Balaban.LargeField
