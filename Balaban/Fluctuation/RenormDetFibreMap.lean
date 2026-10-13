/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormLocFibre
public import Balaban.Fluctuation.HatLabelsExpansion
public import Balaban.Fluctuation.Prop33Level
public import Balaban.Fluctuation.DetCauchyHull
public import Balaban.Fluctuation.SizeModG1
public import Balaban.SmallField.Def6BridgeGeom
public import Balaban.Inhabited.V2Energy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From polymers to the renormalization cover: the fibre map of the determinant terms

The determinant terms of a step are indexed by polymers `X` (connected unions of cubes of side
`L a_K`, `a_K = cellSide L m₀ m₁ K`) that contain the root neighbourhood.  The renormalization
record needs terms indexed by `renYs`, the finsets `Y[𝒞]` of the connected families `𝒞` of labels
(parameter cubes of side `s = L ^ (K + m₁)` disjoint from the root neighbourhood `X₁`).

For a level generating set (`IsLevel G K`: every site lies in the layer `K`) this file defines

* `renLabelFam G X₁ X`: the labels whose parameter cube meets `X`;
* `renFibreMap G m₀ X₁ X`: the finset `Y[𝒞]` of that family.

and proves, for `X₁ = X1 G m₀ j 𝒦X` the root neighbourhood of a `CovSetup`:

* `renFibreMap_mem_renYs`: for a polymer `X` meeting `X₁`, the family is connected for the
  connectivity of `renYs` (`IsConnectedFamily`: each parameter cube lies in the component of
  `X₁ ∪ ⋃ parameter cubes` containing `X₁`), so `renFibreMap X ∈ renYs`;
* `subset_renFibreMap`: `X ⊆ renFibreMap X`;
* `renDY_renFibreMap_le`: `renDY (renFibreMap X) ≤ A sizeJ X + A`;
* `card_renFibre_le`: the number of such polymers with a given image `Y` is at most
  `2 ^ c₁ exp (c₁ log 2 · renDY Y)`;
* `regroup_norm_le` (abstract) and `renRegroup_norm_le`, `sum_renRegroup`: the regrouped bound
  and the sum identity.

Nothing here concerns the chart of the determinant or the analytic dependence of the terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.SmallField
  Balaban.SmallField.Def6 Finset

section Labels

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) (X₁ : Set (CTorus d L N₁ m₁ K))

open Classical in
/-- **The label family of a set of sites**: the labels whose parameter cube meets `X`. -/
noncomputable def renLabelFam (X : Set (CTorus d L N₁ m₁ K)) : Finset (RenLabel G X₁) :=
  Finset.univ.filter fun i => (Pset m₁ (renCube G X₁ i) ∩ X).Nonempty

/-- **The fibre map `Φ`**: the domain `Y[𝒞]` of the family of labels met by `X`, as a finset
of sites. -/
noncomputable def renFibreMap (X : Set (CTorus d L N₁ m₁ K)) : Finset (CTorus d L N₁ m₁ K) :=
  finOf (Ysites G m₀ (renCube G X₁) X₁ (renLabelFam G X₁ X))

variable {G m₀ X₁}

theorem mem_renLabelFam {X : Set (CTorus d L N₁ m₁ K)} {i : RenLabel G X₁} :
    i ∈ renLabelFam G X₁ X ↔ (Pset m₁ (renCube G X₁ i) ∩ X).Nonempty := by
  classical
  simp [renLabelFam]

theorem coe_renFibreMap (X : Set (CTorus d L N₁ m₁ K)) :
    (↑(renFibreMap G m₀ X₁ X) : Set (CTorus d L N₁ m₁ K)) =
      Ysites G m₀ (renCube G X₁) X₁ (renLabelFam G X₁ X) :=
  coe_finOf _

/-- Cells of a union of cubes lie in it. -/
theorem cell_subset_of_isDj (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) {y : CTorus d L N₁ m₁ K} (hy : y ∈ X) :
    box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆ X := by
  obtain ⟨b, hb1, hb2, hb3⟩ := hX.2.1 y hy
  exact (cell_subset_cube (cellSide_dvd (K := K) (m₁ := m₁) hN hj) (cellSide_pos m₀ m₁ j) hb1
    hb2).trans hb3

/-- The root neighbourhood `X1` is a union of cells. -/
theorem cell_subset_X1 {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ K)} (hN : L ^ m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ X1 G m₀ j 𝒦X) :
    box (cbase (cellSide L m₀ m₁ K) y) (cellSide L m₀ m₁ K) ⊆ X1 G m₀ j 𝒦X := by
  obtain ⟨b, hb1, hb2, hb3⟩ := X1_cubes y hy
  exact (cell_subset_cube (cellSide_dvd (K := K) (m₁ := m₁) hN le_rfl) (cellSide_pos m₀ m₁ K) hb1
    hb2).trans hb3

omit [NeZero L] in
theorem pset_cell_dvd (m₀ : ℕ) :
    L ^ (K + m₁) ∣ cellSide L m₀ m₁ K := by
  unfold cellSide; exact pow_dvd_pow L (by omega)

/-- A site outside `X₁` lies in the parameter cube of a label. -/
theorem exists_label_of_notMem {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ K)} (hG : IsLevel G K)
    (hN : L ^ m₀ ∣ N₁) {x : CTorus d L N₁ m₁ K} (hx : x ∉ X1 G m₀ j 𝒦X) :
    ∃ i : RenLabel G (X1 G m₀ j 𝒦X), x ∈ Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i) := by
  classical
  set s := L ^ (K + m₁) with hs
  have hs0 : 0 < s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcb : ∀ y : CTorus d L N₁ m₁ K, ∀ μ, ((cbase s y) μ).val / s = (y μ).val / s := by
    intro y μ
    rw [cbase_val, Nat.mul_div_cancel_left _ hs0]
  have hq : ((K, cbase s x) : ℕ × CTorus d L N₁ m₁ K) ∈ cubeIdx G := by
    rw [mem_cubeIdx]
    exact ⟨⟨hG.bounds.1, le_rfl⟩, hG.mem_layer _, aligned_cbase x⟩
  have hxP : x ∈ Pset m₁ ((K, cbase s x) : ℕ × CTorus d L N₁ m₁ K) := fun μ => (hcb x μ).symm
  refine ⟨⟨(K, cbase s x), hq, ?_⟩, hxP⟩
  rw [Set.disjoint_left]
  intro y hy hyX
  have hxy : ∀ μ, (x μ).val / cellSide L m₀ m₁ K = (y μ).val / cellSide L m₀ m₁ K := by
    have h1 : SameCell s x y := fun μ => (hxP μ).trans (hy μ).symm
    exact SameCell.mono (pset_cell_dvd (K := K) (m₁ := m₁) m₀) h1
  have hxbox : x ∈ box (cbase (cellSide L m₀ m₁ K) y) (cellSide L m₀ m₁ K) :=
    mem_box_cbase_of_sameCell (cellSide_pos m₀ m₁ K) hxy
  exact hx (cell_subset_X1 hN hyX hxbox)

end Labels

section Connected

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- A nearest-neighbour path inside `S ⊆ V` is a path of the lattice graph inside `V`. -/
theorem rtg_adj_of_nbr {n : ℕ} {S V : Set (Torus d n)} (hSV : S ⊆ V) {x y : Torus d n}
    (h : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Nbr a b) x y) :
    Relation.ReflTransGen (fun a b => (latGraph d n).Adj a b ∧ a ∈ V ∧ b ∈ V) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    by_cases hbc' : b = c
    · subst hbc'; exact ih
    · exact ih.tail ⟨⟨hbc', hbc.2.2⟩, hSV hbc.1, hSV hbc.2.1⟩

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ} {Xr 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **T1 (i): the family of labels met by a polymer is connected.**  If `X` is a polymer
(`IsPolyDom m₀ K X`) meeting `X₁ = X1 G m₀ j 𝒦X`, each parameter cube of the family lies in the
component of `X₁ ∪ ⋃ parameter cubes` containing `X₁` (the connectivity of `renYs`). -/
theorem renLabelFam_connected (hG : IsLevel G K) (hN : L ^ m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ K X)
    (hx0 : ∃ x ∈ X, x ∈ X1 G m₀ j 𝒦X) :
    IsConnectedFamily (fun i => Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i))
      (compY (renCube G (X1 G m₀ j 𝒦X)) (X1 G m₀ j 𝒦X))
      (renLabelFam G (X1 G m₀ j 𝒦X) X) := by
  classical
  obtain ⟨x0, hx0X, hx0X1⟩ := hx0
  set C := renLabelFam G (X1 G m₀ j 𝒦X) X with hC
  set V := patchUnion (X1 G m₀ j 𝒦X) (fun i => Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i)) C with hV
  have hXV : X ⊆ V := by
    intro x hx
    by_cases hx1 : x ∈ X1 G m₀ j 𝒦X
    · exact Or.inl hx1
    · obtain ⟨i, hi⟩ := exists_label_of_notMem (m₀ := m₀) hG hN hx1
      exact Or.inr (Set.mem_iUnion₂.2 ⟨i, mem_renLabelFam.2 ⟨x, hi, hx⟩, hi⟩)
  intro i hi y hy
  have hPV : Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i) ⊆ V := fun z hz =>
    Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hz⟩)
  have hy : y ∈ Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i) := hy
  obtain ⟨x, hxP, hxX⟩ := mem_renLabelFam.1 hi
  have hP1 : (renCube G (X1 G m₀ j 𝒦X) i).1 ≤ K := (mem_cubeIdx G).1 (renCube_mem _ _ i) |>.1.2
  have hbox := Pset_eq_box (m₀ := m₀) hN hP1
  have hp1 := hX.2.2 x0 hx0X x hxX
  have hp2 : Relation.ReflTransGen (fun a b => a ∈ Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i) ∧
      b ∈ Pset m₁ (renCube G (X1 G m₀ j 𝒦X) i) ∧ Nbr a b) x y := by
    rw [hbox] at hxP hy ⊢
    exact siteConnected_box_aux _ _ x hxP y hy
  exact ⟨x0, hx0X1, (rtg_adj_of_nbr hXV hp1).trans (rtg_adj_of_nbr hPV hp2)⟩

/-- **T1 (i): `Φ(X) ∈ renYs`.** -/
theorem renFibreMap_mem_renYs (hS : CovSetup G m₀ j Xr 𝒦X) (hG : IsLevel G K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ K X)
    (hx0 : ∃ x ∈ X, x ∈ X1 G m₀ j 𝒦X) :
    renFibreMap G m₀ (X1 G m₀ j 𝒦X) X ∈
      renYs (renCube G (X1 G m₀ j 𝒦X)) G m₀ (X1 G m₀ j 𝒦X) := by
  classical
  rw [mem_renYs, coe_renFibreMap]
  unfold polymerDomains
  rw [Finset.mem_image]
  exact ⟨renLabelFam G (X1 G m₀ j 𝒦X) X,
    Finset.mem_filter.2 ⟨Finset.mem_univ _, renLabelFam_connected hG hS.hN hX hx0⟩, rfl⟩

/-- **T1 (ii): `X ⊆ Φ(X)`.** -/
theorem subset_renFibreMap (hS : CovSetup G m₀ j Xr 𝒦X) (hG : IsLevel G K)
    {X : Set (CTorus d L N₁ m₁ K)} :
    X ⊆ ↑(renFibreMap G m₀ (X1 G m₀ j 𝒦X) X) := by
  intro x hx
  rw [coe_renFibreMap]
  by_cases hx1 : x ∈ X1 G m₀ j 𝒦X
  · exact Or.inl hx1
  · obtain ⟨i, hi⟩ := exists_label_of_notMem (m₀ := m₀) hG hS.hN hx1
    exact Or.inr (Set.mem_iUnion₂.2 ⟨i, mem_renLabelFam.2 ⟨x, hi, hx⟩,
      Pset_subset_Dsites hS.hU hS.hN (renCube_mem _ _ i) hi⟩)

end Connected

section Size

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ} {Xr 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- Every label of a level generating set has layer `K`. -/
theorem renCube_fst (hG : IsLevel G K) (X₁ : Set (CTorus d L N₁ m₁ K)) (i : RenLabel G X₁) :
    (renCube G X₁ i).1 = K := by
  obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_cubeIdx G).1 (renCube_mem G X₁ i)
  by_contra hne
  exact G.layer_disjoint h1 hK hG.bounds.1 hG.bounds.2 hne hl (hG.mem_layer _)

/-- Distinct labels have disjoint parameter cubes. -/
theorem renLabel_pset_disjoint (hG : IsLevel G K) {X₁ : Set (CTorus d L N₁ m₁ K)}
    {i i' : RenLabel G X₁} (h : i ≠ i') :
    Disjoint (Pset m₁ (renCube G X₁ i)) (Pset m₁ (renCube G X₁ i')) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  apply renCube_injective G X₁
  have e1 := renCube_fst hG X₁ i
  have e2 := renCube_fst hG X₁ i'
  have hs0 : 0 < L ^ (K + m₁) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hb1 := (mem_cubeIdx G).1 (renCube_mem G X₁ i) |>.2.2
  have hb2 := (mem_cubeIdx G).1 (renCube_mem G X₁ i') |>.2.2
  have hx1 : ∀ μ, (x μ).val / L ^ (K + m₁) = ((renCube G X₁ i).2 μ).val / L ^ (K + m₁) := by
    intro μ; have := hx μ; rwa [e1] at this
  have hx2 : ∀ μ, (x μ).val / L ^ (K + m₁) = ((renCube G X₁ i').2 μ).val / L ^ (K + m₁) := by
    intro μ; have := hx' μ; rwa [e2] at this
  refine Prod.ext (e1.trans e2.symm) ?_
  funext μ
  apply ZMod.val_injective
  have a1 := hb1 μ
  have a2 := hb2 μ
  rw [e1] at a1
  rw [e2] at a2
  have d1 := Nat.div_add_mod ((renCube G X₁ i).2 μ).val (L ^ (K + m₁))
  have d2 := Nat.div_add_mod ((renCube G X₁ i').2 μ).val (L ^ (K + m₁))
  rw [a1] at d1
  rw [a2] at d2
  have := (hx1 μ).symm.trans (hx2 μ)
  show ((renCube G X₁ i).2 μ).val = ((renCube G X₁ i').2 μ).val
  rw [← d1, ← d2, this]

/-- A parameter cube meeting a union of cubes lies in it. -/
theorem pset_subset_of_meets (hN : L ^ m₀ ∣ N₁) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ K X) (hG : IsLevel G K) {X₁ : Set (CTorus d L N₁ m₁ K)}
    {i : RenLabel G X₁} (hi : (Pset m₁ (renCube G X₁ i) ∩ X).Nonempty) :
    Pset m₁ (renCube G X₁ i) ⊆ X := by
  obtain ⟨y, hy, hyX⟩ := hi
  intro z hz
  have e1 := renCube_fst hG X₁ i
  have h1 : ∀ μ, (z μ).val / L ^ (K + m₁) = (y μ).val / L ^ (K + m₁) := by
    intro μ; have a := hz μ; have b := hy μ; rw [e1] at a b; exact a.trans b.symm
  have h2 : SameCell (L ^ (K + m₁)) z y := h1
  have h3 := SameCell.mono (pset_cell_dvd (K := K) (m₁ := m₁) m₀) h2
  exact cell_subset_of_isDj hN le_rfl hX hyX (mem_box_cbase_of_sameCell (cellSide_pos m₀ m₁ K) h3)

/-- Counting the labels met by a union of cubes by sites: `|𝒞| s^d ≤ |X|`. -/
theorem card_renLabelFam_mul_le (hG : IsLevel G K) (hN : L ^ m₀ ∣ N₁)
    {X₁ X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ K X) :
    ((renLabelFam G X₁ X).card : ℝ) * (((L ^ (K + m₁) : ℕ) : ℝ)) ^ d ≤ X.ncard := by
  classical
  set C := renLabelFam G X₁ X with hC
  set T : RenLabel G X₁ → Finset (CTorus d L N₁ m₁ K) :=
    fun i => Finset.univ.filter (· ∈ Pset m₁ (renCube G X₁ i)) with hT
  have hn : (L ^ (K + m₁)) ≤ (N₁ * L ^ m₁) * L ^ K := by
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (Dvd.intro_left N₁ ?_)
    ring
  have hTc : ∀ i, (L ^ (K + m₁)) ^ d ≤ (T i).card := by
    intro i
    have e1 := renCube_fst hG X₁ i
    have hP1 : (renCube G X₁ i).1 ≤ K := e1.le
    have hb := Pset_eq_box (m₀ := m₀) hN hP1
    have h1 := Balaban.SmallField.Def6v2.ncard_box_ge (d := d) (n := (N₁ * L ^ m₁) * L ^ K)
      (cbase (L ^ ((renCube G X₁ i).1 + m₁)) (renCube G X₁ i).2)
      (L ^ ((renCube G X₁ i).1 + m₁))
    rw [← hb, e1, min_eq_left hn] at h1
    have : (Pset m₁ (renCube G X₁ i)).ncard = (T i).card := by
      rw [Set.ncard_eq_toFinset_card' (Pset m₁ (renCube G X₁ i))]
      congr 1; ext; simp [hT]
    rwa [this] at h1
  have hdisj : ∀ i ∈ C, ∀ i' ∈ C, i ≠ i' → Disjoint (T i) (T i') := by
    intro i _ i' _ h
    rw [Finset.disjoint_left]
    intro x hx hx'
    have := Set.disjoint_left.1 (renLabel_pset_disjoint hG h)
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact this hx hx'
  have hsub : C.biUnion T ⊆ Finset.univ.filter (· ∈ X) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hxi ⊢
    exact pset_subset_of_meets hN hX hG (mem_renLabelFam.1 hi) hxi
  have h1 : C.card * (L ^ (K + m₁)) ^ d ≤ X.ncard := by
    have e : X.ncard = (Finset.univ.filter (· ∈ X)).card := by
      rw [Set.ncard_eq_toFinset_card' X]; congr 1; ext; simp
    rw [e]
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_biUnion hdisj]
    calc C.card * (L ^ (K + m₁)) ^ d = ∑ _i ∈ C, (L ^ (K + m₁)) ^ d := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hTc i
  exact_mod_cast h1

/-- The constant of the size comparison: `A = d (2L+1)^d · c₁ · (L^{m₀})^d`. -/
noncomputable def renDetA (d L m₀ : ℕ) : ℝ :=
  d * (((2 * L + 1) ^ d : ℕ) : ℝ) * (c1 d L * (((L ^ m₀) ^ d : ℕ) : ℝ))

theorem renDetA_pos (d L m₀ : ℕ) [NeZero L] (hd : 3 ≤ d) : 0 < renDetA d L m₀ := by
  have h1 := one_le_c1 d L
  have h2 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h3 : (0 : ℝ) < (((2 * L + 1) ^ d : ℕ) : ℝ) := by positivity
  have h4 : (0 : ℝ) < (((L ^ m₀) ^ d : ℕ) : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold renDetA
  positivity

/-- **T2: the size comparison.**  For a polymer `X` meeting the root neighbourhood,
`renDY (Φ X) ≤ A · sizeJ X + A`, `A = d (2L+1)^d c₁ (L^{m₀})^d`. -/
theorem renDY_renFibreMap_le (hS : CovSetup G m₀ j Xr 𝒦X) (hG : IsLevel G K) (hd : 3 ≤ d)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ Xr) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j Xr)
    (hΔ : treeLenCovOne m₀ j Xr = 0)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ K X)
    (hx0 : ∃ x ∈ X, x ∈ X1 G m₀ j 𝒦X) :
    renDY G m₀ (renFibreMap G m₀ (X1 G m₀ j 𝒦X) X) ≤
      renDetA d L m₀ * sizeJ m₀ K X + renDetA d L m₀ := by
  classical
  have hXdj := isDj_of_isPolyDom hX
  have hconn := renLabelFam_connected (j := j) (𝒦X := 𝒦X) hG hS.hN hX hx0
  have h2 := gm2 hS hd (fun i => renCube_mem G (X1 G m₀ j 𝒦X) i)
    (renLabelFam G (X1 G m₀ j 𝒦X) X) hconn hopt
  rw [hΔ, mul_zero, zero_add] at h2
  have h3 : renDY G m₀ (renFibreMap G m₀ (X1 G m₀ j 𝒦X) X) ≤
      d * (((2 * L + 1) ^ d : ℕ) : ℝ) * (renLabelFam G (X1 G m₀ j 𝒦X) X).card := by
    unfold renDY
    rw [coe_renFibreMap]
    exact h2
  -- the count of labels
  have hcount := card_renLabelFam_mul_le (X₁ := X1 G m₀ j 𝒦X) hG hS.hN hXdj
  have hG1 := G1_card hS.hN (le_refl K) hXdj
  have hs0 : (0 : ℝ) < (((L ^ (K + m₁) : ℕ) : ℝ)) ^ d := by
    have := Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hcs : ((cellSide L m₀ m₁ K : ℕ) : ℝ) ^ d =
      (((L ^ m₀) ^ d : ℕ) : ℝ) * (((L ^ (K + m₁) : ℕ) : ℝ)) ^ d := by
    unfold cellSide
    push_cast
    rw [← mul_pow, ← pow_add]
    congr 2; ring
  have hc1 : 0 ≤ c1 d L := by have := one_le_c1 d L; linarith
  have hcard : ((renLabelFam G (X1 G m₀ j 𝒦X) X).card : ℝ) ≤
      c1 d L * (((L ^ m₀) ^ d : ℕ) : ℝ) * (1 + sizeJ m₀ K X) := by
    have h4 : ((renLabelFam G (X1 G m₀ j 𝒦X) X).card : ℝ) * (((L ^ (K + m₁) : ℕ) : ℝ)) ^ d ≤
        c1 d L * (((L ^ m₀) ^ d : ℕ) : ℝ) * (1 + sizeJ m₀ K X) *
          (((L ^ (K + m₁) : ℕ) : ℝ)) ^ d := by
      refine hcount.trans (hG1.trans (le_of_eq ?_))
      rw [hcs]; unfold sizeJ; ring
    exact le_of_mul_le_mul_right h4 hs0
  have hdd : 0 ≤ (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) := by positivity
  calc _ ≤ _ := h3
    _ ≤ d * (((2 * L + 1) ^ d : ℕ) : ℝ) *
          (c1 d L * (((L ^ m₀) ^ d : ℕ) : ℝ) * (1 + sizeJ m₀ K X)) :=
        mul_le_mul_of_nonneg_left hcard hdd
    _ = _ := by unfold renDetA; ring

end Size

end Balaban.Fluctuation
