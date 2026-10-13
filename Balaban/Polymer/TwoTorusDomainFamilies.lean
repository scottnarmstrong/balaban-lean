/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusThickSets
public import Balaban.Localization.I5Expansion
public import Balaban.Localization.I5Glue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The families of the expansion on two step tori

For two step tori identified on a centred box by `boxMap`, the index sets, patches, `Y[𝒞]` and
`Y(𝒞)` of a family of cube centres correspond (`TwoTorusThickSets`).  This file extends the
correspondence to the finite families of indices used by the expansion of Theorem I-5: connected
families (`IsConnectedFamily`), the families `connFams` with a given `Y[𝒞]`, and the domains
`polymerDomains`.  The margin is `2ρ + 5 · L · cellSide < N₁ L^m₁ L^K, N₁' L^m₁ L^K`, as in
`TwoTorusThickSets`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale

section Families

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j m₀ : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

omit [NeZero N₁'] in
/-- The whole-lattice generating set `levelGS j` is a union of aligned cubes of side `L a_j`. -/
theorem layerUnion_levelGS (hj : j ≤ K) (m₀ : ℕ) :
    LayerUnion (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) m₀ := by
  intro n hn1 hnK z hz
  have h := layer_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj n
  rw [h] at hz
  have hn : n = j := by
    by_contra hne
    simp [hne] at hz
  refine ⟨cbase (cellSide L m₀ m₁ n) z, aligned_cbase z,
    box_mono _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L)))
      (mem_box_cbase (cellSide_pos m₀ m₁ n) z), fun x _ => ?_⟩
  rw [Finset.mem_coe, h]
  simp [hn]

end Families

section OneTorus

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {j m₀ : ℕ}
variable {ρ : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
  (hn : 2 * ρ + 5 * (L * cellSide L m₀ m₁ j) < (N₁ * L ^ m₁) * L ^ K)

local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj

include hN hj hn

/-- The sites `D(P)` of a cube centre with base point in the box of radius `ρ` lie in the box of
radius `ρ + 2 L a_j`. -/
theorem dsites_inBox {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx GA)
    (hq0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) q.2) :
    ∀ x ∈ Dsites GA m₀ q, InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j)
      ((N₁ * L ^ m₁) * L ^ K) x := by
  obtain ⟨y, rfl, -⟩ := exists_of_mem_cubeIdx hj hq
  intro x hx
  simp only [Dsites, Set.mem_iUnion] at hx
  obtain ⟨b, hb, hx⟩ := hx
  exact (dcubes_fwd (N₁' := N₁) hN hN hj hn hq0 hb).1 x hx

omit hN in
/-- The union `X₁ ∪ ⋃ P_i` of a boxed family of patches lies in the box of radius `ρ + 2 L a_j`. -/
theorem patchUnion_inBox {ι : Type*} (c : ι → ℕ × CTorus d L N₁ m₁ K) (C : Finset ι)
    (hc : ∀ i ∈ C, c i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (c i).2)
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    ∀ x ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C,
      InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ K) x := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  rintro x (hx | hx)
  · exact inBox_mono (by omega) (hX x hx)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨y, hqe, hb⟩ := exists_of_mem_cubeIdx hj (hc i hi).1
    have h0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y := by
      have := (hc i hi).2; rw [hqe] at this; exact this
    rw [hqe, pset_eq_box hj hb] at hx
    exact inBox_mono (by omega) (inBox_of_mem_box_right (by omega) h0 hx)

/-- `Y[𝒞]` of a boxed family lies in the box of radius `ρ + 2 L a_j`. -/
theorem ysites_inBox {ι : Type*} (c : ι → ℕ × CTorus d L N₁ m₁ K) (C : Finset ι)
    (hc : ∀ i ∈ C, c i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (c i).2)
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    ∀ x ∈ Ysites GA m₀ c X₁ C,
      InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ K) x := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  rintro x (hx | hx)
  · exact inBox_mono (by omega) (hX x hx)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hx⟩ := hx
    exact dsites_inBox hN hj hn (hc i hi).1 (hc i hi).2 x hx

omit hN in
/-- `Y(𝒞)` of a boxed family lies in the box of radius `ρ + 2 L a_j`. -/
theorem compY_inBox {ι : Type*} (c : ι → ℕ × CTorus d L N₁ m₁ K) (C : Finset ι)
    (hc : ∀ i ∈ C, c i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (c i).2)
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    ∀ x ∈ compY c X₁ C,
      InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ K) x :=
  fun x hx => patchUnion_inBox hj hn c C hc hX x
    (componentOf_subset _ (fun _ hy => Or.inl hy) hx)

end OneTorus

section Families2

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j m₀ : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)

omit [NeZero N₁] [NeZero N₁'] in
/-- `boxMap` is injective on the box of radius `ρ + 2 L a_j`. -/
theorem injOn_boxMap_wide {ρ : ℕ}
    (hn' : 2 * ρ + 5 * (L * cellSide L m₀ m₁ j) < (N₁' * L ^ m₁) * L ^ K) :
    Set.InjOn bm {x | InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j)
      ((N₁ * L ^ m₁) * L ^ K) x} := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  exact fun a ha b hb h => boxMap_inj (hm' := (by omega : 2 * (ρ + L * cellSide L m₀ m₁ j +
    L * cellSide L m₀ m₁ j) + 1 < (N₁' * L ^ m₁) * L ^ K)) ha hb h

end Families2

section Families3

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j m₀ : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

variable {ρ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
  (hn : 2 * ρ + 5 * (L * cellSide L m₀ m₁ j) < (N₁ * L ^ m₁) * L ^ K)
  (hn' : 2 * ρ + 5 * (L * cellSide L m₀ m₁ j) < (N₁' * L ^ m₁) * L ^ K)

local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj

section Generic

variable {ιA ιB : Type*}
  (cA : ιA → ℕ × CTorus d L N₁ m₁ K) (cB : ιB → ℕ × CTorus d L N₁' m₁ K)

include hN hN' hj hn hn'

/-- **`Y[𝒞]` of corresponding families.**  `C'` is the family of the second torus whose centres
are the images of the centres of `C` (both inclusions are hypotheses `h1`, `h2`); the centres of
`C` lie in the cube index and in the box of radius `ρ`. -/
theorem ysites_img (C : Finset ιA) (C' : Finset ιB)
    (hC : ∀ i ∈ C, cA i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (cA i).2)
    (h1 : ∀ i' ∈ C', ∃ i ∈ C, cB i' = Prod.map id bm (cA i))
    (h2 : ∀ i ∈ C, ∃ i' ∈ C', cB i' = Prod.map id bm (cA i))
    (X₁ : Set (CTorus d L N₁ m₁ K)) :
    Ysites GB m₀ cB (bm '' X₁) C' = bm '' Ysites GA m₀ cA X₁ C := by
  rw [← ysites_image hN hN' hj hn hn' cA C hC X₁]
  unfold Ysites
  congr 1
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i', hi', hx⟩
    obtain ⟨i, hi, he⟩ := h1 i' hi'
    exact ⟨i, hi, by rw [← he]; exact hx⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨i', hi', he⟩ := h2 i hi
    exact ⟨i', hi', by rw [he]; exact hx⟩

omit hN hN' in
/-- **`Y(𝒞)` of corresponding families.** -/
theorem compY_img (C : Finset ιA) (C' : Finset ιB)
    (hC : ∀ i ∈ C, cA i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (cA i).2)
    (h1 : ∀ i' ∈ C', ∃ i ∈ C, cB i' = Prod.map id bm (cA i))
    (h2 : ∀ i ∈ C, ∃ i' ∈ C', cB i' = Prod.map id bm (cA i))
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    compY cB (bm '' X₁) C' = bm '' compY cA X₁ C := by
  rw [← compY_image hj hn hn' cA C hC hX]
  have hp : patchUnion (bm '' X₁) (fun i => Pset m₁ (cB i)) C' =
      patchUnion (bm '' X₁) (fun i => Pset m₁ (Prod.map id bm (cA i))) C := by
    unfold patchUnion
    congr 1
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i', hi', hx⟩
      obtain ⟨i, hi, he⟩ := h1 i' hi'
      exact ⟨i, hi, by rw [← he]; exact hx⟩
    · rintro ⟨i, hi, hx⟩
      obtain ⟨i', hi', he⟩ := h2 i hi
      exact ⟨i', hi', by rw [he]; exact hx⟩
  unfold compY
  rw [hp]

omit hN hN' in
/-- **T2: connected families correspond.**  For a finite family `C` of cube indices whose centres
have base points in the box of radius `ρ` and the family `C'` of the images, `C'` is connected for
the second torus exactly when `C` is connected for the first.  The margin is
`2ρ + 5 · L · cellSide < N₁ L^m₁ L^K, N₁' L^m₁ L^K`. -/
theorem isConnectedFamily_img (C : Finset ιA) (C' : Finset ιB)
    (hC : ∀ i ∈ C, cA i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (cA i).2)
    (h1 : ∀ i' ∈ C', ∃ i ∈ C, cB i' = Prod.map id bm (cA i))
    (h2 : ∀ i ∈ C, ∃ i' ∈ C', cB i' = Prod.map id bm (cA i))
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    IsConnectedFamily (fun i => Pset m₁ (cB i)) (compY cB (bm '' X₁)) C' ↔
      IsConnectedFamily (fun i => Pset m₁ (cA i)) (compY cA X₁) C := by
  have hinj := injOn_boxMap_wide (N₁ := N₁) (N₁' := N₁') (d := d) (L := L) (m₁ := m₁) (K := K)
    (j := j) (m₀ := m₀) hn'
  unfold IsConnectedFamily
  rw [compY_img hj hn hn' cA cB C C' hC h1 h2 hX]
  constructor
  · intro h i hi
    obtain ⟨i', hi', he⟩ := h2 i hi
    have : Pset m₁ (cB i') ⊆ _ := h i' hi'
    rw [he, ← pset_image_q hj hn (hC i hi).1 (hC i hi).2] at this
    show Pset m₁ (cA i) ⊆ _
    refine (hinj.image_subset_image_iff ?_ (compY_inBox hj hn cA C hC hX)).1 this
    exact fun x hx => patchUnion_inBox hj hn cA C hC hX x
      (Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hx⟩))
  · intro h i' hi'
    obtain ⟨i, hi, he⟩ := h1 i' hi'
    show Pset m₁ (cB i') ⊆ _
    rw [he, ← pset_image_q hj hn (hC i hi).1 (hC i hi).2]
    exact Set.image_mono (h i hi)

include hN hN' hj hn hn' in
/-- **T3, generic form.**  For corresponding finite families `C`, `C'` (centres of `C'` are the
images of the centres of `C`, boxed with base points in the box of radius `ρ`), `X₁` and `Y`
inside the box, `C'` is a connected family of the second torus with `Y[𝒞'] = boxMap '' Y` exactly
when `C` is a connected family of the first torus with `Y[𝒞] = Y`. -/
theorem mem_connFams_img [DecidableEq ιA] [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (C : Finset ιA) (C' : Finset ιB)
    (hC : ∀ i ∈ C, cA i ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (cA i).2)
    (h1 : ∀ i' ∈ C', ∃ i ∈ C, cB i' = Prod.map id bm (cA i))
    (h2 : ∀ i ∈ C, ∃ i' ∈ C', cB i' = Prod.map id bm (cA i))
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    C' ∈ connFams cB GB m₀ (bm '' X₁) (bm '' Y) ↔ C ∈ connFams cA GA m₀ X₁ Y := by
  have hinj := injOn_boxMap_wide (N₁ := N₁) (N₁' := N₁') (d := d) (L := L) (m₁ := m₁) (K := K)
    (j := j) (m₀ := m₀) hn'
  rw [mem_connFams cB, mem_connFams cA, isConnectedFamily_img hj hn hn' cA cB C C' hC h1 h2 hX,
    ysites_img hN hN' hj hn hn' cA cB C C' hC h1 h2 X₁]
  refine and_congr_right fun _ => ?_
  exact hinj.image_eq_image_iff (ysites_inBox hN hj hn cA C hC hX)
    (fun y hy => inBox_mono (by omega) (hY y hy))

end Generic

section ParIdx

include hN hN' hj hn hn'

omit hN hN' in
/-- Every index of `ParIdx` of the second torus with centre in the box of radius `ρ` is the image
of an index of `ParIdx` of the first torus with centre in the box. -/
theorem exists_parIdx_preimage (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (i' : ParIdx GB (bm '' X₁)) (hi' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) i'.1.1.2) :
    ∃ i : ParIdx GA X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 ∧
      i'.1.1 = Prod.map id bm i.1.1 := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  have hn1 : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hn1' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  have hmem : i'.1.1 ∈ (cubeIdx GB).filter
      (fun q => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2) :=
    Finset.mem_filter.2 ⟨i'.1.2, hi'⟩
  rw [cubeIdx_filter_image hj1 hj hn1 hn1'] at hmem
  obtain ⟨q0, hq0, hq⟩ := Finset.mem_image.1 hmem
  rw [Finset.mem_filter] at hq0
  have hd : Disjoint (Pset m₁ (Prod.map id bm q0)) (bm '' X₁) := by
    rw [hq]; exact i'.2
  exact ⟨⟨⟨q0, hq0.1⟩, (pset_disjoint_iff hj hn hn' hq0.1 hq0.2 hX).1 hd⟩, hq0.2, hq.symm⟩

omit hN hN' in
/-- Every index of `ParIdx` of the first torus with centre in the box of radius `ρ` goes to an
index of `ParIdx` of the second torus. -/
theorem exists_parIdx_image (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (i : ParIdx GA X₁) (hi : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2) :
    ∃ i' : ParIdx GB (bm '' X₁), InBox d ρ ((N₁' * L ^ m₁) * L ^ K) i'.1.1.2 ∧
      i'.1.1 = Prod.map id bm i.1.1 := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  have hn1 : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hn1' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  have hmem : Prod.map id bm i.1.1 ∈ (cubeIdx GB).filter
      (fun q => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2) := by
    rw [cubeIdx_filter_image hj1 hj hn1 hn1']
    exact Finset.mem_image.2 ⟨i.1.1, Finset.mem_filter.2 ⟨i.1.2, hi⟩, rfl⟩
  rw [Finset.mem_filter] at hmem
  exact ⟨⟨⟨_, hmem.1⟩, (pset_disjoint_iff hj hn hn' i.1.2 hi hX).2 i.2⟩, hmem.2, rfl⟩

omit hN hN' in
/-- **T1 (the index map on `ParIdx`).**  The centres of the indices of `ParIdx` of the second torus
that lie in the box of radius `ρ` are exactly the images, under `Prod.map id boxMap`, of the
centres of the indices of `ParIdx` of the first torus that lie in the box. -/
theorem parIdx_centres_image (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    ((Finset.univ : Finset (ParIdx GB (bm '' X₁))).filter
        (fun i => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) i.1.1.2)).image (fun i => i.1.1) =
      ((Finset.univ : Finset (ParIdx GA X₁)).filter
        (fun i => InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2)).image
          (fun i => Prod.map id bm i.1.1) := by
  ext q
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i', hi', rfl⟩
    obtain ⟨i, hi, he⟩ := exists_parIdx_preimage hj hn hn' hj1 hX i' hi'
    exact ⟨i, hi, he.symm⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨i', hi', he⟩ := exists_parIdx_image hj hn hn' hj1 hX i hi
    exact ⟨i', hi', he⟩

omit [NeZero N₁'] hN hN' hn in
/-- The index map is injective on the indices with centre in the box. -/
theorem parIdx_inj {X₁ : Set (CTorus d L N₁ m₁ K)} {i₁ i₂ : ParIdx GA X₁}
    (h₁ : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i₁.1.1.2)
    (h₂ : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i₂.1.1.2)
    (h : Prod.map id bm i₁.1.1 = Prod.map id bm i₂.1.1) : i₁ = i₂ := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  exact Subtype.ext (Subtype.ext (injOn_idxMap (by omega) h₁ h₂ h))

omit [NeZero N₁] [NeZero N₁'] hN hN' hj hn hn' in
/-- The centres of a family of `ParIdx` whose `Y[𝒞]` lies in the box lie in the box. -/
theorem boxed_of_ysites {N : ℕ} [NeZero N] {G : GeneratingSet d L (N * L ^ m₁) K ϱ}
    (hU : LayerUnion G m₀) (hNN : L ^ m₀ ∣ N) {X₁ Y : Set (CTorus d L N m₁ K)}
    {C : Finset (ParIdx G X₁)} (hYC : Ysites G m₀ (fun i : ParIdx G X₁ => i.1.1) X₁ C = Y)
    {P : CTorus d L N m₁ K → Prop} (hY : ∀ y ∈ Y, P y) : ∀ i ∈ C, P i.1.1.2 := by
  intro i hi
  apply hY
  rw [← hYC]
  right
  simp only [Set.mem_iUnion]
  exact ⟨i, hi, Pset_subset_Dsites hU hNN i.1.2 (self_mem_Pset _)⟩

omit hN hN' hn hn' in
/-- The family of the images of a family of `ParIdx`. -/
theorem exists_img_family (X₁ : Set (CTorus d L N₁ m₁ K)) :
    ∃ e : Finset (ParIdx GA X₁) → Finset (ParIdx GB (bm '' X₁)),
      ∀ C i', i' ∈ e C ↔ ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1 :=
  ⟨fun C => Finset.univ.filter fun i' => ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1,
    fun C i' => by simp⟩

omit hN hN' in
/-- The family of the preimages of a boxed family of `ParIdx` of the second torus. -/
theorem exists_pre_family (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (C' : Finset (ParIdx GB (bm '' X₁)))
    (hb : ∀ i' ∈ C', InBox d ρ ((N₁' * L ^ m₁) * L ^ K) i'.1.1.2) :
    ∃ C : Finset (ParIdx GA X₁),
      (∀ i ∈ C, i.1.1 ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2) ∧
      (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) ∧
      (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) := by
  obtain ⟨C, hC⟩ : ∃ C : Finset (ParIdx GA X₁), ∀ i, i ∈ C ↔
      (InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 ∧ ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) :=
    ⟨Finset.univ.filter fun i => InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 ∧
      ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1, fun i => by simp⟩
  refine ⟨C, fun i hi => ⟨i.1.2, ((hC i).1 hi).1⟩, fun i' hi' => ?_,
    fun i hi => ((hC i).1 hi).2⟩
  obtain ⟨i, hi, he'⟩ := exists_parIdx_preimage hj hn hn' hj1 hX i' (hb i' hi')
  exact ⟨i, (hC i).2 ⟨hi, i', hi', he'⟩, he'⟩

include hN hN' in
/-- The image of a connected family with `Y[𝒞] = Y` is a connected family with
`Y[𝒞] = boxMap '' Y`. -/
theorem connFams_img_mem (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y)
    (e : Finset (ParIdx GA X₁) → Finset (ParIdx GB (bm '' X₁)))
    (he : ∀ C i', i' ∈ e C ↔ ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1)
    (C : Finset (ParIdx GA X₁))
    (hC : C ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y) :
    e C ∈ connFams (fun i : ParIdx GB (bm '' X₁) => i.1.1) GB m₀ (bm '' X₁) (bm '' Y) := by
  have hUA := layerUnion_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj m₀
  have hboxA : ∀ i ∈ C, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 :=
    boxed_of_ysites hUA hN ((mem_connFams (fun i : ParIdx GA X₁ => i.1.1)).1 hC).2 hY
  have hA : ∀ i ∈ C, i.1.1 ∈ cubeIdx GA ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 :=
    fun i hi => ⟨i.1.2, hboxA i hi⟩
  have h1 : ∀ i' ∈ e C, ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1 :=
    fun i' hi' => (he C i').1 hi'
  have h2 : ∀ i ∈ C, ∃ i' ∈ e C, i'.1.1 = Prod.map id bm i.1.1 := fun i hi => by
    obtain ⟨i', -, hi'⟩ := exists_parIdx_image hj hn hn' hj1 hX i (hboxA i hi)
    exact ⟨i', (he C i').2 ⟨i, hi, hi'⟩, hi'⟩
  exact (mem_connFams_img hN hN' hj hn hn' (fun i : ParIdx GA X₁ => i.1.1)
    (fun i : ParIdx GB (bm '' X₁) => i.1.1) C (e C) hA h1 h2 hX hY).2 hC

include hN hN' in
/-- Every connected family of the second torus with `Y[𝒞] = boxMap '' Y` is the image of a
connected family of the first torus with `Y[𝒞] = Y`. -/
theorem connFams_pre_mem (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y)
    (C' : Finset (ParIdx GB (bm '' X₁)))
    (hC' : C' ∈ connFams (fun i : ParIdx GB (bm '' X₁) => i.1.1) GB m₀ (bm '' X₁) (bm '' Y)) :
    ∃ C ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y,
      (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) ∧
      (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) := by
  have hn1' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K := by
    obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
    omega
  have hUB := layerUnion_levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj m₀
  have hb : ∀ i' ∈ C', InBox d ρ ((N₁' * L ^ m₁) * L ^ K) i'.1.1.2 := by
    intro i' hi'
    obtain ⟨y, hy, hyc⟩ := boxed_of_ysites hUB hN'
      ((mem_connFams (fun i : ParIdx GB (bm '' X₁) => i.1.1)).1 hC').2
      (P := fun z => z ∈ bm '' Y) (fun z hz => hz) i' hi'
    rw [← hyc]
    exact inBox_boxMap hn1' (hY y hy)
  obtain ⟨C, hC1, h1, h2⟩ := exists_pre_family hj hn hn' hj1 hX C' hb
  have key := mem_connFams_img hN hN' hj hn hn' (fun i : ParIdx GA X₁ => i.1.1)
    (fun i : ParIdx GB (bm '' X₁) => i.1.1) C C' hC1 h1 h2 hX hY
  exact ⟨C, key.1 hC', h1, h2⟩

omit hN hN' in
/-- The image map is injective on connected families with `Y[𝒞] = Y`. -/
theorem img_family_injOn (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hboxA : ∀ C ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y, ∀ i ∈ C,
      InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2)
    (e : Finset (ParIdx GA X₁) → Finset (ParIdx GB (bm '' X₁)))
    (he : ∀ C i', i' ∈ e C ↔ ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) :
    Set.InjOn e ↑(connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y) := by
  have hsub : ∀ C₁ ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y,
      ∀ C₂ ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y, e C₁ = e C₂ → C₁ ⊆ C₂ := by
    intro C₁ h₁ C₂ h₂ h12 i hi
    obtain ⟨i', -, hc⟩ := exists_parIdx_image hj hn hn' hj1 hX i (hboxA C₁ h₁ i hi)
    have hi' : i' ∈ e C₁ := (he C₁ i').2 ⟨i, hi, hc⟩
    rw [h12] at hi'
    obtain ⟨i2, hi2, hc2⟩ := (he C₂ i').1 hi'
    have hii : i = i2 := parIdx_inj hj hn' (hboxA C₁ h₁ i hi) (hboxA C₂ h₂ i2 hi2)
      (by rw [← hc, ← hc2])
    exact hii ▸ hi2
  intro C₁ h₁ C₂ h₂ h12
  exact Finset.Subset.antisymm (hsub C₁ h₁ C₂ h₂ h12) (hsub C₂ h₂ C₁ h₁ h12.symm)

include hN hN' in
/-- **T3 (the connected families correspond).**  Let `X₁` and `Y` lie in the box of radius `ρ`.
There is a map `e` from families of `ParIdx` of the first torus to families of `ParIdx` of the
second torus, with `i' ∈ e C ↔ ∃ i ∈ C, centre i' = Prod.map id boxMap (centre i)`, injective on
`connFams … Y`, such that the connected families of the second torus with `Y[𝒞] = boxMap '' Y`
are exactly the images `e C` of the connected families `C` of the first torus with `Y[𝒞] = Y`.
Margin: `2ρ + 5 · L · cellSide < N₁ L^m₁ L^K, N₁' L^m₁ L^K`. -/
theorem connFams_parIdx_boxMap (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    ∃ e : Finset (ParIdx GA X₁) → Finset (ParIdx GB (bm '' X₁)),
      (∀ C i', i' ∈ e C ↔ ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) ∧
      Set.InjOn e ↑(connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y) ∧
      connFams (fun i : ParIdx GB (bm '' X₁) => i.1.1) GB m₀ (bm '' X₁) (bm '' Y) =
        (connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y).image e := by
  have hUA := layerUnion_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj m₀
  have hboxA : ∀ C ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y, ∀ i ∈ C,
      InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 := fun C hC =>
    boxed_of_ysites hUA hN ((mem_connFams (fun i : ParIdx GA X₁ => i.1.1)).1 hC).2 hY
  obtain ⟨e, he⟩ := exists_img_family (N₁ := N₁) (N₁' := N₁') (d := d) (L := L) (m₁ := m₁)
    (K := K) (ϱ := ϱ) hj X₁
  refine ⟨e, he, img_family_injOn hj hn hn' hj1 hX hboxA e he, ?_⟩
  ext C'
  rw [Finset.mem_image]
  constructor
  · intro hC'
    obtain ⟨C, hC, h1, h2⟩ := connFams_pre_mem hN hN' hj hn hn' hj1 hX hY C' hC'
    refine ⟨C, hC, ?_⟩
    ext i'
    rw [he]
    constructor
    · rintro ⟨i, hi, hc⟩
      obtain ⟨i'', hi'', hc''⟩ := h2 i hi
      have : i' = i'' := Subtype.ext (Subtype.ext (hc.trans hc''.symm))
      exact this ▸ hi''
    · intro hi'
      exact h1 i' hi'
  · rintro ⟨C, hC, hCe⟩
    rw [← hCe]
    exact connFams_img_mem hN hN' hj hn hn' hj1 hX hY e he C hC

omit [NeZero N₁] [NeZero N₁'] hN hN' hj hn hn' in
/-- A set is a domain `Y[𝒞]` of a connected family exactly when some connected family has it. -/
theorem mem_polymerDomains_iff_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    [NeZero N] {G : GeneratingSet d L (N * L ^ m₁) K ϱ}
    (c : ι → ℕ × CTorus d L N m₁ K) (X Z : Set (CTorus d L N m₁ K)) :
    Z ∈ polymerDomains c G m₀ X ↔ (connFams c G m₀ X Z).Nonempty := by
  simp only [polymerDomains, connFams, Finset.mem_image, Finset.Nonempty, Finset.mem_filter,
    Finset.mem_univ, true_and]

include hN hN' in
/-- **T3, domains.**  For `X₁` and `Y` in the box of radius `ρ`, `boxMap '' Y` is a domain
`Y[𝒞]` of a connected family of the second torus exactly when `Y` is one of the first torus. -/
theorem mem_polymerDomains_boxMap_iff (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    bm '' Y ∈ polymerDomains (fun i : ParIdx GB (bm '' X₁) => i.1.1) GB m₀ (bm '' X₁) ↔
      Y ∈ polymerDomains (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ := by
  rw [mem_polymerDomains_iff_nonempty, mem_polymerDomains_iff_nonempty]
  obtain ⟨e, he, hinj, himg⟩ := connFams_parIdx_boxMap hN hN' hj hn hn' hj1 hX hY
  rw [himg, Finset.image_nonempty]

include hN hN' in
/-- **T3, domains, second form.**  A set `Y'` of the box of radius `ρ` of the second torus is a
domain of the second torus exactly when `Y' = boxMap '' Y` for a domain `Y` of the first torus
(`Y = boxMap' '' Y'`, in the box). -/
theorem polymerDomains_boxMap_iff_of_inBox (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y' : Set (CTorus d L N₁' m₁ K)} (hY' : ∀ y ∈ Y', InBox d ρ ((N₁' * L ^ m₁) * L ^ K) y) :
    Y' ∈ polymerDomains (fun i : ParIdx GB (bm '' X₁) => i.1.1) GB m₀ (bm '' X₁) ↔
      ∃ Y : Set (CTorus d L N₁ m₁ K), (∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) ∧
        Y' = bm '' Y ∧ Y ∈ polymerDomains (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  have hn1' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  have hY : ∀ y ∈ bm' '' Y', InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap (by omega) (hY' y hy)
  have hY'e : bm '' (bm' '' Y') = Y' := image_image_boxMap (by omega) hY'
  constructor
  · intro h
    refine ⟨bm' '' Y', hY, hY'e.symm, ?_⟩
    rw [← mem_polymerDomains_boxMap_iff hN hN' hj hn hn' hj1 hX hY, hY'e]
    exact h
  · rintro ⟨Y, hYb, rfl, hYd⟩
    exact (mem_polymerDomains_boxMap_iff hN hN' hj hn hn' hj1 hX hYb).2 hYd

include hN hN' in
/-- **Reindexing of the terms `evTerm` (the finite re-indexing).**  Let `F`, `F'` be functions
of data and decoupling parameters of the two tori.  If the coefficients `coef (F' u') C'` and
`coef (F u) C` agree for every pair of corresponding connected families (`C` connected with
`Y[𝒞] = Y`; `C'` has as centres exactly the images of the centres of `C`), then
`evTerm` of the second torus at `boxMap '' Y` equals `evTerm` of the first torus at `Y`. -/
theorem evTerm_boxMap {U U' : Type*} (hj1 : 1 ≤ j) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : ∀ y ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y)
    (F : U → (ParIdx GA X₁ → ℂ) → ℂ) (F' : U' → (ParIdx GB (bm '' X₁) → ℂ) → ℂ) (u : U) (u' : U')
    (hcoef : ∀ C ∈ connFams (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ Y,
      ∀ C' : Finset (ParIdx GB (bm '' X₁)),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) →
        coef (F' u') C' = coef (F u) C) :
    evTerm (fun i : ParIdx GB (bm '' X₁) => i.1.1) GB m₀ (bm '' X₁) F' (bm '' Y) u' =
      evTerm (fun i : ParIdx GA X₁ => i.1.1) GA m₀ X₁ F Y u := by
  obtain ⟨e, he, hinj, himg⟩ := connFams_parIdx_boxMap hN hN' hj hn hn' hj1 hX hY
  have hUA := layerUnion_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj m₀
  unfold evTerm
  rw [himg, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun C hC => ?_
  refine hcoef C hC (e C) (fun i hi => ?_) (fun i' hi' => (he C i').1 hi')
  have hbox : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 :=
    boxed_of_ysites hUA hN ((mem_connFams (fun i : ParIdx GA X₁ => i.1.1)).1 hC).2 hY i hi
  obtain ⟨i', -, hi'⟩ := exists_parIdx_image hj hn hn' hj1 hX i hbox
  exact ⟨i', (he C i').2 ⟨i, hi, hi'⟩, hi'⟩

end ParIdx

end Families3

end Balaban.Polymer.TwoTorusStep
