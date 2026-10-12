/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeSystem
public import Balaban.Fluctuation.Prop33Count
public import Balaban.Fluctuation.HatEngineLocal
public import Balaban.Polymer.MarkedCubes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Thickening of a domain by the cubes next to it (support of a block-local term)

A term of the expansion of Proposition 3.3 in the variable `ψ̂` for the domain `Y` is local in the
hat variable at the unit points of the sites of `blockThick Y`: the `(k+1)`-blocks meeting `Y` or a
nearest neighbour of `Y`.  These blocks lie in the `π_{k+1}`-cubes meeting `psiThick Y`.  For a
block-local activity, the support has to contain all of these cubes: the support of the label is
the union `Z` of `Y` and the `π'`-cubes `box p (L a)` containing a cube of `Y` together with a
neighbouring cube.  The size of `Z` is controlled by (G3) (`G3_dcov`) applied once for each added
cube: `d^cov(Z) ≤ d^cov(Y) + (number of added cubes) c_G`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale

section Boxes

variable {d n : ℕ}

/-- A box is nearest-neighbour connected. -/
theorem siteConnected_box_aux (p : Torus d n) (s : ℕ) :
    ∀ x ∈ box p s, ∀ y ∈ box p s,
      Relation.ReflTransGen (fun u v => u ∈ box p s ∧ v ∈ box p s ∧ Nbr u v) x y := by
  have hto : ∀ x ∈ box p s, Relation.ReflTransGen
      (fun u v => u ∈ box p s ∧ v ∈ box p s ∧ Nbr u v) p x := by
    rintro x ⟨w, hw, rfl⟩
    have h := reach_box p w (box p s) (fun w' hw' => ⟨w', fun μ => lt_of_le_of_lt (hw' μ) (hw μ), rfl⟩)
    refine Relation.ReflTransGen.mono (fun u v huv => ⟨huv.2.1, huv.2.2, huv.1.2⟩) _ _ h
  intro x hx y hy
  have hsymm : ∀ a b : Torus d n, (a ∈ box p s ∧ b ∈ box p s ∧ Nbr a b) →
      (b ∈ box p s ∧ a ∈ box p s ∧ Nbr b a) := fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  exact (rtg_symm hsymm (hto x hx)).trans (hto y hy)

end Boxes

section Thick

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- The base obtained from the cell base `c` by going back one cell in the directions `o`. -/
def pBase (a : ℕ) (c : CTorus d L N₁ m₁ K) (o : Fin d → Bool) : CTorus d L N₁ m₁ K :=
  c + natT (fun μ => if o μ then (N₁ * L ^ m₁) * L ^ K - a else 0)

theorem pBase_aligned {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) {c : CTorus d L N₁ m₁ K}
    (hc : Aligned a c) (o : Fin d → Bool) : Aligned a (pBase a c o) := by
  refine aligned_add_natT ha hc fun μ => ?_
  by_cases h : o μ
  · simp only [h, ite_true]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub ha dvd_rfl)
  · simp [h]

theorem eq_pBase_add {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K)
    (c : CTorus d L N₁ m₁ K) (o : Fin d → Bool) :
    c = pBase a c o + natT (fun μ => if o μ then a else 0) := by
  have hle : a ≤ (N₁ * L ^ m₁) * L ^ K := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) ha
  funext μ
  simp only [pBase, Pi.add_apply, natT_apply]
  by_cases h : o μ
  · simp only [h, ite_true]
    rw [add_assoc, ← Nat.cast_add, Nat.sub_add_cancel hle]
    simp
  · simp [h]

omit [NeZero N₁] [NeZero L] in
theorem box_subset_of_offset (hL : 2 ≤ L) {a : ℕ} {p c' : CTorus d L N₁ m₁ K} {off : Fin d → ℕ}
    (h : c' = p + natT off) (hoff : ∀ μ, off μ ≤ a) : box c' a ⊆ box p (L * a) := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨off + w, fun μ => ?_, ?_⟩
  · have h1 := hoff μ
    have h2 := hw μ
    have h3 : 2 * a ≤ L * a := Nat.mul_le_mul_right a hL
    simp only [Pi.add_apply]
    omega
  · rw [h, natT_add]; abel

theorem exists_pBase_near (hL : 2 ≤ L) {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {c c' : CTorus d L N₁ m₁ K} (hnear : Near 1 a c c') :
    ∃ o : Fin d → Bool, box c a ⊆ box (pBase a c o) (L * a) ∧
      box c' a ⊆ box (pBase a c o) (L * a) := by
  have hle : a ≤ (N₁ * L ^ m₁) * L ^ K := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) ha
  obtain ⟨q, hq, hc'⟩ := hnear
  have hq' : ∀ μ, q μ = -1 ∨ q μ = 0 ∨ q μ = 1 := fun μ => by
    have := abs_le.1 (hq μ); omega
  refine ⟨fun μ => decide (q μ = -1), ?_, ?_⟩
  · refine box_subset_of_offset hL (eq_pBase_add ha c _) fun μ => ?_
    split_ifs <;> omega
  · refine box_subset_of_offset hL (off := fun μ => if q μ = 1 then a else 0) ?_ fun μ => ?_
    · rw [hc']
      funext μ
      simp only [pBase, Pi.add_apply, natT_apply]
      rcases hq' μ with h | h | h
      · simp only [h, decide_true, ite_true]
        have : ¬ ((-1 : ℤ) = 1) := by omega
        simp only [this, ite_false]
        push_cast
        rw [Nat.cast_sub hle]
        simp
      · simp [h]
      · simp only [h]
        have : ¬ ((1 : ℤ) = -1) := by omega
        simp [this]
    · split_ifs <;> omega

omit [NeZero N₁] in
theorem isDj_box {p : CTorus d L N₁ m₁ K} (hp : Aligned (cellSide L m₀ m₁ j) p) :
    IsDj m₀ j (box p (L * cellSide L m₀ m₁ j)) := by
  have hLa : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  exact ⟨⟨p, mem_box_self p hLa⟩, fun z hz => ⟨p, hp, hz, subset_rfl⟩,
    siteConnected_box_aux p _⟩

omit [NeZero N₁] in
theorem dcovMod_box_le {p : CTorus d L N₁ m₁ K} (hp : Aligned (cellSide L m₀ m₁ j) p) :
    dcovMod m₀ j Set.univ (box p (L * cellSide L m₀ m₁ j)) ≤ 0 := by
  classical
  have hLa : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  have hadm : ModAdmissible m₀ j Set.univ (box p (L * cellSide L m₀ m₁ j)) {p} {p} ∅ := by
    refine ⟨fun b hb => ?_, fun z hz => ?_, ⟨⟨p, by simp⟩, by simp, ?_⟩, ?_, ?_⟩
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact ⟨hp, subset_rfl⟩
    · exact Set.mem_iUnion₂.2 ⟨p, rfl, hz.1⟩
    · intro x hx y hy
      simp only [Finset.mem_singleton] at hx hy
      subst hx; subst hy; exact Relation.ReflTransGen.refl
    · intro x hx; simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx; subst hx
      exact mem_box_self _ hLa
    · intro b hb; rw [Set.mem_singleton_iff] at hb; subst hb
      exact ⟨b, by simp, mem_box_self _ hLa⟩
  have := dcovMod_le_of_admissible hadm
  simpa [bondCost] using this

theorem thick_union {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ j Y) (P : Finset (CTorus d L N₁ m₁ K))
    (hP : ∀ p ∈ P, Aligned (cellSide L m₀ m₁ j) p ∧
      ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧ box t (cellSide L m₀ m₁ j) ⊆ Y ∩ box p (L * cellSide L m₀ m₁ j)) :
    IsDj m₀ j (Y ∪ ⋃ p ∈ P, box p (L * cellSide L m₀ m₁ j)) ∧
      treeLenCovOne m₀ j (Y ∪ ⋃ p ∈ P, box p (L * cellSide L m₀ m₁ j)) ≤
        treeLenCovOne m₀ j Y + P.card * cG d L := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using hY
  | insert q P' hq ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun p hp => hP p (Finset.mem_insert_of_mem hp))
    obtain ⟨hq1, t, ht1, ht2⟩ := hP q (Finset.mem_insert_self _ _)
    set X₁ := Y ∪ ⋃ p ∈ P', box p (L * cellSide L m₀ m₁ j) with hX₁
    set X₂ := box q (L * cellSide L m₀ m₁ j) with hX₂
    have hvac : ∀ X : Set (CTorus d L N₁ m₁ K), ∀ z ∈ (Set.univ : Set _)ᶜ,
        OmegaComp Set.univ z ⊆ X ∨ Disjoint (OmegaComp Set.univ z) X :=
      fun X z hz => absurd (Set.mem_univ z) hz
    have h1 : DjMod m₀ j Set.univ X₁ := ⟨ih1, hvac X₁⟩
    have h2 : DjMod m₀ j Set.univ X₂ := ⟨isDj_box hq1, hvac X₂⟩
    have hcube : ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
        box t (cellSide L m₀ m₁ j) ⊆ X₁ ∩ X₂ ∩ Set.univ :=
      ⟨t, ht1, fun x hx => ⟨⟨Or.inl (ht2 hx).1, (ht2 hx).2⟩, Set.mem_univ _⟩⟩
    obtain ⟨h3, h4⟩ := G3_dcov h1 h2 hcube
    have hu : Y ∪ ⋃ p ∈ insert q P', box p (L * cellSide L m₀ m₁ j) = X₁ ∪ X₂ := by
      rw [Finset.set_biUnion_insert, hX₁, hX₂]
      ext x; simp only [Set.mem_union]; tauto
    rw [hu]
    refine ⟨h3.1, ?_⟩
    rw [dcovMod_of_subset (Set.subset_univ _), dcovMod_of_subset (Set.subset_univ _),
      dcovMod_of_subset (Set.subset_univ _)] at h4
    have hb := dcovMod_box_le (m₀ := m₀) (j := j) hq1
    rw [dcovMod_of_subset (Set.subset_univ _)] at hb
    rw [Finset.card_insert_of_notMem hq]
    push_cast
    linarith

open Classical in
theorem card_blocksOf_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ j Y) :
    ((blocksOf m₀ j Set.univ Y).card : ℝ) ≤ c1 d L * (1 + treeLenCovOne m₀ j Y) := by
  have h2 := G1_cellCount hN hj (Ω := Set.univ) (X := Y)
    ⟨hY, fun z hz => absurd (Set.mem_univ z) hz⟩
  rw [Set.inter_univ, dcovMod_of_subset (Set.subset_univ Y)] at h2
  refine le_trans ?_ h2
  have : (blocksOf m₀ j Set.univ Y).card ≤ cellCount (cellSide L m₀ m₁ j) Y := by
    unfold cellCount
    refine Finset.card_le_card_of_injOn (fun b => b.1) (fun b hb => ?_) (fun a _ b _ h => Subtype.ext h)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨b.2.1, mem_blocksOf.1 hb⟩
  exact_mod_cast this

open Classical in
/-- **The thickening of a domain by the cubes next to it.**  For `Y ∈ 𝒟_j` (`L ≥ 2`) there is
`Z ∈ 𝒟_j` containing `Y` and the `π_j`-cube of every site of `psiThick Y`, with
`d^cov_j(Z) ≤ d^cov_j(Y) + 2^d c₁ c_G (1 + d^cov_j(Y))`. -/
theorem thick_spec (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hL : 2 ≤ L) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ j Y) :
    ∃ Z, IsDj m₀ j Z ∧ Y ⊆ Z ∧
      (∀ y ∈ psiThick Y, box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆ Z) ∧
      treeLenCovOne m₀ j Z ≤ treeLenCovOne m₀ j Y +
        2 ^ d * c1 d L * (1 + treeLenCovOne m₀ j Y) * cG d L := by
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  set a := cellSide L m₀ m₁ j with hadef
  set P : Finset (CTorus d L N₁ m₁ K) :=
    ((blocksOf m₀ j Set.univ Y) ×ˢ (Finset.univ : Finset (Fin d → Bool))).image
      (fun x => pBase a x.1.1 x.2) with hP
  have hcellY : ∀ y ∈ Y, box (cbase a y) a ⊆ Y := by
    intro y hy
    obtain ⟨b, hb1, hb2, hb3⟩ := hY.2.1 y hy
    exact (cell_subset_cube ha ha0 hb1 hb2).trans hb3
  have hPprop : ∀ p ∈ P, Aligned a p ∧ ∃ t, Aligned a t ∧ box t a ⊆ Y ∩ box p (L * a) := by
    intro p hp
    obtain ⟨⟨c, o⟩, hmem, rfl⟩ := Finset.mem_image.1 hp
    have hc := (Finset.mem_product.1 hmem).1
    refine ⟨pBase_aligned ha c.2.1 o, c.1, c.2.1, fun x hx => ⟨mem_blocksOf.1 hc hx, ?_⟩⟩
    exact box_subset_of_offset hL (eq_pBase_add ha c.1 o) (fun μ => by split_ifs <;> omega) hx
  obtain ⟨hZ1, hZ2⟩ := thick_union (m₀ := m₀) (j := j) hY P hPprop
  refine ⟨_, hZ1, Set.subset_union_left, ?_, ?_⟩
  · intro y hy
    rcases hy with hy | ⟨x, hx, hxy⟩
    · exact (hcellY y hy).trans Set.subset_union_left
    · have hcb : (⟨cbase a x, aligned_cbase x, Set.subset_univ _⟩ :
          CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ) ∈
          blocksOf m₀ j Set.univ Y := mem_blocksOf.2 (hcellY x hx)
      obtain ⟨o, -, ho⟩ := exists_pBase_near hL ha ha0 (near_cbase_of_nbr ha ha0 (show Nbr x y from hxy))
      refine ho.trans (fun z hz => Or.inr ?_)
      refine Set.mem_iUnion₂.2 ⟨pBase a (cbase a x) o, Finset.mem_image.2 ⟨(⟨_, aligned_cbase x, Set.subset_univ _⟩, o), Finset.mem_product.2 ⟨hcb, Finset.mem_univ _⟩, rfl⟩, hz⟩
  · refine hZ2.trans ?_
    have hc := card_blocksOf_le hN hj hY
    have hcard : (P.card : ℝ) ≤ 2 ^ d * c1 d L * (1 + treeLenCovOne m₀ j Y) := by
      have h1 : P.card ≤ (blocksOf m₀ j Set.univ Y).card * 2 ^ d := by
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product]
        simp
      have h2 : (P.card : ℝ) ≤ ((blocksOf m₀ j Set.univ Y).card : ℝ) * 2 ^ d := by exact_mod_cast h1
      have h3 : (0 : ℝ) ≤ 2 ^ d := by positivity
      nlinarith
    have hg : 0 ≤ cG d L := by unfold cG; positivity
    nlinarith [mul_le_mul_of_nonneg_right hcard hg]

end Thick

end Balaban.Fluctuation
