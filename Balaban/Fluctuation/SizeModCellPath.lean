/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModStruct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Paths between cells of the fine torus, and unions of cells

Finite geometry on the fine torus `CTorus d L N₁ m₁ K`, with `a = cellSide L m₀ m₁ j`.  It
mentions no history and no fields.  This is package (2) of `notes/phase1/VMOD-38.md` §4.

* `cbase_succ`: a nearest-neighbour step moves a site into the same cell or into the next cell;
  `cbase_nbr`: the cells of nearest neighbours are equal or `CAdj`.
* `linked_cell_adj` (T1a): two adjacent cells (`CAdj a x y`, bases differing by `a` in one
  coordinate) have their corners linked at cost `1` (`a` bonds of weight `a⁻¹`) inside the union
  of the two cells.
* `linked_box_two`, `linked_box_site_corner` (T1b): two sites of an aligned box of side `L a`
  are linked inside the box at cost `d L`; in particular a site of the box and the corner of a
  cell inside the box.
* `linked_cell_corner` (T1c): a site of a cell is linked to the corner of the cell at cost `d`.
* `IsPiUnion` calculus: `isPiUnion_iff_cell`, `IsPiUnion.compl/inter/diff`,
  `IsPiPrimeUnion.isPiUnion`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

section Arith

variable {d n : ℕ} [NeZero n]

/-- A nearest-neighbour step in direction `μ` leaves a cell of side `a` or moves to the next one. -/
theorem cbase_succ {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a) (x : Torus d n) (μ : Fin d) :
    cbase a (x + Pi.single μ 1) = cbase a x ∨
      cbase a (x + Pi.single μ 1) = cbase a x + natT (Pi.single μ a) := by
  set b := cbase a x with hb
  have hbal : Aligned a b := aligned_cbase x
  set r : Fin d → ℕ := fun ν => (x ν).val % a with hr
  have hx : x = b + natT r := by
    rw [hb, cbase_eq_sub]; abel
  have hrlt : ∀ ν, r ν < a := fun ν => Nat.mod_lt _ ha0
  set w : Fin d → ℕ := r + Pi.single μ 1 with hw
  have hy : x + Pi.single μ 1 = b + natT w := by
    conv_lhs => rw [hx]
    rw [hw, natT_add, natT_single, add_assoc]
  rw [hy, cbase_add ha hbal]
  by_cases hra : r μ + 1 = a
  · right
    have : (fun ν => w ν - w ν % a) = Pi.single μ a := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp [hw, hra]
      · simp [hw, hν, Nat.mod_eq_of_lt (hrlt ν)]
    rw [this]
  · left
    have hlt : r μ + 1 < a := lt_of_le_of_ne (hrlt μ) hra
    have : (fun ν => w ν - w ν % a) = 0 := by
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp [hw, Nat.mod_eq_of_lt hlt]
      · simp [hw, hν, Nat.mod_eq_of_lt (hrlt ν)]
    rw [this, natT_zero, add_zero]

/-- Nearest-neighbour sites lie in the same cell or in `CAdj` cells. -/
theorem cbase_nbr {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a) {x y : Torus d n} (h : Nbr x y) :
    cbase a y = cbase a x ∨ CAdj a (cbase a x) (cbase a y) := by
  have key : ∀ (x : Torus d n) (μ : Fin d), cbase a (x + Pi.single μ 1) = cbase a x ∨
      CAdj a (cbase a x) (cbase a (x + Pi.single μ 1)) := by
    intro x μ
    rcases cbase_succ ha ha0 x μ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨μ, Or.inl h⟩
  obtain ⟨μ, h | h⟩ := h
  · rw [h]; exact key x μ
  · rw [h]
    rcases key y μ with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (by
        obtain ⟨ν, h1 | h1⟩ := h'
        · exact ⟨ν, Or.inr h1⟩
        · exact ⟨ν, Or.inl h1⟩)

omit [NeZero n] in
theorem CAdj.symm {a : ℕ} {x y : Torus d n} (h : CAdj a x y) : CAdj a y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

end Arith

section Links

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
theorem scaleW_eq (x y : CTorus d L N₁ m₁ K) :
    scaleW L m₀ m₁ j x y = ((cellSide L m₀ m₁ j : ℕ) : ℝ)⁻¹ := by
  unfold scaleW cellSide
  push_cast
  rw [show j + m₀ + m₁ = m₀ + m₁ + j by ring]

omit [NeZero N₁] [NeZero L] in
theorem scaleW_nonneg (x y : CTorus d L N₁ m₁ K) : 0 ≤ scaleW L m₀ m₁ j x y := by
  rw [scaleW_eq (m₀ := m₀) (j := j)]; positivity

omit [NeZero N₁] in
/-- **T1(a).**  The corners of two adjacent cells are linked at cost `1` (`a` bonds of weight
`a⁻¹`), inside the union of the two cells (any region containing both cells). -/
theorem linked_cell_adj {R : Set (CTorus d L N₁ m₁ K)} {x y : CTorus d L N₁ m₁ K}
    (hx : box x (cellSide L m₀ m₁ j) ⊆ R) (hy : box y (cellSide L m₀ m₁ j) ⊆ R)
    (h : CAdj (cellSide L m₀ m₁ j) x y) : Linked R (scaleW L m₀ m₁ j) 1 x y := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have step : ∀ {x y : CTorus d L N₁ m₁ K} {μ : Fin d}, box x a ⊆ R → y ∈ R →
      y = x + natT (Pi.single μ a) → Linked R (scaleW L m₀ m₁ j) 1 x y := by
    intro x y μ hx hy h
    have hR : ∀ w' : Fin d → ℕ, (∀ ν, w' ν ≤ (Pi.single μ a : Fin d → ℕ) ν) →
        x + natT w' ∈ R := by
      intro w' hw'
      by_cases hlt : w' μ < a
      · refine hx ⟨w', fun ν => ?_, rfl⟩
        by_cases hν : ν = μ
        · subst hν; exact hlt
        · have := hw' ν; simp [Pi.single_eq_of_ne hν] at this; omega
      · have hμ : w' μ = a := by
          have := hw' μ; simp at this; omega
        have : w' = Pi.single μ a := by
          funext ν
          by_cases hν : ν = μ
          · subst hν; simpa using hμ
          · have := hw' ν; simp [Pi.single_eq_of_ne hν] at this
            simp [Pi.single_eq_of_ne hν, this]
        rw [this, ← h]
        exact hy
    have hc : ∀ x ∈ R, ∀ y ∈ R, scaleW L m₀ m₁ j x y ≤ ((a : ℕ) : ℝ)⁻¹ :=
      fun x _ y _ => (scaleW_eq (m₀ := m₀) (j := j) x y).le
    have := linked_box (scaleW_nonneg (m₀ := m₀) (j := j)) x (Pi.single μ a) hR hc
    rw [← h] at this
    refine Covers.mono_c this (le_of_eq ?_)
    have hs : (∑ ν, (Pi.single μ a : Fin d → ℕ) ν) = a := by simp
    rw [hs]
    have : (a : ℝ) ≠ 0 := by positivity
    field_simp
  obtain ⟨μ, h | h⟩ := h
  · exact step hx (hy (mem_box_self y ha0)) h
  · exact (step hy (hx (mem_box_self x ha0)) h).symm

omit [NeZero N₁] [NeZero L] in
/-- Two sites of a box of side `s` inside `R` are linked at cost `d s c`, `c` a bound of the bond
weights: a monotone path from the coordinatewise minimum to each. -/
theorem linked_box_two {R : Set (CTorus d L N₁ m₁ K)} {ω : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ}
    (hω : ∀ x y, 0 ≤ ω x y) (b : CTorus d L N₁ m₁ K) (s : ℕ) {c : ℝ}
    (hbox : box b s ⊆ R) (hc : ∀ x ∈ R, ∀ y ∈ R, ω x y ≤ c) {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ box b s) (hy : y ∈ box b s) : Linked R ω (d * s * c) x y := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hxR : b + natT u ∈ R := hbox ⟨u, hu, rfl⟩
  have hc0 : 0 ≤ c := (hω _ _).trans (hc _ hxR _ hxR)
  set m : Fin d → ℕ := fun μ => min (u μ) (v μ) with hm
  have hmu : ∀ μ, m μ ≤ u μ := fun μ => min_le_left _ _
  have hmv : ∀ μ, m μ ≤ v μ := fun μ => min_le_right _ _
  have hmem : ∀ w' : Fin d → ℕ, (∀ μ, w' μ ≤ u μ ∨ w' μ ≤ v μ) → (∀ μ, w' μ < s) →
      b + natT w' ∈ R := fun w' _ hw => hbox ⟨w', hw, rfl⟩
  have h1 : Linked R ω (((∑ μ, (u - m) μ : ℕ) : ℝ) * c) (b + natT m) (b + natT u) := by
    have := linked_box hω (b + natT m) (u - m) (c := c) ?_ hc
    · have e : b + natT m + natT (u - m) = b + natT u := by
        rw [add_assoc, ← natT_add]
        congr 2
        funext μ
        simp [Nat.add_sub_cancel' (hmu μ)]
      rwa [e] at this
    · intro w' hw'
      rw [add_assoc, ← natT_add]
      refine hbox ⟨m + w', fun μ => ?_, rfl⟩
      have := hw' μ
      simp only [Pi.sub_apply] at this
      have := hu μ
      simp only [Pi.add_apply]
      have := hmu μ
      have := hw' μ
      simp only [Pi.sub_apply] at this
      omega
  have h2 : Linked R ω (((∑ μ, (v - m) μ : ℕ) : ℝ) * c) (b + natT m) (b + natT v) := by
    have := linked_box hω (b + natT m) (v - m) (c := c) ?_ hc
    · have e : b + natT m + natT (v - m) = b + natT v := by
        rw [add_assoc, ← natT_add]
        congr 2
        funext μ
        simp [Nat.add_sub_cancel' (hmv μ)]
      rwa [e] at this
    · intro w' hw'
      rw [add_assoc, ← natT_add]
      refine hbox ⟨m + w', fun μ => ?_, rfl⟩
      have := hv μ
      simp only [Pi.add_apply]
      have := hmv μ
      have := hw' μ
      simp only [Pi.sub_apply] at this
      omega
  have h3 := Linked.trans hω h1.symm h2
  refine Covers.mono_c h3 ?_
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ hc0
  have hsum : (∑ μ, (u - m) μ) + ∑ μ, (v - m) μ ≤ d * s := by
    rw [← Finset.sum_add_distrib]
    calc ∑ μ, ((u - m) μ + (v - m) μ) ≤ ∑ _μ : Fin d, s := by
          refine Finset.sum_le_sum fun μ _ => ?_
          have := hu μ; have := hv μ
          simp only [Pi.sub_apply, hm]
          omega
      _ = d * s := by simp
  exact_mod_cast hsum

omit [NeZero N₁] in
/-- **T1(b).**  A site `w` of an aligned box `b₀` of side `L a`, contained in `R`, is linked to
any site `p` of the box (in particular to the corner of a cell contained in the box) at cost
`d L`, i.e. with at most `d L a` bonds. -/
theorem linked_box_site_corner {R : Set (CTorus d L N₁ m₁ K)} (b₀ : CTorus d L N₁ m₁ K)
    (hbox : box b₀ (L * cellSide L m₀ m₁ j) ⊆ R) {w p : CTorus d L N₁ m₁ K}
    (hw : w ∈ box b₀ (L * cellSide L m₀ m₁ j)) (hp : p ∈ box b₀ (L * cellSide L m₀ m₁ j)) :
    Linked R (scaleW L m₀ m₁ j) (d * L) w p := by
  have ha0 : (0 : ℝ) < ((cellSide L m₀ m₁ j : ℕ) : ℝ) := by exact_mod_cast cellSide_pos m₀ m₁ j
  have := linked_box_two (scaleW_nonneg (m₀ := m₀) (j := j)) b₀ (L * cellSide L m₀ m₁ j) hbox
    (c := ((cellSide L m₀ m₁ j : ℕ) : ℝ)⁻¹)
    (fun x _ y _ => (scaleW_eq (m₀ := m₀) (j := j) x y).le) hw hp
  refine Covers.mono_c this (le_of_eq ?_)
  push_cast
  field_simp

omit [NeZero N₁] in
/-- **T1(c).**  A site of a cell contained in `R` is linked to the corner of the cell at cost
`d`, i.e. with at most `d a` bonds. -/
theorem linked_cell_corner {R : Set (CTorus d L N₁ m₁ K)} {b x : CTorus d L N₁ m₁ K}
    (hbox : box b (cellSide L m₀ m₁ j) ⊆ R) (hx : x ∈ box b (cellSide L m₀ m₁ j)) :
    Linked R (scaleW L m₀ m₁ j) d b x := by
  have ha0 : (0 : ℝ) < ((cellSide L m₀ m₁ j : ℕ) : ℝ) := by exact_mod_cast cellSide_pos m₀ m₁ j
  have := linked_corner (scaleW_nonneg (m₀ := m₀) (j := j)) b (cellSide L m₀ m₁ j) hbox
    (c := ((cellSide L m₀ m₁ j : ℕ) : ℝ)⁻¹)
    (fun x _ y _ => (scaleW_eq (m₀ := m₀) (j := j) x y).le) hx
  refine Covers.mono_c this (le_of_eq ?_)
  field_simp

omit [NeZero N₁] [NeZero L] in
/-- A linked pair is joined by nearest-neighbour steps inside the region. -/
theorem siteReach_of_linked {R : Set (CTorus d L N₁ m₁ K)}
    {ω : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ} {c : ℝ} {x y : CTorus d L N₁ m₁ K}
    (h : Linked R ω c x y) :
    Relation.ReflTransGen (fun u v => u ∈ R ∧ v ∈ R ∧ Nbr u v) x y := by
  obtain ⟨W, E, ⟨-, hE, hconn⟩, hWR, hA, -⟩ := h
  have hx : x ∈ W := hA (by simp)
  have hy : y ∈ W := hA (by simp)
  refine Relation.ReflTransGen.mono ?_ _ _ (hconn x hx y hy)
  intro u v huv
  rcases huv with h | h
  · obtain ⟨h1, h2, h3⟩ := hE _ h
    exact ⟨hWR h1, hWR h2, h3⟩
  · obtain ⟨h1, h2, h3⟩ := hE _ h
    exact ⟨hWR h2, hWR h1, h3.symm⟩

end Links

section Cells

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- A set is a union of cells exactly when it contains the whole cell of each of its sites. -/
theorem isPiUnion_iff_cell (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {S : Set (CTorus d L N₁ m₁ K)} :
    IsPiUnion m₀ j S ↔ ∀ z ∈ S, box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ S := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  constructor
  · intro h z hz
    obtain ⟨b, hb, hzb, hsub⟩ := h z hz
    rw [cbase_eq_of_mem_box hdvd hb hzb]
    exact hsub
  · intro h z hz
    exact ⟨_, aligned_cbase z, mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z, h z hz⟩

theorem IsPiUnion.cell (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {S : Set (CTorus d L N₁ m₁ K)}
    (h : IsPiUnion m₀ j S) {z : CTorus d L N₁ m₁ K} (hz : z ∈ S) :
    box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ S :=
  (isPiUnion_iff_cell hN hj).1 h z hz

/-- The complement of a union of cells is a union of cells. -/
theorem IsPiUnion.compl (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {S : Set (CTorus d L N₁ m₁ K)}
    (h : IsPiUnion m₀ j S) : IsPiUnion m₀ j Sᶜ := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  refine (isPiUnion_iff_cell hN hj).2 fun z hz y hy hyS => hz ?_
  have e : cbase (cellSide L m₀ m₁ j) y = cbase (cellSide L m₀ m₁ j) z :=
    cbase_eq_of_mem_box hdvd (aligned_cbase z) hy
  have := h.cell hN hj hyS
  rw [e] at this
  exact this (mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z)

/-- The intersection of two unions of cells is a union of cells. -/
theorem IsPiUnion.inter (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {S T : Set (CTorus d L N₁ m₁ K)}
    (hS : IsPiUnion m₀ j S) (hT : IsPiUnion m₀ j T) : IsPiUnion m₀ j (S ∩ T) :=
  (isPiUnion_iff_cell hN hj).2 fun _ hz =>
    Set.subset_inter (hS.cell hN hj hz.1) (hT.cell hN hj hz.2)

/-- A union of `π'_j`-cubes is a union of `π_j`-cubes. -/
theorem IsPiPrimeUnion.isPiUnion (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {X : Set (CTorus d L N₁ m₁ K)}
    (h : IsPiPrimeUnion m₀ j X) : IsPiUnion m₀ j X := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  refine (isPiUnion_iff_cell hN hj).2 fun z hz => ?_
  obtain ⟨b, hb, hzb, hsub⟩ := h z hz
  exact (cell_subset_cube hdvd ha0 hb hzb).trans hsub

theorem cbase_mem_cellsIn (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {S : Set (CTorus d L N₁ m₁ K)}
    (h : IsPiUnion m₀ j S) {z : CTorus d L N₁ m₁ K} (hz : z ∈ S) :
    cbase (cellSide L m₀ m₁ j) z ∈ cellsIn m₀ j S :=
  mem_cellsIn.2 ⟨aligned_cbase z, h.cell hN hj hz⟩

theorem mem_of_mem_cellsIn {S : Set (CTorus d L N₁ m₁ K)} {t : CTorus d L N₁ m₁ K}
    (h : t ∈ cellsIn (L := L) m₀ j S) : t ∈ S :=
  (mem_cellsIn.1 h).2 (mem_box_self t (cellSide_pos (L := L) m₀ m₁ j))

end Cells

end Balaban.Fluctuation
