/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModAllDefs
public import Balaban.Fluctuation.SizeModG1
public import Balaban.Fluctuation.SizeModExtend
public import Balaban.Inhabited.SizeModExtendWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Upper comparison of the all-eligible size with the landed modular size (VMOD-43 (2.1))

Under `DjMod m₀ j Ω X`, `IsPiUnion m₀ j Ω`, `j ≤ K` and `L^{m₀} ∣ N₁` (the hypotheses of
`G1_cellCount` and of the piece property of `Ω`):

`dcovModAll ≤ (1 + 2 d L c₁) · dcovMod + 2 d L c₁`, `c₁ = [3 (2L - 1)]^d` (`Fluctuation.c1`).

The proof is that of `Localization.treeLenAll_le`: take an optimal chosen-cover witness, join each
active cell (a `π_j`-cell contained in `X ∩ Ω`) to the witness by a path inside a covering chosen
box (cost at most `2 d L` per cell, `linked_box_pair`), and use that every eligible box contains
an active cell.  The number of active cells is bounded by `G1_cellCount`.

Together with `dcovMod_le_dcovModAll` (`SizeModAllDefs.lean`) this is the two-sided comparison of
the two fine sizes.  The comparison with the papers' continuum size, the aligned-lift
identification and the component compatibility are NOT proved here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- Adding a finite set of points, each linked at cost `ρ` to the structure. -/
theorem covers_add_points {R : Set (CTorus d L N₁ m₁ K)}
    {ω : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ} (hω : ∀ x y, 0 ≤ ω x y)
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hW : ConnStruct W E) (hWR : ↑W ⊆ R) {ρ : ℝ}
    (S : Finset (CTorus d L N₁ m₁ K))
    (hlink : ∀ c ∈ S, ∃ p ∈ W, Linked R ω ρ p c) :
    Covers R ω (bondCost ω E + S.card * ρ) (W ∪ S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨W, E, hW, hWR, by simp, by simp⟩
  | insert b S hb ih =>
    obtain ⟨p, hpW, hl⟩ := hlink b (Finset.mem_insert_self _ _)
    have h1 := ih fun c hc => hlink c (Finset.mem_insert_of_mem hc)
    have h2 := Covers.join hω h1 hl ⟨p, Finset.mem_union_left _ hpW, by simp⟩
    refine (Covers.mono_A h2 ?_).mono_c (le_of_eq ?_)
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    · rw [Finset.card_insert_of_notMem hb]; push_cast; ring

/-- An eligible box contains an active cell: for `z ∈ box b (L a) ∩ X ∩ Ω`, the cell of `z` lies
in `X ∩ Ω` and in the box. -/
theorem active_cell_of_eligible (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω X : Set (CTorus d L N₁ m₁ K)}
    (hXU : IsPiPrimeUnion m₀ j X) (hΩ : IsPiUnion m₀ j Ω)
    {b : CTorus d L N₁ m₁ K} (hb : Aligned (cellSide L m₀ m₁ j) b)
    (hne : (box b (L * cellSide L m₀ m₁ j) ∩ (X ∩ Ω)).Nonempty) :
    ∃ c, Aligned (cellSide L m₀ m₁ j) c ∧ box c (cellSide L m₀ m₁ j) ⊆ X ∩ Ω ∧
      box c (cellSide L m₀ m₁ j) ⊆ box b (L * cellSide L m₀ m₁ j) := by
  obtain ⟨z, hzb, hzX, hzΩ⟩ := hne
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  obtain ⟨b', hb'1, hb'2, hb'3⟩ := hXU z hzX
  obtain ⟨b'', hb''1, hb''2, hb''3⟩ := hΩ z hzΩ
  have hcb : cbase (cellSide L m₀ m₁ j) z = b'' := cbase_eq_of_mem_box hdvd hb''1 hb''2
  refine ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, ?_, cell_subset_cube hdvd ha0 hb hzb⟩
  exact Set.subset_inter ((cell_subset_cube hdvd ha0 hb'1 hb'2).trans hb'3) (hcb ▸ hb''3)

/-- **Existence of a short extension** (VMOD-43 (2.1)): an admissible structure of the
all-eligible size of cost at most `(1 + 2 d L c₁) dcovMod + 2 d L c₁`. -/
theorem exists_modAdmissibleAll_cost_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : DjMod m₀ j Ω X) (hΩ : IsPiUnion m₀ j Ω) :
    ∃ W E, ModAdmissibleAll m₀ j Ω X W E ∧
      bondCost (scaleW L m₀ m₁ j) E ≤
        (1 + 2 * d * L * c1 d L) * dcovMod m₀ j Ω X + 2 * d * L * c1 d L := by
  classical
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have haR : (a : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
  have hω : ∀ x y : CTorus d L N₁ m₁ K, 0 ≤ scaleW L m₀ m₁ j x y := fun x y => by
    unfold scaleW; positivity
  obtain ⟨𝒦, W, E, hE, hcost⟩ :=
    exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) hX.1)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hE
  set ρ : ℝ := 2 * d * L with hρ
  set S : Finset (CTorus d L N₁ m₁ K) :=
    Finset.univ.filter fun c => Aligned a c ∧ box c a ⊆ X ∩ Ω with hS
  have hcard : (S.card : ℝ) ≤ c1 d L * (1 + dcovMod m₀ j Ω X) := by
    have := G1_cellCount hN hj hX
    unfold cellCount at this
    exact this
  -- every active cell is linked to the witness
  have hlink : ∀ c ∈ S, ∃ p ∈ W, Linked X (scaleW L m₀ m₁ j) ρ p c := by
    intro c hc
    obtain ⟨hcal, hcbox⟩ := (Finset.mem_filter.1 hc).2
    have hcXΩ : c ∈ X ∩ Ω := hcbox (mem_box_self c ha0)
    obtain ⟨b, hb, hcb⟩ := Set.mem_iUnion₂.1 (h2 hcXΩ)
    obtain ⟨p, hpW, hpb⟩ := h5 b hb
    refine ⟨p, hpW, ?_⟩
    have := linked_box_pair (R := X) (ω := scaleW L m₀ m₁ j) hω b (L * a)
      (c := ((a : ℝ))⁻¹) (h1 b hb).2 (fun x y _ _ => by
        unfold scaleW; rw [haR]) hpb hcb
    refine Covers.mono_c this (le_of_eq ?_)
    rw [hρ]; push_cast; field_simp
  obtain ⟨W', E', g1, g2, g3, g4⟩ := covers_add_points hω h3 h4 S hlink
  have hΔ := dcovMod_nonneg (m₀ := m₀) (j := j) Ω X
  refine ⟨W', E', ⟨g1, g2, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨hbal, hne⟩ := hb
    obtain ⟨c, hcal, hcXΩ, hcb⟩ := active_cell_of_eligible hN hj hX.1.2.1 hΩ hbal hne
    have hcS : c ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hcal, hcXΩ⟩
    exact ⟨c, g3 (Finset.mem_union_right _ hcS), hcb (mem_box_self c ha0)⟩
  · rw [hcost] at *
    have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
    have := mul_le_mul_of_nonneg_right hcard hρ0
    nlinarith [this]

/-- **Upper comparison** (VMOD-43 (2.1)): `D_A ≤ (1 + 2 d L c₁) Δ + 2 d L c₁`. -/
theorem dcovModAll_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω X : Set (CTorus d L N₁ m₁ K)}
    (hX : DjMod m₀ j Ω X) (hΩ : IsPiUnion m₀ j Ω) :
    dcovModAll m₀ j Ω X ≤
      (1 + 2 * d * L * c1 d L) * dcovMod m₀ j Ω X + 2 * d * L * c1 d L := by
  obtain ⟨W, E, h, hc⟩ := exists_modAdmissibleAll_cost_le hN hj hX hΩ
  exact (dcovModAll_le_of_admissible h).trans hc

/-- **Two-sided comparison** of the two fine sizes. -/
theorem dcovMod_le_dcovModAll_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : DjMod m₀ j Ω X) (hΩ : IsPiUnion m₀ j Ω) :
    dcovMod m₀ j Ω X ≤ dcovModAll m₀ j Ω X ∧
      dcovModAll m₀ j Ω X ≤
        (1 + 2 * d * L * c1 d L) * dcovMod m₀ j Ω X + 2 * d * L * c1 d L :=
  ⟨dcovMod_le_dcovModAll hX.1, dcovModAll_le hN hj hX hΩ⟩

/-- Finiteness (also `dcovModAllE_ne_top_of_IsDj`, which needs no further hypothesis). -/
theorem dcovModAllE_ne_top (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω X : Set (CTorus d L N₁ m₁ K)}
    (hX : DjMod m₀ j Ω X) (hΩ : IsPiUnion m₀ j Ω) : dcovModAllE m₀ j Ω X ≠ ⊤ := by
  obtain ⟨W, E, h, -⟩ := exists_modAdmissibleAll_cost_le hN hj hX hΩ
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (dcovModAllE_le_of_admissible h)

/-- **Non-vacuity**: for every choice of parameters with `L^{m₀} ∣ N₁` and `j ≤ K`, the label
`X = univ` with `Ω = univ` satisfies all hypotheses, so that the lower and upper comparisons
hold.  Here every aligned box is eligible and lies in `X`, so the eligible family is itself a
chosen family and no eligible box crosses the boundary of the label; an instance with a box
crossing `∂X` is not given. -/
theorem exists_compare_instance (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) :
    ∃ Ω X : Set (CTorus d L N₁ m₁ K), DjMod m₀ j Ω X ∧ IsPiUnion m₀ j Ω ∧
      dcovModE m₀ j Ω X ≤ dcovModAllE m₀ j Ω X ∧ dcovModAllE m₀ j Ω X ≠ ⊤ ∧
      dcovModAll m₀ j Ω X ≤
        (1 + 2 * d * L * c1 d L) * dcovMod m₀ j Ω X + 2 * d * L * c1 d L := by
  have hX : DjMod m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) Set.univ :=
    ⟨isDj_univ, fun z hz => absurd (Set.mem_univ z) hz⟩
  exact ⟨Set.univ, Set.univ, hX, isPiUnion_univ, dcovModE_le_dcovModAllE isDj_univ,
    dcovModAllE_ne_top hN hj hX isPiUnion_univ, dcovModAll_le hN hj hX isPiUnion_univ⟩

end Balaban.Fluctuation
