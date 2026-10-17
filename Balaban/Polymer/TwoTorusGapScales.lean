/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The torus margin at the scales below the last one does not need a floor in `L`

The landed two-torus transport theorems of one step (`TwoTorusEv`, `TwoTorusCoef`, `TwoTorusDet`,
`TwoTorusDecBg`, `TwoTorusDecSol`, `TwoTorusDecCov`) ask for margins of the form
`2 R + 5 L a_K < n` (the cover `X₁` and the hulls of `π'_K`-cubes, of side `L a_K`) and
`4 R + 12 L^(K+m₁) + 7 L^K + 5 < n` (background, fluctuation, covariance and determinant), where
`a_K = cellSide L m₀ m₁ K` and `n` is the side of the torus.  The ledger records their sum as the
additive slack `19 L a_K`, which depends on `L`.

Every domain of a step is a union of `π'_K`-cubes, so a nonempty read region `X₁` contains a box of
side `L a_K`.  If it lies in the centred box of radius `R`, then `L a_K ≤ 2 R + 1`
(`width_le_of_box_subset_inBox`).  Hence all the margins follow from the single condition
`20 R + 20 < n`, which does not involve `L` (`gapMargins_of_width`), and
`evTerm_boxMap_of_width` is `evTerm_boxMap_of_eq` under this condition.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer

/-- A box of side `s` of the torus of side `n` inside the centred box of radius `r` has at most
`2 r + 1` points per side: any `t ≤ min s n` satisfies `t ≤ 2 r + 1`. -/
theorem width_le_of_box_subset_inBox {d n : ℕ} [NeZero n] (hd : 0 < d) {b : Torus d n}
    {s r t : ℕ} (hts : t ≤ s) (htn : t ≤ n)
    (hbox : ∀ x ∈ box b s, InBox d r n x) : t ≤ 2 * r + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · omega
  set μ₀ : Fin d := ⟨0, hd⟩ with hμ₀
  let f : ℕ → ℤ := fun j => (b μ₀ + (j : ZMod n)).valMinAbs
  have hmaps : ∀ j ∈ Finset.range t, f j ∈ Finset.Icc (-(r : ℤ)) r := by
    intro j hj
    have hj' : j < t := Finset.mem_range.1 hj
    have hmem : b + natT (n := n) (Pi.single μ₀ j) ∈ box b s := by
      refine ⟨Pi.single μ₀ j, fun μ => ?_, rfl⟩
      by_cases h : μ = μ₀
      · subst h; simp; omega
      · simp [h]; omega
    have := hbox _ hmem μ₀
    have h2 : (b + natT (n := n) (Pi.single μ₀ j)) μ₀ = b μ₀ + (j : ZMod n) := by simp [natT]
    rw [h2] at this
    exact Finset.mem_Icc.2 (abs_le.1 this)
  have hinj : Set.InjOn f (Finset.range t : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < t := Finset.mem_range.1 hi
    have hj' : j < t := Finset.mem_range.1 hj
    have h1 : b μ₀ + (i : ZMod n) = b μ₀ + (j : ZMod n) := ZMod.injective_valMinAbs hij
    have h2 : (i : ZMod n) = (j : ZMod n) := add_left_cancel h1
    have h3 := (ZMod.natCast_eq_natCast_iff' i j n).1 h2
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range, Int.card_Icc] at hc
  omega

/-- **The margins of the step transport theorems from one condition without `L`.**  If a read
region of radius `R` contains a box of side `L a_K` (`L a_K ≤ 2 R + 1`) and `20 R + 20 < n`, then
the four margins used by the landed theorems hold (`K` is the top level, `m₀, m₁ ≥ 1`):
the cover margin `2 R + 5 L a_K < n`, the margin `4 R + 12 L^(K+m₁) + 7 L^K + 5 < n`, the margin
of the fluctuation cover, and the hull margin `2 (R + 2 L a_K) + L a_K < n`. -/
theorem gapMargins_of_width {L m₀ m₁ K R n : ℕ} (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hw : L * cellSide L m₀ m₁ K ≤ 2 * R + 1) (hn : 20 * R + 20 < n) :
    2 * R + 5 * (L * cellSide L m₀ m₁ K) < n ∧
    4 * R + 12 * L ^ (K + m₁) + 7 * L ^ K + 5 < n ∧
    2 * (R + (3 * L ^ (K + m₁) + 3 * L ^ (K + 2)) + L ^ (K + m₁)) +
      5 * (L * cellSide L 0 m₁ K) < n ∧
    2 * (R + 2 * (L * cellSide L m₀ m₁ K)) + L * cellSide L m₀ m₁ K < n := by
  have hLpos : 0 < L := by omega
  have ha : cellSide L m₀ m₁ K = L ^ m₀ * L ^ (K + m₁) := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  have hb : cellSide L 0 m₁ K = L ^ (K + m₁) := by unfold cellSide; congr 1
  have hLm : L ≤ L ^ m₀ := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ m₀ := Nat.pow_le_pow_right hLpos hm₀
  have hq : L ^ K ≤ L ^ (K + m₁) := Nat.pow_le_pow_right hLpos (by omega)
  have hK2 : L ^ (K + 2) ≤ cellSide L m₀ m₁ K := by
    unfold cellSide; exact Nat.pow_le_pow_right hLpos (by omega)
  set a := cellSide L m₀ m₁ K with hadef
  set p := L ^ (K + m₁) with hpdef
  have hLp : L * p ≤ a := by rw [ha]; exact Nat.mul_le_mul_right _ hLm
  have h2p : 2 * p ≤ L * p := Nat.mul_le_mul_right _ hL
  have h2a : 2 * a ≤ L * a := Nat.mul_le_mul_right _ hL
  rw [hb]
  refine ⟨by omega, by omega, ?_, by omega⟩
  have : L * p ≤ a := hLp
  omega

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

/-- **`evTerm_boxMap_of_eq` with a margin that does not involve `L`.**  The read region `X₁`
(a nonempty union of `π'_{k+1}`-cubes: it contains a box of side `L a_{k+1}`) and `Y` lie in the
centred box of radius `R`, and `20 R + 20 < N₁ L^m₁ L^(k+1), N₁' L^m₁ L^(k+1)`. -/
theorem evTerm_boxMap_of_width {U U' : Type*} {m₀ R : ℕ} (hd : 0 < d) (hL : 2 ≤ L)
    (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hbox : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆ X₁)
    (hX : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    {S' : Set (CTorus d L N₁' m₁ (k + 1))} (hS' : S' = bm '' X₁)
    {F : U → (ParIdx (GA) X₁ → ℂ) → ℂ} {F' : U' → (ParIdx (GB) S' → ℂ) → ℂ} {u : U} {u' : U'}
    (hcoef : ∀ C ∈ connFams (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ Y,
      ∀ C' : Finset (ParIdx (GB) S'),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id bm i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id bm i.1.1) →
        coef (F' u') C' = coef (F u) C) :
    evTerm (fun i : ParIdx (GB) S' => i.1.1) (GB) m₀ S' F' (bm '' Y) u' =
      evTerm (fun i : ParIdx (GA) X₁ => i.1.1) (GA) m₀ X₁ F Y u := by
  obtain ⟨b, hb⟩ := hbox
  have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
    (b := b) (s := L * cellSide L m₀ m₁ (k + 1)) (r := R)
    (t := min (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
    (min_le_left _ _) (min_le_right _ _) (fun x hx => hX x (hb hx))
  have hw : L * cellSide L m₀ m₁ (k + 1) ≤ 2 * R + 1 := by
    rcases min_choice (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
    · rwa [h] at hw0
    · rw [h] at hw0; omega
  obtain ⟨h1, -⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn
  obtain ⟨h1', -⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn'
  exact evTerm_boxMap_of_eq hN hN' h1 h1' hX hY hS' F F' u u' hcoef

end Balaban.Polymer.TwoTorusStep
