/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModEntropy
public import Balaban.Fluctuation.SizeModCellPath
public import Balaban.Fluctuation.SizeModUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rooted entropy at a hole component

`G2_X` roots the labels `X ∈ 𝒟_j(mod Ω^c)` at a cell of `Ω`.  A hole component `H` (a union of
whole nearest-neighbour components of `Ω^c`) has no cell of `Ω` in it, but a label `X ⊇ H` that
meets `Ω` leaves `H` through an active cell next to `H`:

* `exists_active_adj_hole` (the exit cell): `X ∈ 𝒟_j(mod Ω^c)`, `H ⊆ X`, `X ∩ Ω ≠ ∅` give a
  cell of `X ∩ Ω` that is cell-adjacent (`CAdj`) to the cell of a site of `H`;
* `sum_exp_le_of_roots`: if every label of a family contains one of finitely many root cells of
  `Ω`, the `G2_X` sum over the family is at most `#roots · K₀`;
* `sum_exp_le_of_hole`: the sum over labels `X ⊇ H` meeting `Ω` is at most
  `2 d · #(cells of H) · K₀`.

These are counting lemmas on the landed cover size.  The gas estimate, the retained-hole bridge
and everything analytic about the renormalization operation are not proved here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- **The exit cell.**  Let `Ω` be a union of `π_j`-cells and `H ⊆ Ω^c` closed under
nearest-neighbour steps into `Ω^c` (a union of whole components of `Ω^c`).  If
`X ∈ 𝒟_j(mod Ω^c)` contains `H ≠ ∅` and meets `Ω`, then some `π_j`-cell contained in `X ∩ Ω` is
cell-adjacent to the cell of a site of `H`. -/
theorem exists_active_adj_hole (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Ω X H : Set (CTorus d L N₁ m₁ K)} (hΩ : IsPiUnion m₀ j Ω) (hX : DjMod m₀ j Ω X)
    (hHΩ : H ⊆ Ωᶜ) (hHcl : ∀ y ∈ H, ∀ z, z ∉ Ω → Nbr y z → z ∈ H) (hHX : H ⊆ X)
    (hHne : H.Nonempty) (hXΩ : (X ∩ Ω).Nonempty) :
    ∃ u ∈ H, ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
      box t (cellSide L m₀ m₁ j) ⊆ X ∩ Ω ∧ CAdj (cellSide L m₀ m₁ j) (cbase (cellSide L m₀ m₁ j) u) t := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  obtain ⟨y, hy⟩ := hHne
  obtain ⟨x, hxX, hxΩ⟩ := hXΩ
  have hpath := hX.1.2.2 y (hHX hy) x hxX
  have key : ∀ b, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ Nbr u v) y b →
      b ∈ H ∨ ∃ u ∈ H, ∃ v ∈ X, v ∉ H ∧ Nbr u v := by
    intro b hb
    induction hb with
    | refl => exact Or.inl hy
    | @tail b' c' _ hbc ih =>
      rcases ih with h | h
      · by_cases hc : c' ∈ H
        · exact Or.inl hc
        · exact Or.inr ⟨b', h, c', hbc.2.1, hc, hbc.2.2⟩
      · exact Or.inr h
  rcases key x hpath with h | ⟨u, hu, v, hvX, hvH, huv⟩
  · exact absurd hxΩ (hHΩ h)
  have hvΩ : v ∈ Ω := by
    by_contra hv
    exact hvH (hHcl u hu v hv huv)
  have hcellΩ : box (cbase (cellSide L m₀ m₁ j) v) (cellSide L m₀ m₁ j) ⊆ Ω := by
    obtain ⟨b, hb1, hb2, hb3⟩ := hΩ v hvΩ
    rw [cbase_eq_of_mem_box hdvd hb1 hb2]; exact hb3
  have hcellX : box (cbase (cellSide L m₀ m₁ j) v) (cellSide L m₀ m₁ j) ⊆ X := by
    obtain ⟨b, hb1, hb2, hb3⟩ := hX.1.2.1 v hvX
    exact (cell_subset_cube hdvd ha0 hb1 hb2).trans hb3
  refine ⟨u, hu, cbase (cellSide L m₀ m₁ j) v, aligned_cbase v, fun z hz => ⟨hcellX hz, hcellΩ hz⟩, ?_⟩
  rcases cbase_nbr hdvd ha0 huv with h | h
  · exfalso
    have : u ∈ box (cbase (cellSide L m₀ m₁ j) v) (cellSide L m₀ m₁ j) := by
      rw [h]; exact mem_box_cbase ha0 u
    exact hHΩ hu (hcellΩ this)
  · exact h

/-- The sums over a family all of whose members contain one of finitely many root cells. -/
theorem sum_exp_le_of_roots (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Ω : Set (CTorus d L N₁ m₁ K)} (hΩ : IsPiUnion m₀ j Ω) (Rt : Finset (CTorus d L N₁ m₁ K))
    (hRt : ∀ r ∈ Rt, Aligned (cellSide L m₀ m₁ j) r ∧ box r (cellSide L m₀ m₁ j) ⊆ Ω)
    {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) (P : Set (CTorus d L N₁ m₁ K) → Prop)
    (hP : ∀ X, DjMod m₀ j Ω X → P X → ∃ r ∈ Rt, box r (cellSide L m₀ m₁ j) ⊆ X) :
    (open Classical in
      ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) => DjMod m₀ j Ω X ∧ P X),
        Real.exp (-κ₀ * dcovMod m₀ j Ω X)) ≤ Rt.card * K0 d L κ₀ := by
  classical
  set S := Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) => DjMod m₀ j Ω X ∧ P X) with hS
  set f : Set (CTorus d L N₁ m₁ K) → ℝ := fun X => Real.exp (-κ₀ * dcovMod m₀ j Ω X) with hf
  have hf0 : ∀ X, 0 ≤ f X := fun X => (Real.exp_pos _).le
  have h1 : ∀ X ∈ S, f X ≤ ∑ r ∈ Rt, if box r (cellSide L m₀ m₁ j) ⊆ X then f X else 0 := by
    intro X hX
    obtain ⟨hD, hPX⟩ := (Finset.mem_filter.1 hX).2
    obtain ⟨r, hr, hrX⟩ := hP X hD hPX
    calc f X = (if box r (cellSide L m₀ m₁ j) ⊆ X then f X else 0) := by simp [hrX]
      _ ≤ _ := Finset.single_le_sum (f := fun r => if box r (cellSide L m₀ m₁ j) ⊆ X then f X else 0)
          (fun r _ => by split_ifs <;> simp [hf0]) hr
  have h2 : ∑ X ∈ S, f X ≤ ∑ r ∈ Rt, ∑ X ∈ S, if box r (cellSide L m₀ m₁ j) ⊆ X then f X else 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_le_sum h1
  have h3 : ∀ r ∈ Rt, (∑ X ∈ S, if box r (cellSide L m₀ m₁ j) ⊆ X then f X else 0) ≤ K0 d L κ₀ := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hRt r hr
    rw [← Finset.sum_filter]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.filter
      (fun X : Set (CTorus d L N₁ m₁ K) => DjMod m₀ j Ω X ∧ box r (cellSide L m₀ m₁ j) ⊆ X)) ?_
      (fun X _ _ => hf0 X)) (G2_X hN hj hΩ hr1 hr2 hκ)
    intro X hX
    obtain ⟨hX1, hX2⟩ := Finset.mem_filter.1 hX
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hX1).2.1, hX2⟩
  calc ∑ X ∈ S, f X ≤ _ := h2
    _ ≤ ∑ _r ∈ Rt, K0 d L κ₀ := Finset.sum_le_sum h3
    _ = _ := by simp

open Classical in
/-- The bases of the `π_j`-cells meeting `H` (a literal helper set). -/
noncomputable def holeBases (m₀ j : ℕ) (H : Set (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun t => ∃ y ∈ H, cbase (cellSide L m₀ m₁ j) y = t

/-- The at most `2 d` cells adjacent to the cell with base `s`. -/
noncomputable def adjCells (m₀ j : ℕ) (s : CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  (Finset.univ : Finset (Fin d × Bool)).image fun p =>
    if p.2 then s + natT (Pi.single p.1 (cellSide L m₀ m₁ j))
    else s - natT (Pi.single p.1 (cellSide L m₀ m₁ j))

omit [NeZero N₁] [NeZero L] in
theorem card_adjCells_le (s : CTorus d L N₁ m₁ K) : (adjCells (L := L) (m₁ := m₁) m₀ j s).card ≤ 2 * d := by
  refine Finset.card_image_le.trans ?_
  simp [mul_comm]

omit [NeZero N₁] [NeZero L] in
theorem CAdj_mem_adjCells {s t : CTorus d L N₁ m₁ K} (h : CAdj (cellSide L m₀ m₁ j) s t) :
    t ∈ adjCells m₀ j s := by
  obtain ⟨μ, h | h⟩ := h
  · exact Finset.mem_image.2 ⟨(μ, true), Finset.mem_univ _, by simp [h]⟩
  · exact Finset.mem_image.2 ⟨(μ, false), Finset.mem_univ _, by simp [h]⟩

/-- **Rooted entropy at a hole component.**  Let `Ω` be a union of `π_j`-cells, `H ≠ ∅` a subset
of `Ω^c` closed under nearest-neighbour steps into `Ω^c` (a union of whole components of `Ω^c`)
and `κ₀ ≥ a_ent + 1`.  Summing over the labels `X ∈ 𝒟_j(mod Ω^c)` with `H ⊆ X` and `X ∩ Ω ≠ ∅`
(in the form of the sum of `G2_X`):
`∑ e^{-κ₀ d^cov_j(X mod Ω^c)} ≤ 2 d · #(cells meeting H) · K₀`. -/
theorem sum_exp_le_of_hole (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Ω H : Set (CTorus d L N₁ m₁ K)} (hΩ : IsPiUnion m₀ j Ω)
    (hHΩ : H ⊆ Ωᶜ) (hHcl : ∀ y ∈ H, ∀ z, z ∉ Ω → Nbr y z → z ∈ H) (hHne : H.Nonempty)
    {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) :
    (open Classical in
      ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
          DjMod m₀ j Ω X ∧ H ⊆ X ∧ (X ∩ Ω).Nonempty),
        Real.exp (-κ₀ * dcovMod m₀ j Ω X)) ≤
      2 * d * (holeBases m₀ j H).card * K0 d L κ₀ := by
  classical
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  set Rt : Finset (CTorus d L N₁ m₁ K) := Finset.univ.filter fun t =>
    Aligned (cellSide L m₀ m₁ j) t ∧ box t (cellSide L m₀ m₁ j) ⊆ Ω ∧
      ∃ s ∈ holeBases m₀ j H, CAdj (cellSide L m₀ m₁ j) s t with hRt
  have hcard : Rt.card ≤ (holeBases m₀ j H).card * (2 * d) := by
    refine le_trans (Finset.card_le_card (t := (holeBases m₀ j H).biUnion (adjCells m₀ j)) ?_)
      (Finset.card_biUnion_le.trans ?_)
    · intro t ht
      obtain ⟨-, -, -, s, hs, hst⟩ := (Finset.mem_filter.1 ht)
      exact Finset.mem_biUnion.2 ⟨s, hs, CAdj_mem_adjCells hst⟩
    · calc ∑ s ∈ holeBases m₀ j H, (adjCells m₀ j s).card
          ≤ ∑ _s ∈ holeBases m₀ j H, 2 * d := Finset.sum_le_sum fun s _ => card_adjCells_le s
        _ = _ := by simp
  have key := sum_exp_le_of_roots hN hj hΩ Rt
    (fun r hr => ⟨(Finset.mem_filter.1 hr).2.1, (Finset.mem_filter.1 hr).2.2.1⟩) hκ
    (fun X => H ⊆ X ∧ (X ∩ Ω).Nonempty) (by
      rintro X hX ⟨hHX, hXΩ⟩
      obtain ⟨u, hu, t, hta, htb, hadj⟩ := exists_active_adj_hole hN hj hΩ hX hHΩ hHcl hHX hHne hXΩ
      refine ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, hta, fun z hz => (htb hz).2,
        cbase (cellSide L m₀ m₁ j) u, ?_, hadj⟩, fun z hz => (htb hz).1⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, u, hu, rfl⟩)
  have hK : 0 ≤ K0 d L κ₀ := by
    have h1 : 0 < 1 - Real.exp (-1) := by
      have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at this; linarith
    exact div_nonneg (Real.exp_pos _).le h1.le
  refine le_trans (le_of_eq (Finset.sum_congr (by ext; simp) (fun _ _ => rfl))) (key.trans ?_)
  have : (Rt.card : ℝ) ≤ 2 * d * (holeBases m₀ j H).card := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this; linarith
  nlinarith

end Balaban.Fluctuation
