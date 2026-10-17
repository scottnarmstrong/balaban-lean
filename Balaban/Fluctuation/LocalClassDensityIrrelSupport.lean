/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusSum

/-!
# The support polymer of a label `(j, y, X)` (`LocalClassDensityIrrelSupport`)

The label functional `ℰ_{irrel}(y, X)` depends on `Ψ` on `X ∪ st₊(y)`, which is not a union of
`π'_j`-cubes.  The support used in the chain is the polymer `X^⋆ = X ∪ □(y)`, `□(y)` the
`π'_j`-cube whose central cell contains `y` (it contains `st₊(y)` for `L ≥ 3`).

* `isPolyDom_union`: the union of two polymers with a common site is a polymer;
* `stPlus_mem_cubeAt`: `y + L^j e_μ ∈ □(y)` for `L ≥ 3`;
* `eq_of_cell_bases`: two polymers with `X ∪ □ = X' ∪ □` and the same cells of `□` coincide;
* `fibre_card_le`: at most `2^{L^d}` labels `(j, y, X)` have the same `(j, y, X ∪ □(y))`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2

section Support

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

omit [NeZero L] [NeZero N₁] in
/-- The union of two polymers of `𝒟_j` through a common site is a polymer of `𝒟_j`. -/
theorem isPolyDom_union {X Y : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X)
    (hY : IsPolyDom m₀ j Y) {z : CTorus d L N₁ m₁ k} (hzX : z ∈ X) (hzY : z ∈ Y) :
    IsPolyDom m₀ j (X ∪ Y) := by
  obtain ⟨hXn, ⟨𝒦X, hXa, hXb⟩, hXc⟩ := hX
  obtain ⟨hYn, ⟨𝒦Y, hYa, hYb⟩, hYc⟩ := hY
  refine ⟨hXn.mono Set.subset_union_left, ⟨𝒦X ∪ 𝒦Y, ?_, ?_⟩, ?_⟩
  · rintro b (hb | hb)
    · exact ⟨(hXa b hb).1, (hXa b hb).2.trans Set.subset_union_left⟩
    · exact ⟨(hYa b hb).1, (hYa b hb).2.trans Set.subset_union_right⟩
  · rintro x (hx | hx)
    · obtain ⟨b, hb, hxb⟩ := hXb x hx
      exact ⟨b, Or.inl hb, hxb⟩
    · obtain ⟨b, hb, hxb⟩ := hYb x hx
      exact ⟨b, Or.inr hb, hxb⟩
  · have hmX : ∀ x ∈ X, Relation.ReflTransGen
        (fun a b => a ∈ X ∪ Y ∧ b ∈ X ∪ Y ∧ Nbr a b) x z := fun x hx =>
      Relation.ReflTransGen.mono (fun a b h => ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) _ _ (hXc x hx z hzX)
    have hmY : ∀ x ∈ Y, Relation.ReflTransGen
        (fun a b => a ∈ X ∪ Y ∧ b ∈ X ∪ Y ∧ Nbr a b) x z := fun x hx =>
      Relation.ReflTransGen.mono (fun a b h => ⟨Or.inr h.1, Or.inr h.2.1, h.2.2⟩) _ _ (hYc x hx z hzY)
    have hsymm : ∀ a b : CTorus d L N₁ m₁ k, (a ∈ X ∪ Y ∧ b ∈ X ∪ Y ∧ Nbr a b) →
        (b ∈ X ∪ Y ∧ a ∈ X ∪ Y ∧ Nbr b a) := fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
    have hto : ∀ x ∈ X ∪ Y, Relation.ReflTransGen
        (fun a b => a ∈ X ∪ Y ∧ b ∈ X ∪ Y ∧ Nbr a b) x z := fun x hx => hx.elim (hmX x) (hmY x)
    intro x hx y hy
    exact (hto x hx).trans (rtg_symm hsymm (hto y hy))

/-- **The cell of a site of a polymer lies in the polymer.** -/
theorem cell_subset_of_isPolyDom (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) :
    ∀ z ∈ X, box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X := by
  intro z hz
  obtain ⟨-, ⟨𝒦, hch⟩, -⟩ := hX
  obtain ⟨b, hb, hzb⟩ := hch.2 z hz
  exact (cell_subset_cube (cellSide_dvd hN hjk) (cellSide_pos m₀ m₁ j) (hch.1 b hb).1 hzb).trans
    (hch.1 b hb).2

/-- A site of a cell is in a polymer iff the base of the cell is. -/
theorem mem_iff_cell_base (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom m₀ j X) {c z : CTorus d L N₁ m₁ k} (hc : Aligned (cellSide L m₀ m₁ j) c)
    (hz : z ∈ box c (cellSide L m₀ m₁ j)) : z ∈ X ↔ c ∈ X := by
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hpos := cellSide_pos (L := L) m₀ m₁ j
  have hcc : cbase (cellSide L m₀ m₁ j) c = c :=
    cbase_eq_of_mem_box hdvd hc (mem_box_self c hpos)
  constructor
  · intro hzX
    have h := cell_subset_of_isPolyDom hN hjk hX z hzX
    rw [cbase_eq_of_mem_box hdvd hc hz] at h
    exact h (mem_box_self c hpos)
  · intro hcX
    have h := cell_subset_of_isPolyDom hN hjk hX c hcX
    rw [hcc] at h
    exact h hz

omit [NeZero L] [NeZero N₁] in
/-- A site of the cube `box c (L s)` lies in a cell `box (c + s w) s`, `w ∈ [0, L)^d`. -/
theorem exists_cell_of_mem_cube {s : ℕ} (hs : 0 < s) {c z : CTorus d L N₁ m₁ k}
    (hz : z ∈ box c (L * s)) :
    ∃ w : Fin d → Fin L, z ∈ box (c + natT fun μ => s * (w μ : ℕ)) s := by
  obtain ⟨v, hv, rfl⟩ := hz
  have hlt : ∀ μ, v μ / s < L := fun μ => by
    rw [Nat.div_lt_iff_lt_mul hs]; exact hv μ
  refine ⟨fun μ => ⟨v μ / s, hlt μ⟩, fun μ => v μ % s, fun μ => Nat.mod_lt _ hs, ?_⟩
  have : v = (fun μ => s * (v μ / s)) + fun μ => v μ % s := funext fun μ => by
    simp only [Pi.add_apply]; exact (Nat.div_add_mod (v μ) s).symm
  conv_lhs => rw [this]
  rw [natT_add, add_assoc]

/-- Two polymers whose unions with the cube `□` agree and which contain the same cells of `□`
coincide. -/
theorem eq_of_cell_bases (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) {X X' : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom m₀ j X) (hX' : IsPolyDom m₀ j X') {c : CTorus d L N₁ m₁ k}
    (hc : Aligned (cellSide L m₀ m₁ j) c)
    (hU : X ∪ box c (L * cellSide L m₀ m₁ j) = X' ∪ box c (L * cellSide L m₀ m₁ j))
    (hcell : ∀ w : Fin d → Fin L,
      (c + natT fun μ => cellSide L m₀ m₁ j * (w μ : ℕ)) ∈ X ↔
        (c + natT fun μ => cellSide L m₀ m₁ j * (w μ : ℕ)) ∈ X') : X = X' := by
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hpos := cellSide_pos (L := L) m₀ m₁ j
  ext z
  by_cases hz : z ∈ box c (L * cellSide L m₀ m₁ j)
  · obtain ⟨w, hw⟩ := exists_cell_of_mem_cube hpos hz
    have hal : Aligned (cellSide L m₀ m₁ j) (c + natT fun μ => cellSide L m₀ m₁ j * (w μ : ℕ)) :=
      aligned_add_natT hdvd hc fun μ => by simp
    rw [mem_iff_cell_base hN hjk hX hal hw, mem_iff_cell_base hN hjk hX' hal hw]
    exact hcell w
  · have h := congrArg (fun A => z ∈ A) hU
    simp only [Set.mem_union, hz, or_false, eq_iff_iff] at h
    exact h

/-- **`st₊(y) ⊆ □(y)`** for `L ≥ 3`: `y + L^j e_μ` lies in the `π'_j`-cube whose central cell
contains `y`. -/
theorem stPlus_mem_cubeAt (hL : 3 ≤ L) (y : CTorus d L N₁ m₁ k) (μ : Fin d) :
    y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) ∈
      box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
        (L * cellSide L m₀ m₁ j) := by
  have hs0 := cellSide_pos (L := L) m₀ m₁ j
  have hsj : L ^ j ≤ cellSide L m₀ m₁ j := by
    unfold cellSide
    exact Nat.pow_le_pow_right (NeZero.pos L) (by omega)
  set s := cellSide L m₀ m₁ j with hs
  let wy : Fin d → ℕ := fun ν => L / 2 * s + (y ν).val % s
  have hy : y = (cbase s y - natT fun _ => L / 2 * s) + natT wy := by
    have e : (natT wy : CTorus d L N₁ m₁ k) =
        natT (fun _ : Fin d => L / 2 * s) + natT (fun ν => (y ν).val % s) :=
      natT_add (fun _ : Fin d => L / 2 * s) (fun ν => (y ν).val % s)
    rw [e, cbase_eq_sub]; abel
  have hsingle : (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) =
      natT (Pi.single μ (L ^ j) : Fin d → ℕ) := by
    funext ν
    by_cases h : ν = μ
    · subst h; simp [natT]
    · simp [natT, h]
  refine ⟨wy + Pi.single μ (L ^ j), fun ν => ?_, ?_⟩
  · have h1 : (y ν).val % s < s := Nat.mod_lt _ hs0
    have h2 : L / 2 + 2 ≤ L := by omega
    have h3 : (L / 2 + 2) * s ≤ L * s := Nat.mul_le_mul_right _ h2
    simp only [wy, Pi.add_apply, Pi.single_apply]
    split_ifs
    · nlinarith
    · nlinarith
  · rw [hsingle, natT_add]
    conv_lhs => rw [hy]
    abel

open Classical in
/-- **At most `2^{L^d}` labels have the same support polymer.**  Labels `τ = (j_τ, y_τ, X_τ)` with
the polymers `X_τ ∈ 𝒟_{j_τ}` and the same `(j, y, X ∪ □(y))` are determined by the cells of `□(y)`
contained in `X_τ`. -/
theorem fibre_card_le {ι : Type*} [Fintype ι] (hN : L ^ m₀ ∣ N₁) (jL : ι → ℕ)
    (hjk : ∀ τ, jL τ ≤ k) (yL : ι → CTorus d L N₁ m₁ k) (XP : ι → Set (CTorus d L N₁ m₁ k))
    (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (XP τ))
    (hinj : ∀ τ τ', jL τ = jL τ' → yL τ = yL τ' → XP τ = XP τ' → τ = τ') (τ : ι) :
    (Finset.univ.filter fun τ' : ι => jL τ' = jL τ ∧ yL τ' = yL τ ∧
      XP τ' ∪ box (cbase (cellSide L m₀ m₁ (jL τ')) (yL τ') -
        natT fun _ => L / 2 * cellSide L m₀ m₁ (jL τ')) (L * cellSide L m₀ m₁ (jL τ')) =
      XP τ ∪ box (cbase (cellSide L m₀ m₁ (jL τ)) (yL τ) -
        natT fun _ => L / 2 * cellSide L m₀ m₁ (jL τ)) (L * cellSide L m₀ m₁ (jL τ))).card ≤
      2 ^ (L ^ d) := by
  set c : CTorus d L N₁ m₁ k := cbase (cellSide L m₀ m₁ (jL τ)) (yL τ) -
    natT fun _ => L / 2 * cellSide L m₀ m₁ (jL τ) with hc
  have hcal : Aligned (cellSide L m₀ m₁ (jL τ)) c := aligned_cubeAt_base hN (hjk τ) (yL τ)
  set F := Finset.univ.filter fun τ' : ι => jL τ' = jL τ ∧ yL τ' = yL τ ∧
      XP τ' ∪ box (cbase (cellSide L m₀ m₁ (jL τ')) (yL τ') -
        natT fun _ => L / 2 * cellSide L m₀ m₁ (jL τ')) (L * cellSide L m₀ m₁ (jL τ')) =
      XP τ ∪ box (cbase (cellSide L m₀ m₁ (jL τ)) (yL τ) -
        natT fun _ => L / 2 * cellSide L m₀ m₁ (jL τ)) (L * cellSide L m₀ m₁ (jL τ)) with hF
  have hFmem : ∀ a ∈ F, jL a = jL τ ∧ XP a ∪ box c (L * cellSide L m₀ m₁ (jL τ)) =
      XP τ ∪ box c (L * cellSide L m₀ m₁ (jL τ)) := by
    intro a ha
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.1 ha).2
    refine ⟨h1, ?_⟩
    rw [h1, h2] at h3
    exact h3
  have hbound : F.card ≤ (Finset.univ : Finset (Finset (Fin d → Fin L))).card := by
    refine Finset.card_le_card_of_injOn (fun a => Finset.univ.filter fun w : Fin d → Fin L =>
      (c + natT fun μ => cellSide L m₀ m₁ (jL τ) * (w μ : ℕ)) ∈ XP a)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
    intro a ha b hb hab
    have ha' := hFmem a (Finset.mem_coe.1 ha)
    have hb' := hFmem b (Finset.mem_coe.1 hb)
    have hXa : IsPolyDom m₀ (jL τ) (XP a) := ha'.1 ▸ hXp a
    have hXb : IsPolyDom m₀ (jL τ) (XP b) := hb'.1 ▸ hXp b
    have hXe : XP a = XP b := eq_of_cell_bases hN (hjk τ) hXa hXb hcal (ha'.2.trans hb'.2.symm)
      fun w => by
        have := congrArg (fun A => w ∈ A) hab
        simpa using this
    refine hinj a b (ha'.1.trans hb'.1.symm) ?_ hXe
    exact ((Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2.2.1).trans
      ((Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2.2.1).symm
  refine hbound.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

end Support

end Balaban.Fluctuation
