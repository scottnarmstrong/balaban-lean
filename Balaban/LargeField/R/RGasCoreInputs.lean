/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCore
public import Balaban.Fluctuation.SizeModCellPath

/-!
# Inputs of the physical large-field gas bound (blocker 4)

`notes/phase1/VMOD-43.md` §5b-5c.  Inputs of `gas_activity_bound_physical`
(`LargeField/R/RGasCore.lean`).

* `dExt_le_card_sub_one_of_connected`: the size of a set `T` of `π_j`-cells whose union is
  nearest-neighbour connected, and whose hull `Ŷ(sitesOf T)` is a union of `π'_j`-cubes, is at most
  `|T| - 1`.  The constant does not depend on the torus, on `j`, or on `T`.  The proof is the
  tree lemma `assemble`: the corners of adjacent cells are linked at cost `1`
  (`linked_cell_adj`), and a spanning tree of the cell adjacency has `|T| - 1` bonds.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization

section Core

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)}

/-- Cells of a set whose union is nearest-neighbour connected are joined by a chain of adjacent
cells of the set. -/
theorem cells_reach_of_siteConnected (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    (hconn : SiteConnected (sitesOf T)) {u : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω}
    (hu : u ∈ T) :
    ∀ v ∈ T, Relation.ReflTransGen
      (fun p q : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω =>
        CAdj (cellSide L m₀ m₁ j) p.1 q.1 ∧ p ∈ T ∧ q ∈ T) u v := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  intro v hv
  have hx : u.1 ∈ sitesOf T := mem_sitesOf.2 ⟨u, hu, mem_box_self _ ha0⟩
  have hy : v.1 ∈ sitesOf T := mem_sitesOf.2 ⟨v, hv, mem_box_self _ ha0⟩
  have key : ∀ y, Relation.ReflTransGen (fun p q => p ∈ sitesOf T ∧ q ∈ sitesOf T ∧ Nbr p q)
      u.1 y → ∀ cy ∈ T, y ∈ Localization.box cy.1 (cellSide L m₀ m₁ j) → Relation.ReflTransGen
      (fun p q : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω =>
        CAdj (cellSide L m₀ m₁ j) p.1 q.1 ∧ p ∈ T ∧ q ∈ T) u cy := by
    intro y hy
    induction hy with
    | refl =>
      intro cy hcy hmem
      have e : cy = u := Subtype.ext
        ((cbase_eq_of_mem_box hdvd cy.2.1 hmem).symm.trans
          (cbase_eq_of_mem_box hdvd u.2.1 (mem_box_self _ ha0)))
      rw [e]
    | @tail b c _ hbc ih =>
      intro cc hcc hmem
      obtain ⟨cb, hcb, hbmem⟩ := mem_sitesOf.1 hbc.1
      have ihb := ih cb hcb hbmem
      have hc1 : cbase (cellSide L m₀ m₁ j) c = cc.1 := cbase_eq_of_mem_box hdvd cc.2.1 hmem
      have hb1 : cbase (cellSide L m₀ m₁ j) b = cb.1 := cbase_eq_of_mem_box hdvd cb.2.1 hbmem
      rcases cbase_nbr hdvd ha0 hbc.2.2 with h | h
      · have : cc = cb := Subtype.ext (hc1.symm.trans (h.trans hb1))
        rw [this]; exact ihb
      · rw [hb1, hc1] at h
        exact ihb.tail ⟨h, hcb, hcc⟩
  exact key v.1 (hconn _ hx _ hy) v hv (mem_box_self _ ha0)

/-- **Cover of the corners of a connected set of cells.**  The corners of the cells of `T` lie in a
connected lattice structure inside any region containing the cells, of cost at most `|T| - 1`. -/
theorem covers_corners_of_siteConnected (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    (hT : T.Nonempty) (hconn : SiteConnected (sitesOf T)) {R : Set (Balaban.Localization.CTorus d L N₁ m₁ K)}
    (hR : ∀ b ∈ T, Localization.box b.1 (cellSide L m₀ m₁ j) ⊆ R) :
    Covers R (scaleW L m₀ m₁ j) ((T.card : ℝ) - 1) (T.biUnion fun b => {b.1}) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hT
  have := assemble (R := R) (ω := scaleW L m₀ m₁ j) (scaleW_nonneg (m₀ := m₀) (j := j)) T
    (fun p q => CAdj (cellSide L m₀ m₁ j) p.1 q.1) v₀ hv₀
    (fun v hv => by
      refine Relation.ReflTransGen.mono (fun p q h => h) _ _ (cells_reach_of_siteConnected hN hj T hconn hv₀ v hv))
    (fun b => {b.1}) (fun _ => 0)
    (fun v hv => by
      refine ⟨{v.1}, ∅, connStruct_singleton v.1, ?_, by simp, ?_⟩
      · simpa using hR v hv (mem_box_self _ (cellSide_pos (L := L) m₀ m₁ j))
      · simp [bondCost])
    1 (fun u hu v hv h => ⟨u.1, by simp, v.1, by simp,
      linked_cell_adj (hR u hu) (hR v hv) h⟩)
  simpa using this

/-- **The size of a connected core is at most its number of cells, minus one.**  If the cells of
`T` form a nearest-neighbour connected set and `Ŷ(sitesOf T)` is a connected union of `π'_j`-cubes
(`IsDj`), then `dExt T ≤ |T| - 1`.  The constant `1` is independent of the torus, of `j` and of
`T`. -/
theorem dExt_le_card_sub_one_of_connected (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) (hT : T.Nonempty)
    (hconn : SiteConnected (sitesOf T))
    (hDj : IsDj m₀ j (Yhat Ω (sitesOf T))) :
    dExt (d := d) T ≤ (T.card : ℝ) - 1 := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hsub : ∀ b ∈ T, Localization.box b.1 (cellSide L m₀ m₁ j) ⊆ Yhat Ω (sitesOf T) :=
    fun b hb z hz => Or.inl (mem_sitesOf.2 ⟨b, hb, hz⟩)
  obtain ⟨W, E, hc, hWR, hA, hcost⟩ := covers_corners_of_siteConnected hN hj T hT hconn hsub
  have hadm : ModAdmissible m₀ j Ω (Yhat Ω (sitesOf T))
      {b | Aligned (cellSide L m₀ m₁ j) b ∧
        Localization.box b (L * cellSide L m₀ m₁ j) ⊆ Yhat Ω (sitesOf T) ∧
        ∃ z ∈ sitesOf T, z ∈ Localization.box b (L * cellSide L m₀ m₁ j)} W E := by
    refine ⟨fun b hb => ⟨hb.1, hb.2.1⟩, fun z hz => ?_, hc, hWR, ?_⟩
    · have hzT : z ∈ sitesOf T := by
        rcases hz.1 with h | ⟨z', hz', -, hy⟩
        · exact h
        · exact absurd hz.2 hy.1
      obtain ⟨b, hb1, hb2, hb3⟩ := hDj.2.1 z hz.1
      exact Set.mem_iUnion₂.2 ⟨b, ⟨hb1, hb3, z, hzT, hb2⟩, hb2⟩
    · intro b hb
      obtain ⟨z, hzT, hzb⟩ := hb.2.2
      obtain ⟨cc, hcc, hzc⟩ := mem_sitesOf.1 hzT
      have hcb := cbase_eq_of_mem_box hdvd cc.2.1 hzc
      have hin : cc.1 ∈ Localization.box (cbase (cellSide L m₀ m₁ j) z)
          (cellSide L m₀ m₁ j) := by rw [hcb]; exact mem_box_self _ ha0
      refine ⟨cc.1, hA (Finset.mem_biUnion.2 ⟨cc, hcc, by simp⟩), ?_⟩
      exact cell_subset_cube hdvd ha0 hb.1 hzb hin
  have hle := dcovModE_le_of_admissible hadm
  have hcost' : bondCost (scaleW L m₀ m₁ j) E ≤ (T.card : ℝ) - 1 := hcost
  have hd : dOmega m₀ j Ω (sitesOf T) = dcovModE m₀ j Ω (Yhat Ω (sitesOf T)) := by
    unfold dOmega; simp [hDj.2.2]
  have hfin : dOmega m₀ j Ω (sitesOf T) ≠ ⊤ := by
    rw [hd]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  rw [dExt_eq_toReal hfin, hd]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E)] at this
  exact this.trans hcost'

/-- The size of a connected core is at most its number of cells (`c2 = 1` in `hzd`). -/
theorem dExt_le_card_of_connected (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) (hT : T.Nonempty)
    (hconn : SiteConnected (sitesOf T))
    (hDj : IsDj m₀ j (Yhat Ω (sitesOf T))) :
    dExt (d := d) T ≤ 1 * (T.card : ℝ) := by
  have := dExt_le_card_sub_one_of_connected hN hj T hT hconn hDj
  linarith

end Core

end Balaban.LargeField
