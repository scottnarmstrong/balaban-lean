/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCore
public import Balaban.Fluctuation.SizeModCellPath
public import Balaban.LargeField.Def7

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

section OldTerms

open Balaban.LargeField.Def7 Balaban.Polymer RegionHistory Balaban.Multiscale Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **The old-term bound `hB` of the physical gas, from (D7) of the post-`R` class.**
Let `rep` satisfy `D7BdryPost` with constant `fac` and rate `rate` (`B₀` and `κ''` of
`gas_activity_bound_physical`; `rate = 3κ/2` for `IsRep`).  Let `labY y` be boundary domains of
the post-`R` class (`bdryDomsPost`: `FineValid`) of a history `A ∈ rep.hist`, whose fine sets are
`Ŷ` of the cells `cy y` of the fine post-`R` region, and let `β y` be the boundary terms
`ℬ^{(k)}(labY y, A)` at one external field `h ∈ hSetB`, one pair of block fields and one `g` that
lie in the `H7` domain at every `labY y`.  Then `‖β y‖ ≤ fac · e^{-rate · dExt (cy y)}`, the
size `dExt` of the core being the modular size `d7Size` of the domain
(`dExt_core_eq_d7Size`).  The hypotheses on the domain are exactly: membership in
`bdryDomsPost` (validity), `d7Pull Fr k (labY y) = Ŷ(sitesOf (cy y))`, and the `H7` domain
condition at the point. -/
theorem old_term_bound_of_D7BdryPost {m₀ m₁ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁}
    {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
    {rep : Rep S n R k0 K M N geo cs P k} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    (hD : D7BdryPost Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {h : Fin N → ℂ} (hh : h ∈ hSetB hv)
    (p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ))
    {Yt : Type*} (labY : Yt → Finset (Torus S.d (n k)))
    (hlab : ∀ y, labY y ∈ bdryDomsPost Fr A k (Zof A))
    (hp : ∀ y, H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (labY y : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    {cy : Yt → Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))}
    (hXY : ∀ y, d7Pull Fr k (labY y : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (cy y)))
    (β : Yt → ℂ) (hβ : ∀ y, β y = rep.B A (labY y) (extK p.1) (extK p.2.1) h p.2.2) :
    ∀ y, ‖β y‖ ≤ fac * Real.exp (-rate * dExt (d := S.d) (cy y)) := by
  intro y
  have hmem := mem_bdryDomsPost.1 (hlab y)
  have hcon : SiteConnected (d7Pull Fr k (labY y : Set (Torus S.d (n k)))) :=
    hmem.2.1.1.2.2
  have hfin := d7SizeE_ne_top_of_mem (hlab y)
  rw [dExt_core_eq_d7Size Fr A k (cy y) (labY y) (hXY y) hcon hfin, hβ y]
  exact (hD.bound A hA (labY y) (hlab y) h hh p (hp y)).le

end OldTerms

end Balaban.LargeField
