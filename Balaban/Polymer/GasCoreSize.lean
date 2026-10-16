/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasCore
public import Balaban.Fluctuation.CubeSystem

/-!
# The size step on cores (blocker 4, `notes/phase1/VMOD-43.md` §3 (ii))

The core-incidence reading of the removed-component gas is due to the Yang-Mills account
(https://github.com/ethanwsussman/Yang--Mills-LLM-experiment, see `notes/phase1/YMACCOUNT.md`).

The base set of the gas is the set `𝔅 = CubeB m₀ j Ω` of `π_j`-cells of the active region `Ω`
(`Fluctuation/CubeSystem.lean`).  A retained hole contains no such cell, so every support
`core X ⊆ 𝔅` consists of active cells only, and two elementary objects are in contact exactly when
their cores share an active cell, that is, when the intersection contains a `π_j`-cell of `Ω`.
This is the hypothesis of `G3_dcov`, whose fold along a contact tree is `dExt_unionCs_le`
(`CubeSystem.lean`, via `phi_union_le`).  The size `dExt` of a set of cells is `d_Ω` of its union
(`dExt_eq_toReal`), so the length through a retained hole is never charged.

* `dExt_unionCs_le_of_connSet`: the size of the union of a contact-connected family of sets of
  cells, indexed by an arbitrary type, is at most the sum of the sizes plus `c_G` per contact.
* `gas_activity_bound_core_dExt`: `gas_activity_bound_core` for the size `dExt`; the hypotheses
  `hd`, `hG3`, `hG1` are discharged.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer

open Balaban Balaban.Fluctuation Balaban.Localization

section Size

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

/-- **Size of a contact-connected union of sets of cells.**  For any family `cs` of sets of active
cells, connected through contacts (shared cells), `dExt (⋃ cs t) ≤ ∑ dExt (cs t) + c_G (|C| - 1)`.
Applied to `cs = gasCs (core ∘ cy) (core ∘ zs)` this is the hypothesis `hG3` of
`gas_activity_bound_core` for the size `dExt`. -/
theorem dExt_unionCs_le_of_connSet {ι : Type*}
    (cs : ι → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) (C : Finset ι)
    (hC : ConnSet cs C) :
    dExt (unionCs cs C) ≤ ∑ t ∈ C, dExt (cs t) + cG d L * ((C.card : ℝ) - 1) := by
  classical
  obtain ⟨hne, hreach⟩ := hC
  by_cases hone : C.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hone
    simp [unionCs]
  have hne2 : 1 < C.card := by
    have := Finset.card_pos.2 hne
    omega
  have hf : ∀ t ∈ C, (cs t).Nonempty := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := Finset.exists_mem_ne hne2 t
    have hr := hreach t ht s hs
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hc, -⟩
    · exact absurd h.symm hst
    · have := hc.2.2
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      exact this (by rw [hemp]; exact Finset.disjoint_empty_left _)
  let Gc : SimpleGraph ι := SimpleGraph.fromRel (Contact cs)
  have hconn : (Gc.induce (C : Set ι)).Connected := by
    obtain ⟨x₀, hx₀⟩ := hne
    have : Nonempty (C : Set ι) := ⟨⟨x₀, hx₀⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have key : ∀ y, Relation.ReflTransGen (fun x y => x ∈ C ∧ y ∈ C ∧ Contact cs x y) a y →
        ∀ hy : y ∈ C, (Gc.induce (C : Set ι)).Reachable ⟨a, ha⟩ ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail u v _ huv ih =>
        intro hv
        have hu : u ∈ C := huv.1
        refine (ih hu).trans ?_
        by_cases heq : u = v
        · subst heq; exact SimpleGraph.Reachable.refl _
        · exact SimpleGraph.Adj.reachable (show Gc.Adj u v from by
            rw [SimpleGraph.fromRel_adj]; exact ⟨heq, Or.inl huv.2.2⟩)
    exact key b (hreach a ha b hb) hb
  have key := phi_union_le (dExt (m₀ := m₀) (j := j) (Ω := Ω)) (cG d L)
    (fun X Y _ _ h => dExt_union_le X Y h) (Gc.induce (C : Set ι)) (fun t => cs t.1)
    (fun t => hf t.1 t.2) (fun a b hab => by
      rw [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with h | h
      · exact h
      · exact fun hd => h hd.symm) (C.card - 1) Finset.univ
    (by
      simpa using (Nat.sub_add_cancel (Finset.card_pos.2 hne)).symm)
    (by
      rw [Finset.coe_univ]
      exact (SimpleGraph.induceUnivIso _).connected_iff.2 hconn)
  have hc : ((C.card - 1 : ℕ) : ℝ) = (C.card : ℝ) - 1 := by
    rw [Nat.cast_sub (Finset.card_pos.2 hne)]; simp
  rw [hc] at key
  have hS : ∑ t : ↥C, dExt (cs t.1) = ∑ t ∈ C, dExt (cs t) :=
    Finset.sum_coe_sort C (fun t => dExt (cs t))
  have hU : unionCs cs C = (Finset.univ : Finset ↥C).biUnion (fun t => cs t.1) := by
    ext x; simp [unionCs]
  rw [hU, ← hS]
  exact key

/-- Classical equality on the cells, so that the finite sums below elaborate with the same
decidability instances as in `gas_activity_bound_core`. -/
local instance (priority := 10000) cubeBDecEq :
    DecidableEq (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) :=
  fun a b => Classical.propDecidable (a = b)

variable {Yt Zt : Type*} [Fintype Yt] [Fintype Zt]
  {β : Yt → ℂ} {τ : Zt → ℂ}

/-- **GAS (activity bound) on cores, for the covering size `dExt`.**  The base set is the set of
active `π_j`-cells `CubeB m₀ j Ω`; the size is `dExt`, with `c = c_G` and `c₁ = c1 d L`.  The
hypotheses `hd`, `hG3`, `hG1` of `gas_activity_bound_core` are discharged by
`dExt_unionCs_le_of_connSet` and `card_le_dExt`; the length through a retained hole is not charged
because a hole contains no active cell.  Core incidence is the reading of the Yang-Mills account
(https://github.com/ethanwsussman/Yang--Mills-LLM-experiment). -/
theorem gas_activity_bound_core_dExt (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (core : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) →
      Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    {cy : Yt → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)}
    {zs cr : Zt → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)}
    {B0 κ' κ'' c2 p h : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hp : 0 ≤ p)
    (hz : ∀ z, (core (zs z)).Nonempty) (hcr : ∀ z, cr z ⊆ core (zs z))
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * dExt (core (cy y))))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (core (zs z)).card))
    (hzd : ∀ z, dExt (core (zs z)) ≤ c2 * (core (zs z)).card)
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b, ∑ y ∈ Finset.univ.filter (fun y => b ∈ core (cy y)),
      Real.exp (-(κ'' - κ') * dExt (core (cy y))) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ core (zs z) ∧ (core (zs z)).card = v)).card : ℝ) ≤
        K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * cG d L) * K0' + κ' * (c2 + cG d L) + c1 d L + 3 +
      Real.log K0'' ≤ h)
    (X : NePoly (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    ‖gasK (fun y => core (cy y)) (fun z => core (zs z)) cr β τ X‖ ≤
      3 * c1 d L * Real.exp (-p) * Real.exp (-(κ' - 2) * dExt X.1) :=
  by
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs (fun y => core (cy y)) (fun z => core (zs z))) C →
      gasA (fun y => core (cy y)) (fun z => core (zs z)) cr C →
      dExt (m₀ := m₀) (j := j) (Ω := Ω)
          (unionCs (gasCs (fun y => core (cy y)) (fun z => core (zs z))) C) ≤
        ∑ t ∈ C, dExt (m₀ := m₀) (j := j) (Ω := Ω)
            (gasCs (fun y => core (cy y)) (fun z => core (zs z)) t) +
          cG d L * ((C.card : ℝ) - 1) :=
    fun C hC _ => dExt_unionCs_le_of_connSet _ C hC
  exact gas_activity_bound_core core (d := dExt (m₀ := m₀) (j := j) (Ω := Ω)) hB0 hκ' hκ''
    hcG hc1 hp dExt_nonneg hz hcr hB hτ hzd hG3 hK0' hent hK1 hcount hh X
    (card_le_dExt hN hj X.1)

end Size

end Balaban.Polymer
