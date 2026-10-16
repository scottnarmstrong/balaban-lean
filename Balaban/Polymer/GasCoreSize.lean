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

variable {Yt Zt : Type*} [Fintype Yt] [Fintype Zt]
  {β : Yt → ℂ} {τ : Zt → ℂ}

omit [Fintype Zt] in
/-- **Counting step, charged sums.**  If at most `m` objects have a given core, the sum over the
objects whose core contains the cell `b` of `exp(-κ dExt (core))` is at most `m (K0 + 1)` for
`κ ≥ a_ent + 1` (`sum_exp_dExt_le`). -/
theorem sum_exp_core_le [DecidableEq (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (S : Yt → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) {m κ : ℝ}
    (hfib : ∀ T, ((Finset.univ.filter (fun y => S y = T)).card : ℝ) ≤ m)
    (hκ : aEnt d L + 1 ≤ κ)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) :
    ∑ y ∈ Finset.univ.filter (fun y => b ∈ S y), Real.exp (-κ * dExt (S y)) ≤
      m * (K0 d L κ + 1) := by
  classical
  set s := Finset.univ.filter (fun y : Yt => b ∈ S y) with hs
  have h1 := Finset.sum_comp (fun T => Real.exp (-κ * dExt T)) S (s := s)
  have hm : 0 ≤ m := le_trans (Nat.cast_nonneg _) (hfib ∅)
  have h2 : ∀ T ∈ s.image S, ((s.filter (fun y => S y = T)).card : ℝ) ≤ m := by
    intro T _
    refine le_trans ?_ (hfib T)
    exact_mod_cast Finset.card_le_card (fun y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy.2)
  have h3 : ∑ T ∈ s.image S, Real.exp (-κ * dExt T) ≤ K0 d L κ + 1 := by
    set U := Finset.univ.filter (fun T : NePoly (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
      m₀ j Ω) => b ∈ T.1) with hU
    have hsub : s.image S ⊆ U.image Subtype.val := by
      intro T hT
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hT
      have hb : b ∈ S y := (Finset.mem_filter.1 hy).2
      exact Finset.mem_image.2 ⟨⟨S y, ⟨b, hb⟩⟩, by simp [hU, hb], rfl⟩
    calc ∑ T ∈ s.image S, Real.exp (-κ * dExt T)
        ≤ ∑ T ∈ U.image Subtype.val, Real.exp (-κ * dExt T) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.exp_nonneg _)
      _ = ∑ T ∈ U, Real.exp (-κ * dExt T.1) :=
          Finset.sum_image (fun a _ a' _ h => Subtype.ext h)
      _ = ∑ T : NePoly (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω),
            (if b ∈ T.1 then Real.exp (-κ * dExt T.1) else 0) := by
          rw [hU, Finset.sum_filter]
      _ ≤ _ := by
          convert sum_exp_dExt_le hN hj b hκ
  calc ∑ y ∈ s, Real.exp (-κ * dExt (S y))
      = ∑ T ∈ s.image S, ((s.filter (fun y => S y = T)).card • Real.exp (-κ * dExt T)) := h1
    _ ≤ ∑ T ∈ s.image S, m * Real.exp (-κ * dExt T) := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (h2 T hT) (Real.exp_nonneg _)
    _ ≤ m * (K0 d L κ + 1) := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h3 hm

omit [Fintype Yt] in
/-- **Counting step, supports of given cardinality.**  If at most `m ≥ 1` heavy objects have a
given core, and the size of a core is at most `c2` times its cardinality, then the number of heavy
objects whose core contains a given cell and has `v` cells is at most `K''^v` with
`K'' = m (K0 + 1) e^{(a_ent + 1) c2}`.  The bound does not depend on the volume. -/
theorem card_core_filter_le [DecidableEq (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (zs : Zt → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) {m c2 : ℝ}
    (hm : 1 ≤ m)
    (hfib : ∀ T, ((Finset.univ.filter (fun z => zs z = T)).card : ℝ) ≤ m)
    (hzd : ∀ z, dExt (zs z) ≤ c2 * (zs z).card)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) (v : ℕ) :
    ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤
      (m * (K0 d L (aEnt d L + 1) + 1) * Real.exp ((aEnt d L + 1) * c2)) ^ v := by
  classical
  set κ := aEnt d L + 1 with hκdef
  have hκ0 : 0 ≤ κ := by linarith [aEnt_nonneg d L]
  have hK0 : 0 ≤ K0 d L κ := by
    unfold K0
    have : Real.exp (-1) < 1 := by simp
    have : 0 < 1 - Real.exp (-1) := by linarith
    positivity
  set A := m * (K0 d L κ + 1) with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set s := Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v) with hs
  by_cases hv : v = 0
  · have : s = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun z hz => ?_)
      obtain ⟨hb, hc⟩ := (Finset.mem_filter.1 hz).2
      have := Finset.card_pos.2 ⟨b, hb⟩
      omega
    simp [this, hv]
  have hsum := sum_exp_core_le hN hj zs hfib (le_refl κ) b
  have h1 : (s.card : ℝ) * Real.exp (-κ * (c2 * v)) ≤ A := by
    calc (s.card : ℝ) * Real.exp (-κ * (c2 * v)) = ∑ z ∈ s, Real.exp (-κ * (c2 * v)) := by simp
      _ ≤ ∑ z ∈ s, Real.exp (-κ * dExt (zs z)) := by
          refine Finset.sum_le_sum fun z hz => Real.exp_le_exp.2 ?_
          have hc := (Finset.mem_filter.1 hz).2.2
          have := hzd z
          rw [hc] at this
          nlinarith
      _ ≤ ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), Real.exp (-κ * dExt (zs z)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun z hz =>
            Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hz).2.1⟩)
            (fun _ _ _ => Real.exp_nonneg _)
      _ ≤ A := hsum
  have h2 : (s.card : ℝ) ≤ A * Real.exp (κ * (c2 * v)) := by
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (κ * (c2 * v)))
    rw [mul_assoc, ← Real.exp_add] at this
    simpa using this
  have h3 : A ≤ A ^ v := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ v := pow_le_pow_right₀ hA1 (by omega)
  calc (s.card : ℝ) ≤ A * Real.exp (κ * (c2 * v)) := h2
    _ ≤ A ^ v * Real.exp (κ * c2) ^ v := by
        have : Real.exp (κ * (c2 * v)) = Real.exp (κ * c2) ^ v := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by rw [← mul_pow, hA]

/-- Classical equality on the cells, so that the finite sums below elaborate with the same
decidability instances as in `gas_activity_bound_core`. -/
local instance (priority := 10000) cubeBDecEq :
    DecidableEq (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) :=
  fun a b => Classical.propDecidable (a = b)

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

/-- **GAS (activity bound) on cores with volume-free counting.**  As
`gas_activity_bound_core_dExt`, with the entropy hypotheses `hent` and `hcount` replaced by the
fibre bounds: at most `mY` couplings have a given core, at most `mZ ≥ 1` heavy objects have a given
core, and `κ'' - κ' ≥ a_ent + 1`.  Then `hent` holds with `K0' = mY (K0 + 1)`
(`sum_exp_core_le`) and `hcount` with `K0'' = mZ (K0 + 1) e^{(a_ent + 1) c2}`
(`card_core_filter_le`); both are independent of the volume.  The remaining inputs are the bound
(1.35) with `3κ/2` decay (`hB`, with `κ'' = 3κ/2`), the removed-component factor `(3.10)` (`hτ`) and
the size of a removed core (`hzd`).  Core incidence is the reading of the Yang-Mills account
(https://github.com/ethanwsussman/Yang--Mills-LLM-experiment). -/
theorem gas_activity_bound_core_dExt_count (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    (core : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) →
      Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    {cy : Yt → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)}
    {zs cr : Zt → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)}
    {B0 κ' κ'' c2 p h mY mZ : ℝ}
    (hc2 : 0 ≤ c2) (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hp : 0 ≤ p)
    (hκ : aEnt d L + 1 ≤ κ'' - κ')
    (hz : ∀ z, (core (zs z)).Nonempty) (hcr : ∀ z, cr z ⊆ core (zs z))
    (hfibY : ∀ T, ((Finset.univ.filter (fun y => core (cy y) = T)).card : ℝ) ≤ mY)
    (hfibZ : ∀ T, ((Finset.univ.filter (fun z => core (zs z) = T)).card : ℝ) ≤ mZ)
    (hmZ : 1 ≤ mZ)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * dExt (core (cy y))))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (core (zs z)).card))
    (hzd : ∀ z, dExt (core (zs z)) ≤ c2 * (core (zs z)).card)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * cG d L) * (mY * (K0 d L (aEnt d L + 1) + 1)) +
      κ' * (c2 + cG d L) + c1 d L + 3 +
      Real.log (mZ * (K0 d L (aEnt d L + 1) + 1) * Real.exp ((aEnt d L + 1) * c2)) ≤ h)
    (X : NePoly (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    ‖gasK (fun y => core (cy y)) (fun z => core (zs z)) cr β τ X‖ ≤
      3 * c1 d L * Real.exp (-p) * Real.exp (-(κ' - 2) * dExt X.1) := by
  have hK0 : 0 ≤ K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by simp
    have : 0 < 1 - Real.exp (-1) := by linarith
    positivity
  have hmY : 0 ≤ mY := le_trans (Nat.cast_nonneg _) (hfibY ∅)
  have hK1 : 1 ≤ mZ * (K0 d L (aEnt d L + 1) + 1) * Real.exp ((aEnt d L + 1) * c2) := by
    have h1 : 1 ≤ mZ * (K0 d L (aEnt d L + 1) + 1) := by nlinarith
    have h2 : 1 ≤ Real.exp ((aEnt d L + 1) * c2) :=
      Real.one_le_exp (mul_nonneg (by linarith [aEnt_nonneg d L]) hc2)
    nlinarith
  have e1 : ∀ b, ∑ y ∈ Finset.univ.filter (fun y => b ∈ core (cy y)),
      Real.exp (-(κ'' - κ') * dExt (core (cy y))) ≤ mY * (K0 d L (aEnt d L + 1) + 1) :=
    fun b => sum_exp_core_le hN hj (fun y => core (cy y)) hfibY hκ b
  have e2 := fun (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω) (v : ℕ) =>
    card_core_filter_le hN hj (fun z => core (zs z)) hmZ hfibZ hzd b v
  refine gas_activity_bound_core_dExt hN hj core (cy := cy) (zs := zs) (cr := cr) (β := β)
    (τ := τ) hB0 hκ' hκ'' hp hz hcr hB hτ hzd
    (K0' := mY * (K0 d L (aEnt d L + 1) + 1))
    (K0'' := mZ * (K0 d L (aEnt d L + 1) + 1) * Real.exp ((aEnt d L + 1) * c2))
    (mul_nonneg hmY (by linarith)) e1 hK1 e2 hh X

end Size

end Balaban.Polymer
