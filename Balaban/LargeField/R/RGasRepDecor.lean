/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Gas

/-!
# The gas of removed objects with decorated couplings (W968)

`notes/phase1/LF4R-PLAN.md`, status W968 (blocker 4, the representation of the output of `R`).  In the bracket of
P7 (3.26) the sum runs over the families `Γ` of pairwise compatible removed objects (removed components with their
localized histories, or removed clusters), with weight `∏_{m∈Γ} τ_m · exp ℬ''(Γ)`.  By (D7) `loc_hist` a boundary term
`ℬ^{(k)}(X, 𝔸' ∪ Γ)` depends on the family only through the members `Γ_X ⊆ Γ` that meet `X`, so
`ℬ''(Γ) = ∑_X b_X(Γ_X)` with `b_X(∅) = 0`.  P7 p. 528 Mayer-expands `exp b_X` and sums, for a polymer, "over all
clusters and all sets `{Z_{i₁}, …, Z_{i_q}}` determining the polymer": the couplings are decorated by the set of
removed objects they meet.  This is not the landed `gasK` (`Polymer/Gas.lean`), whose coupling weights do not depend on
the family.

`gasDecor_eq`: with light objects `(X, S)` (`S` a nonempty set of objects meeting `X`), charged supports
`cx X ∪ ⋃_{m∈S} cz m`, weights `e^{b_X(S)} - 1`, heavy objects `m` with supports `cz m` and weights `τ_m`, and the
admissibility "heavy supports pairwise disjoint, and each light `(X, S)` has `S = Γ_X`", the sum
`∑_Γ ∏_{m∈Γ} τ_m · exp ∑_X b_X(Γ_X)` is the partition function of the polymer gas of connected admissible families
(`decomposition`).  The admissibility is local because a member meeting `X` is in contact with `(X, S)`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Balaban.Polymer

namespace Balaban.LargeField

section Decor

variable {B Zt Xt : Type*} [Fintype B] [Fintype Zt] [Fintype Xt]
  (cz : Zt → Finset B) (cx : Xt → Finset B) (near : Xt → Zt → Prop)
  (τ : Zt → ℂ) (b : Xt → Finset Zt → ℂ)

set_option hygiene false in
/-- The decorated light objects `(X, S)`: `S` a nonempty set of heavy objects meeting `X`. -/
local notation "Dec" => {p : Xt × Finset Zt // p.2.Nonempty ∧ ∀ m ∈ p.2, near p.1 m}

/-- **GAS with decorated couplings (identity)** (P7 (3.26)-(3.27), p. 528): if every heavy support is nonempty, a
heavy object meeting `X` (`near X m`) meets the support `cx X` of `X`, and `b_X(∅) = 0`, then
`∑_{Γ pairwise disjoint} ∏_{m∈Γ} τ_m · exp ∑_X b_X(Γ_X) = Ξ(K)`, `Γ_X = {m ∈ Γ : near X m}`, where `K` is the activity
(`polyAct`) of the connected admissible families of heavy objects `m` (support `cz m`, weight `τ_m`) and decorated
light objects `(X, S)` (support `cx X ∪ ⋃_{m∈S} cz m`, weight `e^{b_X(S)} - 1`), admissible when the heavy supports
are pairwise disjoint and every light `(X, S)` of the family has `S = Γ_X` for the heavy part `Γ` of the family. -/
theorem gasDecor_eq (hz : ∀ m, (cz m).Nonempty) (hnear : ∀ x m, near x m → ¬ Disjoint (cx x) (cz m))
    (hb0 : ∀ x, b x ∅ = 0) :
    ∑ Γ ∈ univ.filter (fun Γ : Finset Zt => ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (cz m) (cz m')),
        (∏ m ∈ Γ, τ m) * Complex.exp (∑ x, b x (Γ.filter (near x))) =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (polyAct (Sum.elim cz (fun y : Dec => cx y.1.1 ∪ y.1.2.biUnion cz))
          (fun D => (∀ m ∈ D.toLeft, ∀ m' ∈ D.toLeft, m ≠ m' → Disjoint (cz m) (cz m')) ∧
            ∀ y ∈ D.toRight, y.1.2 = D.toLeft.filter (near y.1.1))
          (Sum.elim τ (fun y : Dec => Complex.exp (b y.1.1 y.1.2) - 1))) := by
  set cs : Zt ⊕ Dec → Finset B := Sum.elim cz (fun y : Dec => cx y.1.1 ∪ y.1.2.biUnion cz) with hcs
  set A : Finset (Zt ⊕ Dec) → Prop := fun D =>
    (∀ m ∈ D.toLeft, ∀ m' ∈ D.toLeft, m ≠ m' → Disjoint (cz m) (cz m')) ∧
      ∀ y ∈ D.toRight, y.1.2 = D.toLeft.filter (near y.1.1) with hA
  set w : Zt ⊕ Dec → ℂ := Sum.elim τ (fun y : Dec => Complex.exp (b y.1.1 y.1.2) - 1) with hw
  -- a heavy object meeting `X` is in contact with every light object `(X, S)`
  have hct : ∀ (y : Dec) (m : Zt), near y.1.1 m → Contact cs (Sum.inr y) (Sum.inl m) := by
    intro y m hm hd
    exact hnear y.1.1 m hm (Finset.disjoint_of_subset_left Finset.subset_union_left hd)
  have hA0 : ∀ D, A D → ∀ t ∈ D, (cs t).Nonempty := by
    intro D _ t _
    rcases t with m | y
    · exact hz m
    · obtain ⟨m, hm⟩ := y.2.1
      obtain ⟨p, hp⟩ := hz m
      exact ⟨p, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, hm, hp⟩)⟩
  have hLoc : ∀ D, A D ↔ ∀ t ∈ D, A (comp cs D t) := by
    intro D
    constructor
    · rintro ⟨h1, h2⟩ t _
      refine ⟨fun m hm m' hm' hne => h1 m (toLeft_subset_toLeft (comp_subset D t) hm) m'
          (toLeft_subset_toLeft (comp_subset D t) hm') hne, fun y hy => ?_⟩
      have hyC := Finset.mem_toRight.mp hy
      rw [h2 y (Finset.mem_toRight.mpr (comp_subset D t hyC))]
      ext m
      simp only [Finset.mem_filter, Finset.mem_toLeft]
      constructor
      · rintro ⟨hm, hnm⟩
        exact ⟨comp_closed hyC hm (hct y m hnm), hnm⟩
      · rintro ⟨hm, hnm⟩
        exact ⟨comp_subset D t hm, hnm⟩
    · intro h
      refine ⟨fun m hm m' hm' hne => ?_, fun y hy => ?_⟩
      · by_contra hnd
        have hmD := Finset.mem_toLeft.mp hm
        have hm'C : (Sum.inl m' : Zt ⊕ Dec) ∈ comp cs D (Sum.inl m) :=
          comp_closed (self_mem_comp hmD) (Finset.mem_toLeft.mp hm') hnd
        exact hnd ((h _ hmD).1 m (Finset.mem_toLeft.mpr (self_mem_comp hmD)) m'
          (Finset.mem_toLeft.mpr hm'C) hne)
      · have hyD := Finset.mem_toRight.mp hy
        rw [(h _ hyD).2 y (Finset.mem_toRight.mpr (self_mem_comp hyD))]
        ext m
        simp only [Finset.mem_filter, Finset.mem_toLeft]
        constructor
        · rintro ⟨hm, hnm⟩
          exact ⟨comp_subset D _ hm, hnm⟩
        · rintro ⟨hm, hnm⟩
          exact ⟨comp_closed (self_mem_comp hyD) hm (hct y m hnm), hnm⟩
  rw [← decomposition (cs := cs) (A := A) hA0 hLoc w]
  clear_value A
  set S := univ.filter (fun Γ : Finset Zt => ∀ m ∈ Γ, ∀ m' ∈ Γ, m ≠ m' → Disjoint (cz m) (cz m')) with hS
  set Lt : Finset Zt → Finset Dec := fun Γ =>
    univ.filter (fun y : Dec => y.1.2 = Γ.filter (near y.1.1)) with hLt
  -- `exp ∑_X b_X(Γ_X)` is the product over the decorations `(X, Γ_X)`, `Γ_X ≠ ∅`
  have hexp : ∀ Γ : Finset Zt, Complex.exp (∑ x, b x (Γ.filter (near x))) =
      ∏ y ∈ Lt Γ, Complex.exp (b y.1.1 y.1.2) := by
    intro Γ
    rw [Complex.exp_sum, ← Finset.prod_filter_of_ne (p := fun x => (Γ.filter (near x)).Nonempty)]
    · refine Finset.prod_bij' (fun x hx => (⟨(x, Γ.filter (near x)), (Finset.mem_filter.1 hx).2,
          fun m hm => (Finset.mem_filter.1 hm).2⟩ : Dec)) (fun y _ => y.1.1) ?_ ?_ ?_ ?_ ?_
      · intro x _
        simp [hLt]
      · intro y hy
        have hy' : y.1.2 = Γ.filter (near y.1.1) := (Finset.mem_filter.1 hy).2
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        rw [← hy']
        exact y.2.1
      · intro x _
        rfl
      · intro y hy
        have hy' : y.1.2 = Γ.filter (near y.1.1) := (Finset.mem_filter.1 hy).2
        exact Subtype.ext (Prod.ext rfl hy'.symm)
      · intro x _
        rfl
    · intro x _ hx
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact hx (by rw [hne, hb0, Complex.exp_zero])
  have h1 : ∀ Γ : Finset Zt, (∏ m ∈ Γ, τ m) * Complex.exp (∑ x, b x (Γ.filter (near x))) =
      ∑ L ∈ (Lt Γ).powerset, (∏ y ∈ L, (Complex.exp (b y.1.1 y.1.2) - 1)) * ∏ m ∈ Γ, τ m := by
    intro Γ
    have h2 : ∏ y ∈ Lt Γ, Complex.exp (b y.1.1 y.1.2) =
        ∏ y ∈ Lt Γ, (1 + (Complex.exp (b y.1.1 y.1.2) - 1)) :=
      Finset.prod_congr rfl (fun y _ => by ring)
    rw [hexp, h2, Finset.prod_one_add, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun L _ => mul_comm _ _)
  refine (Finset.sum_congr rfl (fun Γ _ => h1 Γ)).trans ?_
  rw [Finset.sum_sigma' S (fun Γ => (Lt Γ).powerset)
    (fun Γ L => (∏ y ∈ L, (Complex.exp (b y.1.1 y.1.2) - 1)) * ∏ m ∈ Γ, τ m)]
  symm
  refine Finset.sum_nbij' (fun D => (⟨D.toLeft, D.toRight⟩ : Σ _ : Finset Zt, Finset Dec))
    (fun x => x.1.disjSum x.2) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    have hAD : A D := (Finset.mem_filter.mp hD).2
    rw [hA] at hAD
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAD.1⟩, ?_⟩
    rw [Finset.mem_powerset]
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAD.2 y hy⟩
  · rintro ⟨Γ, L⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hΓ, hL⟩ := hx
    rw [Finset.mem_powerset] at hL
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hA]
    refine ⟨?_, ?_⟩
    · simpa using (Finset.mem_filter.mp hΓ).2
    · intro y hy
      simp only [Finset.toRight_disjSum, Finset.toLeft_disjSum] at hy ⊢
      exact (Finset.mem_filter.mp (hL hy)).2
  · intro D _
    simp [Finset.toLeft_disjSum_toRight]
  · rintro ⟨Γ, L⟩ _
    simp
  · intro D _
    conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := D)]
    rw [Finset.prod_disjSum, mul_comm]
    rfl

end Decor

end Balaban.LargeField
