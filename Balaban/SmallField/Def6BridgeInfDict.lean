/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfSum

/-!
# The bridge Def-6 to I-6 from the infinite-volume family `T∞`: the dictionary

The fields of `ℤ^d` of a configuration (`fieldInfOf`, `hInfOf`) pull back to the torus fields
`fieldOf`, `hOf` of the finite-torus bridge (`pullFld_fieldInfOf`); the centred term of `T∞`
(`EauxInf`, `termLInf`) is the centred term of every torus on which the polymer does not wind
(`EauxInf_eq`, `termLInf_eq`, from `Einf_eq_torus`).  The size of a polymer of `T∞` is
`dInf`, the supremum over the tori of the sequence on which it is a non-winding polymer of the
covering sizes of its lifts (bounded by `sizeJ_le_ncard_sq`).
-/


@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The `j`-block of a fine site of `ℤ^d` (floor division by `L^j`). -/
def blockOf (L j : ℕ) (z : Fin d → ℤ) : Fin d → ℤ := fun μ => z μ / ((L ^ j : ℕ) : ℤ)

theorem blockOf_fineLift [NeZero N₁] (j : ℕ) (x : CTorus d L N₁ m₁ k) :
    blockOf L j (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x := by
  funext μ
  have hD : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by
    exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  simp only [blockOf, fineLift]
  rw [add_comm, Int.add_mul_ediv_right _ _ hD.ne']
  have h1 : (((x μ).val % L ^ j : ℕ) : ℤ) < ((L ^ j : ℕ) : ℤ) := by
    exact_mod_cast Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
  rw [Int.ediv_eq_zero_of_lt (by positivity) h1, zero_add]

/-- The field of `ℤ^d` of a configuration `c` of the polymer `X'`: `c` on the blocks of `X'`, the
constant `e_{i₀}` elsewhere. -/
def fieldInfOf (L j : ℕ) (i₀ : Fin N) (X' : Finset (Fin d → ℤ)) (c : Cfg d N X') : InfFld d N :=
  fun z i => if h : blockOf L j z ∈ X' then c (Sum.inl (⟨_, h⟩, i)) else
    (Pi.single i₀ 1 : Fin N → ℂ) i

/-- The field `h = b / ν_j` of a configuration on `ℤ^d` (a constant). -/
noncomputable def hInfOf (νj : ℝ) (X' : Finset (Fin d → ℤ)) (c : Cfg d N X') : InfFld d N :=
  fun _ i => c (Sum.inr i) / (νj : ℂ)

theorem pullFld_fieldInfOf [NeZero N₁] (j : ℕ) (i₀ : Fin N) (X' : Finset (Fin d → ℤ))
    (c : Cfg d N X') :
    pullFld (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (fieldInfOf L j i₀ X' c) =
      fieldOf j i₀ X' c := by
  funext x i
  simp only [pullFld, fieldInfOf, fieldOf, blockOf_fineLift]

omit [NeZero L] in
theorem pullFld_hInfOf [NeZero N₁] (j : ℕ) (νj : ℝ) (X' : Finset (Fin d → ℤ)) (c : Cfg d N X') :
    pullFld (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (hInfOf νj X' c) = hOf νj X' c := rfl

omit [NeZero L] in
theorem blockPt_zero [NeZero N₁] (j : ℕ) :
    blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (0 : Fin d → ℤ) = 0 := by
  funext μ; simp [blockPt]


section Size

open Classical in
/-- **A crude upper bound of the covering size**: `d_j(Y) ≤ |Y|²` for a polymer `Y ∈ 𝒟_j`
(the cost of the structure with all bonds between adjacent sites of `Y`, at most `|Y|²` bonds of
weight `≤ 1`). -/
theorem sizeJ_le_ncard_sq [NeZero N₁] {m₀ j : ℕ} {Y : Set (CTorus d L N₁ m₁ k)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j Y) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j Y ≤ (Y.ncard : ℝ) ^ 2 := by
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hcon⟩ := hY
  set W : Finset (CTorus d L N₁ m₁ k) := (Set.toFinite Y).toFinset with hW
  have hWY : ∀ x, x ∈ W ↔ x ∈ Y := fun x => by simp [hW]
  set E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k) :=
    (W ×ˢ W).filter (fun p => Nbr p.1 p.2) with hE
  have hcs : ConnStruct W E := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, (hWY x).2 hx⟩
    · intro p hp
      simp only [hE, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨hp.1.1, hp.1.2, hp.2⟩
    · intro x hx y hy
      refine Relation.ReflTransGen.mono ?_ x y (hcon x ((hWY x).1 hx) y ((hWY y).1 hy))
      intro a b ⟨ha, hb, hab⟩
      left
      simp only [hE, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨(hWY a).2 ha, (hWY b).2 hb⟩, hab⟩
  have hmeet : MeetsOne m₀ j 𝒦 W := by
    intro b hb
    have hpos : 0 < L * cellSide L m₀ m₁ j := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L))
      (cellSide_pos m₀ m₁ j)
    exact ⟨b, (hWY b).2 ((hK1 b hb).2 (mem_box_self b hpos)), mem_box_self b hpos⟩
  have hmem : bondCost (scaleW L m₀ m₁ j) E ∈ {x | ∃ 𝒦 W E, ChosenOne m₀ j Y 𝒦 ∧ ConnStruct W E ∧
      (↑W ⊆ Y) ∧ MeetsOne m₀ j 𝒦 W ∧ x = bondCost (scaleW L m₀ m₁ j) E} :=
    ⟨𝒦, W, E, ⟨hK1, hK2⟩, hcs, fun x hx => (hWY x).1 hx, hmeet, rfl⟩
  have hbdd : BddBelow {x | ∃ 𝒦 W E, ChosenOne m₀ j Y 𝒦 ∧ ConnStruct W E ∧
      (↑W ⊆ Y) ∧ MeetsOne m₀ j 𝒦 W ∧ x = bondCost (scaleW L m₀ m₁ j) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    refine Finset.sum_nonneg fun p _ => ?_
    unfold scaleW; positivity
  refine (csInf_le hbdd hmem).trans ?_
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ (m₀ + m₁ + j) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hw : ∀ p : CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k, scaleW L m₀ m₁ j p.1 p.2 ≤ 1 := by
    intro p
    unfold scaleW
    exact inv_le_one_of_one_le₀ hL1
  calc bondCost (scaleW L m₀ m₁ j) E ≤ ∑ p ∈ E, (1 : ℝ) := Finset.sum_le_sum fun p _ => hw p
    _ = E.card := by simp
    _ ≤ (W.card : ℝ) ^ 2 := by
        have : E.card ≤ (W ×ˢ W).card := Finset.card_le_card (Finset.filter_subset _ _)
        rw [Finset.card_product] at this
        calc (E.card : ℝ) ≤ ((W.card * W.card : ℕ) : ℝ) := by exact_mod_cast this
          _ = (W.card : ℝ) ^ 2 := by push_cast; ring
    _ = (Y.ncard : ℝ) ^ 2 := by
        rw [hW, Set.ncard_eq_toFinset_card Y (Set.toFinite Y)]


variable (L m₁ k) in
/-- `X'` is a good shape on the `n`-th torus of the sequence: it does not wind and its lift is a
polymer of `𝒟_j`. -/
def GoodAt (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) (n : ℕ) : Prop :=
  haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  NonWind L (torusSeq L m₀ n) m₁ k j X' ∧
    IsPolyDom (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X')

variable (L m₁ k) in
/-- The covering size of the lift of `X'` on the `n`-th torus of the sequence. -/
noncomputable def sizeSeq (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) (n : ℕ) : ℝ :=
  haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  sizeJ (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) m₀ j
    (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X')

omit [NeZero L] in
theorem infPoly_iff_goodAt {m₀ j : ℕ} {X' : Finset (Fin d → ℤ)} :
    InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' ↔ ∀ᶠ n in atTop, GoodAt L m₁ k m₀ j X' n :=
  Iff.rfl

variable (L m₁ k) in
/-- **The size of a polymer of `T∞`**: the supremum of the covering sizes of its lifts on the tori
of the sequence on which it is a non-winding polymer (these are bounded, `sizeSeq_le`). -/
noncomputable def dInf (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) : ℝ :=
  ⨆ n : {n : ℕ // GoodAt L m₁ k m₀ j X' n}, sizeSeq L m₁ k m₀ j X' n.1

theorem sizeSeq_nonneg (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) (n : ℕ) :
    0 ≤ sizeSeq L m₁ k m₀ j X' n := by
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  exact treeLenCovOne_nonneg _ _ _

theorem sizeSeq_le {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)} {n : ℕ}
    (hn : GoodAt L m₁ k m₀ j X' n) :
    sizeSeq L m₁ k m₀ j X' n ≤ ((X'.card : ℝ) * ((L : ℝ) ^ j) ^ d) ^ 2 := by
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  unfold sizeSeq
  refine (sizeJ_le_ncard_sq hn.2).trans ?_
  rw [ncard_Ypoly hjk hn.1]
  push_cast
  rfl

theorem bddAbove_sizeSeq {m₀ j : ℕ} (hjk : j ≤ k) (X' : Finset (Fin d → ℤ)) :
    BddAbove (Set.range fun n : {n : ℕ // GoodAt L m₁ k m₀ j X' n} => sizeSeq L m₁ k m₀ j X' n.1) :=
  ⟨((X'.card : ℝ) * ((L : ℝ) ^ j) ^ d) ^ 2, by
    rintro _ ⟨n, rfl⟩; exact sizeSeq_le hjk n.2⟩

theorem sizeSeq_le_dInf {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)} {n : ℕ}
    (hn : GoodAt L m₁ k m₀ j X' n) : sizeSeq L m₁ k m₀ j X' n ≤ dInf L m₁ k m₀ j X' :=
  le_ciSup (bddAbove_sizeSeq hjk X') (⟨n, hn⟩ : {n : ℕ // GoodAt L m₁ k m₀ j X' n})

theorem dInf_nonneg {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)} {n : ℕ}
    (hn : GoodAt L m₁ k m₀ j X' n) : 0 ≤ dInf L m₁ k m₀ j X' :=
  (sizeSeq_nonneg m₀ j X' n).trans (sizeSeq_le_dInf hjk hn)

omit [NeZero L] in
theorem exists_goodAt_gt {m₀ j : ℕ} {X' : Finset (Fin d → ℤ)} {n₀ : ℕ}
    (hn₀ : GoodAt L m₁ k m₀ j X' n₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, GoodAt L m₁ k m₀ j X' n ∧ dInf L m₁ k m₀ j X' - ε < sizeSeq L m₁ k m₀ j X' n := by
  have : Nonempty {n : ℕ // GoodAt L m₁ k m₀ j X' n} := ⟨⟨n₀, hn₀⟩⟩
  obtain ⟨⟨n, hn⟩, h⟩ := exists_lt_of_lt_ciSup (f := fun n : {n : ℕ // GoodAt L m₁ k m₀ j X' n} =>
    sizeSeq L m₁ k m₀ j X' n.1) (show dInf L m₁ k m₀ j X' - ε < dInf L m₁ k m₀ j X' by linarith)
  exact ⟨n, hn, h⟩

end Size

section Terms

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)

/-- **The term of `T∞` in the centred coordinates**: `ℰ_∞(0, X'; ψ, h)` at the fields of `ℤ^d`
of a configuration of the polymer `X'`. -/
noncomputable def EauxInf (m₀ j : ℕ) (i₀ : Fin N) (νj : ℝ) (X' : Finset (Fin d → ℤ))
    (c : Cfg d N X') : ℂ :=
  Einf m₀ Tm j 0 X' (fieldInfOf L j i₀ X' c) (hInfOf νj X' c)

variable {Tm}

/-- On every torus on which `X'` is a non-winding polymer the centred term of `T∞` is the centred
class term of the torus. -/
theorem EauxInf_eq (hT : TorusIndep P.m₀ Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N)
    (νj : ℝ) {X' : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (N₁ : ℕ) [NeZero N₁]
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (c : Cfg d N X') :
    EauxInf Tm P.m₀ j i₀ νj X' c = Eaux (Tm N₁) j i₀ νj X' c := by
  unfold EauxInf Eaux
  rw [Einf_eq_torus hT hj1 hjk h0 hX _ _ N₁ hnw hpd, pullFld_fieldInfOf, pullFld_hInfOf,
    blockPt_zero]

open Classical in
/-- **The term of the infinite-volume lifted family**: as `termL`, with the centred term of `T∞`. -/
noncomputable def termLInf (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (m₀ j : ℕ) (i₀ : Fin N) (νj ρ : ℝ) (X' : Finset (Fin d → ℤ)) (c : Cfg d N X') : ℂ :=
  if h : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ Metric.ball (refPt i₀ νj X') ρ then
    EauxInf Tm m₀ j i₀ νj X' (rotCfgL (Classical.choose h) X' c)
  else EauxInf Tm m₀ j i₀ νj X' c

/-- The term of the infinite-volume lifted family is the term `termL` of every torus on which the
polymer does not wind. -/
theorem termLInf_eq (hT : TorusIndep P.m₀ Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N)
    (νj ρ : ℝ) {X' : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (N₁ : ℕ) [NeZero N₁]
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (c : Cfg d N X') :
    termLInf Tm P.m₀ j i₀ νj ρ X' c = termL (Tm N₁) j i₀ νj ρ X' c := by
  unfold termLInf termL
  simp only [EauxInf_eq hT hj1 hjk i₀ νj h0 hX N₁ hnw hpd]

end Terms

end Balaban.SmallField.Def6
