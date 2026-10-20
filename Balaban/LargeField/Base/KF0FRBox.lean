/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRProd
public import Balaban.LargeField.Base.KF0PolymerLift
public import Balaban.LargeField.Base.KF0FRBall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRBox`: the block supports of the terms (route FR, (B))

`notes/phase1/KF0-FR.md` (B). On the torus of side `ℓ = s m` with blocks of side `s`, the block box
of a block `b` is `{b + δ : δ ∈ {-1,0,1}^d}` (`blockBox`): a connected set of blocks
(`isAnimal_blockBox`) with at most `3^d` blocks (`card_blockBox_le`). A site at `ℓ¹` distance
`r < s` from `x` lies in a block of the box of the block of `x` (`blockOf_mem_blockBox`). The block
support of a term (`frBox`) is the box of the block of its base site; when `2R + 1 < s` it
contains the blocks of the site support of the term (`frSupp_subset_siteSet_frBox`), and at most
`(1+d) s^d |X|` terms have the block support `X` (`card_frBox_eq_le`).
-/

@[expose] public section

open Finset Balaban.Green Balaban.Polymer

namespace Balaban.LargeField.KF0FR

noncomputable section

variable {d m : ℕ} [NeZero m]

/-- The block box of a block: the blocks `b + δ`, `δ ∈ {-1, 0, 1}^d`. -/
def blockBox (b : Torus d m) : Finset (Torus d m) :=
  (Fintype.piFinset fun _ : Fin d => ({-1, 0, 1} : Finset (ZMod m))).image (b + ·)

omit [NeZero m] in
theorem mem_blockBox_self (b : Torus d m) : b ∈ blockBox b :=
  Finset.mem_image.2 ⟨0, Fintype.mem_piFinset.2 fun _ => by simp, by simp⟩

omit [NeZero m] in
theorem card_blockBox_le (b : Torus d m) : (blockBox b).card ≤ 3 ^ d := by
  unfold blockBox
  refine Finset.card_image_le.trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ _i : Fin d, ({-1, 0, 1} : Finset (ZMod m)).card ≤ ∏ _i : Fin d, 3 :=
        Finset.prod_le_prod fun _ _ => Finset.card_le_three
    _ = 3 ^ d := by simp

/-- The truncation of a displacement to a set of coordinates. -/
def truncDisp (δ : Torus d m) (S : Finset (Fin d)) : Torus d m := fun μ => if μ ∈ S then δ μ else 0

omit [NeZero m] in
theorem truncDisp_univ (δ : Torus d m) : truncDisp δ Finset.univ = δ := by
  funext μ; simp [truncDisp]

omit [NeZero m] in
theorem truncDisp_insert (δ : Torus d m) {μ : Fin d} {S : Finset (Fin d)} (hμ : μ ∉ S) :
    truncDisp δ (insert μ S) = truncDisp δ S + Pi.single μ (δ μ) := by
  funext ν
  by_cases hν : ν = μ
  · subst hν; simp [truncDisp, hμ]
  · simp [truncDisp, hν]

omit [NeZero m] in
/-- **The block box is connected.** -/
theorem isAnimal_blockBox (b : Torus d m) : IsAnimal (blockGraph d m) (blockBox b) := by
  set P := Fintype.piFinset fun _ : Fin d => ({-1, 0, 1} : Finset (ZMod m)) with hP
  set R : Torus d m → Torus d m → Prop :=
    fun a c => a ∈ blockBox b ∧ c ∈ blockBox b ∧ (blockGraph d m).Adj a c with hR
  have hmemP : ∀ δ ∈ P, ∀ S, truncDisp δ S ∈ P := by
    intro δ hδ S
    rw [Fintype.mem_piFinset] at hδ ⊢
    intro μ
    unfold truncDisp
    split_ifs
    · exact hδ μ
    · simp
  have hbox : ∀ δ ∈ P, b + δ ∈ blockBox b := fun δ hδ => Finset.mem_image.2 ⟨δ, hδ, rfl⟩
  have hRsymm : ∀ a c, R a c → R c a := fun a c h => ⟨h.2.1, h.1, h.2.2.symm⟩
  -- each point of the box reaches the center
  have hreach : ∀ δ ∈ P, ∀ S : Finset (Fin d),
      Relation.ReflTransGen R (b + truncDisp δ S) b := by
    intro δ hδ S
    induction S using Finset.induction_on with
    | empty =>
      have : truncDisp δ ∅ = 0 := by funext μ; simp [truncDisp]
      rw [this, add_zero]
    | insert μ S hμ ih =>
      have hδμ : δ μ = -1 ∨ δ μ = 0 ∨ δ μ = 1 := by
        have := (Fintype.mem_piFinset.1 hδ) μ
        simpa using this
      rw [truncDisp_insert δ hμ, ← add_assoc]
      set c := b + truncDisp δ S
      have hc : c ∈ blockBox b := hbox _ (hmemP δ hδ S)
      have ha : c + Pi.single μ (δ μ) ∈ blockBox b := by
        rw [add_assoc, ← truncDisp_insert δ hμ]; exact hbox _ (hmemP δ hδ _)
      by_cases heq : c + Pi.single μ (δ μ) = c
      · rw [heq]; exact ih
      · refine Relation.ReflTransGen.head ⟨ha, hc, heq, μ, ?_⟩ ih
        rcases hδμ with h1 | h1 | h1
        · left; rw [h1, add_assoc, ← Pi.single_add, neg_add_cancel, Pi.single_zero, add_zero]
        · exact absurd (by rw [h1, Pi.single_zero, add_zero]) heq
        · right; rw [h1]
  rw [isAnimal_iff]
  refine ⟨⟨b, mem_blockBox_self b⟩, fun p hp q hq => ?_⟩
  obtain ⟨δ₁, hδ₁, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨δ₂, hδ₂, rfl⟩ := Finset.mem_image.1 hq
  have h1 := hreach δ₁ hδ₁ Finset.univ
  have h2 := hreach δ₂ hδ₂ Finset.univ
  rw [truncDisp_univ] at h1 h2
  have hsym : ∀ p q, Relation.ReflTransGen R p q → Relation.ReflTransGen R q p := by
    intro p q h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hRsymm _ _ hbc) ih
  exact h1.trans (hsym _ _ h2)

/-- Two integers at distance less than `s` have quotients by `s` at distance at most `1`. -/
theorem abs_ediv_sub_le_one {s : ℤ} (hs : 0 < s) (a k : ℤ) (hk : |k| < s) :
    -1 ≤ (a + k) / s - a / s ∧ (a + k) / s - a / s ≤ 1 := by
  have h1 := Int.mul_ediv_add_emod a s
  have h2 := Int.mul_ediv_add_emod (a + k) s
  have h3 := Int.emod_nonneg a hs.ne'
  have h4 := Int.emod_lt_of_pos a hs
  have h5 := Int.emod_nonneg (a + k) hs.ne'
  have h6 := Int.emod_lt_of_pos (a + k) hs
  have hk1 := le_abs_self k
  have hk2 := neg_abs_le k
  constructor
  · by_contra hc
    push Not at hc
    have : (a + k) / s - a / s ≤ -2 := by omega
    nlinarith
  · by_contra hc
    push Not at hc
    have : 2 ≤ (a + k) / s - a / s := by omega
    nlinarith

variable {s : ℕ} [NeZero s]

/-- **A site at distance `r < s` from `x` lies in the box of the block of `x`.** -/
theorem blockOf_mem_blockBox {x y : Torus d (s * m)} {r : ℕ} (hr : r < s)
    (hxy : torusDist d (s * m) x y ≤ r) : blockOf d s m y ∈ blockBox (blockOf d s m x) := by
  have hs : (0 : ℤ) < s := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne s)
  refine Finset.mem_image.2 ⟨blockOf d s m y - blockOf d s m x,
    Fintype.mem_piFinset.2 fun μ => ?_, by abel⟩
  set k : ℤ := cycRep (y μ - x μ) with hk
  have hk1 : |k| ≤ r := by
    have h1 : ((cycRep (x μ - y μ)).natAbs : ℝ) ≤ torusDist d (s * m) x y :=
      Finset.single_le_sum (f := fun i => ((cycRep (x i - y i)).natAbs : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ μ)
    have h2 : (cycRep (y μ - x μ)).natAbs = (cycRep (x μ - y μ)).natAbs := by
      rw [← neg_sub, natAbs_cycRep_neg]
    have h3 : ((cycRep (y μ - x μ)).natAbs : ℝ) ≤ r := by rw [h2]; exact h1.trans hxy
    rw [hk, Int.abs_eq_natAbs]
    exact_mod_cast h3
  have hkr : |k| < s := lt_of_le_of_lt hk1 (by exact_mod_cast hr)
  set a : ℤ := ((x μ).val : ℤ) with ha
  have hxa : x μ = ((a : ℤ) : ZMod (s * m)) := by rw [ha]; simp
  have hya : y μ = ((a + k : ℤ) : ZMod (s * m)) := by
    rw [Int.cast_add, ← hxa, hk, cast_cycRep]; ring
  have hbx : blockOf d s m x μ = ((a / s : ℤ) : ZMod m) := by
    have := Balaban.KF0Lift.blockCoord_intCast' (ℓ := s * m) (s := s) (m := m)
      (Nat.pos_of_ne_zero (NeZero.ne s)) rfl a
    rw [← hxa] at this
    exact this
  have hby : blockOf d s m y μ = (((a + k) / s : ℤ) : ZMod m) := by
    have := Balaban.KF0Lift.blockCoord_intCast' (ℓ := s * m) (s := s) (m := m)
      (Nat.pos_of_ne_zero (NeZero.ne s)) rfl (a + k)
    rw [← hya] at this
    exact this
  have hdiff : (blockOf d s m y - blockOf d s m x) μ = (((a + k) / s - a / s : ℤ) : ZMod m) := by
    rw [Pi.sub_apply, hby, hbx, Int.cast_sub]
  obtain ⟨hl, hu⟩ := abs_ediv_sub_le_one hs a k hkr
  rw [hdiff]
  have : (a + k) / s - a / s = -1 ∨ (a + k) / s - a / s = 0 ∨ (a + k) / s - a / s = 1 := by omega
  rcases this with h | h | h <;> rw [h] <;> simp

/-- The base site of a term. -/
def frBase {ℓ : ℕ} : FRTerm d ℓ → Torus d ℓ
  | Sum.inl x => x
  | Sum.inr (x, _) => x

/-- The site support of a term is a ball around its base site. -/
theorem frSupp_eq_torusBall {ℓ : ℕ} [NeZero ℓ] (R : ℕ) (t : FRTerm d ℓ) :
    frSupp R t = torusBall (frBase t) (match t with
      | Sum.inl _ => (2 * R + 1 : ℕ)
      | Sum.inr _ => (R + 1 : ℕ)) := by
  rcases t with x | ⟨x, μ⟩
  · ext y; simp [frSupp, torusBall, frBase]
  · ext y; simp [frSupp, torusBall, frBase]

theorem frBase_mem_frSupp {ℓ : ℕ} [NeZero ℓ] (R : ℕ) (t : FRTerm d ℓ) : frBase t ∈ frSupp R t := by
  rcases t with x | ⟨x, μ⟩
  · exact mem_frSupp_inl_self R x
  · simp [frSupp, frBase, torusDist_self_eq]; positivity

/-- **The block support of a term**: the blocks of its site support. -/
def frBox (R : ℕ) (t : FRTerm d (s * m)) : Finset (Torus d m) :=
  (frSupp R t).image (blockOf d s m)

theorem frBox_nonempty (R : ℕ) (t : FRTerm d (s * m)) : (frBox R t).Nonempty :=
  ⟨_, Finset.mem_image_of_mem _ (frBase_mem_frSupp R t)⟩

/-- **The block support of a term is connected.** -/
theorem isAnimal_frBox (R : ℕ) (t : FRTerm d (s * m)) : IsAnimal (blockGraph d m) (frBox R t) := by
  refine Balaban.LargeField.KF0Gas.isAnimal_image_blockOf_of_nnConnected
    ⟨_, frBase_mem_frSupp R t⟩ ?_
  rw [frSupp_eq_torusBall]
  exact nnConnected_torusBall _ _

/-- The sites of the support of a term are at distance at most `2R + 1` from its base site. -/
theorem torusDist_frBase_le {ℓ : ℕ} [NeZero ℓ] {R : ℕ} {t : FRTerm d ℓ} {y : Torus d ℓ}
    (hy : y ∈ frSupp R t) : torusDist d ℓ (frBase t) y ≤ (2 * R + 1 : ℕ) := by
  rcases t with x | ⟨x, μ⟩
  · simpa [frSupp, frBase] using hy
  · simp only [frSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [frBase]; push_cast; linarith

/-- The block support contains the blocks of the site support. -/
theorem blockOf_mem_frBox {R : ℕ} {t : FRTerm d (s * m)} {y : Torus d (s * m)}
    (hy : y ∈ frSupp R t) : blockOf d s m y ∈ frBox R t :=
  Finset.mem_image_of_mem _ hy

/-- **The block support lies in the block box of the base site** (`2R + 1 < s`). -/
theorem frBox_subset_blockBox {R : ℕ} (hR : 2 * R + 1 < s) (t : FRTerm d (s * m)) :
    frBox R t ⊆ blockBox (blockOf d s m (frBase t)) := by
  intro b hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
  exact blockOf_mem_blockBox hR (torusDist_frBase_le hy)

/-- **The terms with a given block support**: at most `(1+d) s^d |X|`. -/
theorem card_frBox_eq_le (R : ℕ) (X : Finset (Torus d m)) :
    (Finset.univ.filter fun t : FRTerm d (s * m) => frBox R t = X).card ≤
      (1 + d) * (s ^ d * X.card) := by
  have hsub : Finset.univ.filter (fun t : FRTerm d (s * m) => frBox R t = X) ⊆
      ((siteSet d s m X).disjSum ((siteSet d s m X) ×ˢ (Finset.univ : Finset (Fin d)))) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have hb : frBase t ∈ siteSet d s m X := by
      rw [mem_siteSet, ← ht.2]; exact blockOf_mem_frBox (frBase_mem_frSupp R t)
    rcases t with x | ⟨x, μ⟩
    · exact Finset.inl_mem_disjSum.2 hb
    · exact Finset.inr_mem_disjSum.2 (Finset.mem_product.2 ⟨hb, Finset.mem_univ _⟩)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = (siteSet d s m X).card + (siteSet d s m X).card * d := by
        rw [Finset.card_disjSum, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ = (1 + d) * (s ^ d * X.card) := by rw [card_siteSet]; ring

end

end Balaban.LargeField.KF0FR
