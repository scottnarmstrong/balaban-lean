/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ChainGraph
public import Balaban.LargeField.R.WindowGenGlue
import Mathlib.Tactic.Linarith

/-!
# The boundary piece `𝔹_k(U_k) ∩ Z^c ∩ U^∼_k` has lower layers

The earlier premise of `deltaPsi_le_pieces` was "every site of `Ω₁(𝔹_k(U_k))` in `U^∼_k ∖ Z` lies in the top layer
`k`".  `not_bdry_top_of_data` shows that this is false as soon as `k ≥ 2`, `Z ≠ ∅`, `Ω_k(𝔹_k(U_k)) ≠` torus,
`Z ⊆ Ω_k(𝔹_k(U_k))` (`U_k ⊇ Z`), the data sites of `𝔹_k(U_k)` lie in `U^∼_k` (Lemma II.2.3 (c)) and the separation
`ϱ L^{k-1} ≥ 1`: the cubes next to `Ω_k` lie in `Ω_{k-1} ∖ Ω_k ⊆ U^∼_k ∖ Z`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

section Cross

set_option linter.unusedSectionVars false

variable {d m : ℕ} [NeZero m]

theorem reach_single_nn (x : Torus d m) (μ : Fin d) (c : ℕ) :
    Relation.ReflTransGen NNAdj x (x + Pi.single μ (c : ZMod m)) := by
  induction c with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ c ih =>
    refine ih.tail ⟨μ, Or.inl ?_⟩
    ext ν
    by_cases h : ν = μ
    · subst h; simp; ring
    · simp [h]

theorem reach_sum_nn (x : Torus d m) (v : Fin d → ZMod m) (T : Finset (Fin d)) :
    Relation.ReflTransGen NNAdj x (x + ∑ μ ∈ T, Pi.single μ (v μ)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := reach_single_nn (x + ∑ μ ∈ T, Pi.single μ (v μ)) a (v a).val
    rw [ZMod.natCast_zmod_val] at h1
    have e : x + (Pi.single a (v a) + ∑ μ ∈ T, Pi.single μ (v μ)) =
        x + ∑ μ ∈ T, Pi.single μ (v μ) + Pi.single a (v a) := by abel
    rw [e]
    exact ih.trans h1

/-- A nonempty proper subset of the torus has a nearest-neighbour pair `p ∈ A`, `q ∉ A`. -/
theorem exists_nnAdj_crossing {A : Finset (Torus d m)} (hne : A.Nonempty) (hproper : ∃ x, x ∉ A) :
    ∃ p ∈ A, ∃ q, q ∉ A ∧ NNAdj p q := by
  classical
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hx⟩ := hproper
  have hr := reach_sum_nn y (x - y) Finset.univ
  rw [Finset.univ_sum_single] at hr
  have e : y + (x - y) = x := by abel
  rw [e] at hr
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hy hx
  | @head a b hab _ ih =>
    by_cases hb : b ∈ A
    · exact ih hb (by abel)
    · exact ⟨a, by assumption, b, hb, hab⟩

end Cross

section Bdry

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The premise "boundary-piece sites lie in the top layer" is false.**  Let `G'` be `𝔹_k(U_k)`, `Z` a nonempty
set of sites with `Z ⊆ Ω_k(G')`, `Ω_k(G') ≠` torus, `Ω₁(G') ⊆ U^∼` (data sites, Lemma II.2.3 (c)), `k ≥ 2` and
`ϱ L^{k-1} ≥ 1`.  Then some site of `Ω₁(G')` lies in `U^∼ ∖ Z` but not in the layer `k` of `G'`. -/
theorem not_bdry_top_of_data (G' : GeneratingSet d L N₀ k ϱ) (hk : 2 ≤ k) (hϱ : 1 ≤ ϱ * (L : ℝ) ^ (k - 1))
    {Z Unb : Finset (Torus d (N₀ * L ^ k))} (hZne : Z.Nonempty) (hZ : ∀ x ∈ Z, x ∈ G'.Ω k)
    (hpr : ∃ x, x ∉ G'.Ω k) (hU : ∀ x ∈ G'.Ω 1, x ∈ Unb) :
    ¬ (∀ x ∈ Unb, x ∉ Z → x ∈ G'.Ω 1 → x ∈ G'.layer k) := by
  intro hbl
  obtain ⟨z, hz⟩ := hZne
  obtain ⟨p, hp, q, hq, hadj⟩ := exists_nnAdj_crossing (A := G'.Ω k) ⟨z, hZ z hz⟩ hpr
  have hq1 : q ∈ G'.Ω (k - 1) := by
    by_contra hnot
    have hs := G'.separation (k - 1) (by omega) (by omega) q hnot p (by
      have : k - 1 + 1 = k := by omega
      rw [this]; exact hp)
    obtain ⟨μ, hμ⟩ := hadj
    have hd := torusDist_nnAdj_le (x := q) (y := p) ⟨μ, hμ.symm⟩
    linarith
  have hq1' : q ∈ G'.Ω 1 := G'.Ω_antitone le_rfl (by omega) (by omega) hq1
  have := hbl q (hU q hq1') (fun h => hq (hZ q h)) hq1'
  exact hq ((GeneratingSet.mem_layer _).1 this).1

end Bdry

end Balaban.LargeField
