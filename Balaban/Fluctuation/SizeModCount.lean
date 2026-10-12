/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCells
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting connected sets of cells near a cube (the entropy count of (G2))

* `nbF r a F`: the cells at index distance `≤ r` from a set `F` of cells.
* `Acand a n t0`: the connected sets of at most `n` cells containing a cell near `t0`.
* `famT`: the pairs `(T, U)` of subsets of the neighbourhoods of such sets.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

section Count

variable {d n : ℕ} [NeZero n]

open Classical in
/-- The cells (aligned bases) at index distance `≤ r` from some cell of `F`. -/
noncomputable def nbF (r a : ℕ) (F : Finset (Torus d n)) : Finset (Torus d n) :=
  F.biUnion fun c => Finset.univ.filter fun v => Near r a c v

theorem mem_nbF {r a : ℕ} {F : Finset (Torus d n)} {v : Torus d n} :
    v ∈ nbF r a F ↔ ∃ c ∈ F, Near r a c v := by
  classical
  simp [nbF]

theorem card_nbF_le (r a : ℕ) (F : Finset (Torus d n)) :
    (nbF r a F).card ≤ F.card * (2 * r + 1) ^ d := by
  classical
  unfold nbF
  calc _ ≤ ∑ c ∈ F, (Finset.univ.filter fun v => Near r a c v).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ F, (2 * r + 1) ^ d := Finset.sum_le_sum fun c _ => card_near_le r a c
    _ = _ := by simp

theorem nbF_mono (r a : ℕ) {F G : Finset (Torus d n)} (h : F ⊆ G) : nbF r a F ⊆ nbF r a G := by
  intro v hv
  obtain ⟨c, hc, hcv⟩ := mem_nbF.1 hv
  exact mem_nbF.2 ⟨c, h hc, hcv⟩

open Classical in
/-- The connected sets of between `1` and `m` cells containing a cell near `t0`. -/
noncomputable def Acand (L a m : ℕ) (t0 : Torus d n) : Finset (Finset (Torus d n)) :=
  (Finset.univ.filter fun c => Near (L - 1) a c t0).biUnion fun c =>
    (Finset.Icc 1 m).biUnion fun k => Balaban.Polymer.animals (cellGraph d n a) c k

theorem mem_Acand {L a m : ℕ} {t0 : Torus d n} {A : Finset (Torus d n)} {c : Torus d n}
    (hc : c ∈ A) (hnear : Near (L - 1) a c t0) (hcard : A.card ≤ m)
    (hconn : ((cellGraph d n a).induce (A : Set (Torus d n))).Connected) :
    A ∈ Acand L a m t0 := by
  classical
  unfold Acand
  refine Finset.mem_biUnion.2 ⟨c, by simpa using hnear, Finset.mem_biUnion.2 ⟨A.card, ?_, ?_⟩⟩
  · exact Finset.mem_Icc.2 ⟨Finset.card_pos.2 ⟨c, hc⟩, hcard⟩
  · exact (Balaban.Polymer.mem_animals _).2 ⟨hc, rfl, hconn⟩

theorem card_Acand_le (L a m : ℕ) (t0 : Torus d n) :
    (Acand L a m t0 : Finset (Finset (Torus d n))).card ≤
      (2 * (L - 1) + 1) ^ d * (m * (3 ^ d) ^ (2 * m)) := by
  classical
  unfold Acand
  have hball := card_near_le (d := d) (n := n) (L - 1) a t0
  have hk : ∀ c : Torus d n, ∀ k ∈ Finset.Icc 1 m,
      (Balaban.Polymer.animals (cellGraph d n a) c k).card ≤ (3 ^ d) ^ (2 * m) := by
    intro c k hk
    refine (Balaban.Polymer.card_animals_le (cellGraph d n a) (Δ := 3 ^ d)
      (degree_cellGraph_le a) c k).trans ?_
    exact Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) (by
      have := (Finset.mem_Icc.1 hk).2; omega)
  have hc : ∀ c : Torus d n, ((Finset.Icc 1 m).biUnion fun k =>
      Balaban.Polymer.animals (cellGraph d n a) c k).card ≤ m * (3 ^ d) ^ (2 * m) := by
    intro c
    calc _ ≤ ∑ k ∈ Finset.Icc 1 m, (Balaban.Polymer.animals (cellGraph d n a) c k).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.Icc 1 m, (3 ^ d) ^ (2 * m) := Finset.sum_le_sum (hk c)
      _ = m * (3 ^ d) ^ (2 * m) := by simp
  calc _ ≤ ∑ c ∈ (Finset.univ.filter fun c => Near (L - 1) a c t0), ((Finset.Icc 1 m).biUnion fun k =>
          Balaban.Polymer.animals (cellGraph d n a) c k).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ (Finset.univ.filter fun c => Near (L - 1) a c t0), m * (3 ^ d) ^ (2 * m) :=
        Finset.sum_le_sum fun c _ => hc c
    _ = (Finset.univ.filter fun c => Near (L - 1) a c t0).card * (m * (3 ^ d) ^ (2 * m)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by
        have e : (Finset.univ.filter fun c : Torus d n => Near (L - 1) a c t0) =
            Finset.univ.filter fun c : Torus d n => Near (L - 1) a t0 c := by
          ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Near.symm, Near.symm⟩
        rw [e]; exact hball)

open Classical in
/-- The pairs `(T, U)`: `T` a set of cells near a set `A ∈ Acand`, `U` a set of cells next to them. -/
noncomputable def famT (L a m : ℕ) (t0 : Torus d n) : Finset (Finset (Torus d n) × Finset (Torus d n)) :=
  (Acand L a m t0).biUnion fun A =>
    (nbF (L - 1) a A).powerset ×ˢ (nbF 1 a (nbF (L - 1) a A)).powerset

theorem card_le_of_mem_Acand {L a m : ℕ} {t0 : Torus d n} {A : Finset (Torus d n)}
    (h : A ∈ Acand L a m t0) : A.card ≤ m := by
  classical
  unfold Acand at h
  obtain ⟨c, -, h⟩ := Finset.mem_biUnion.1 h
  obtain ⟨k, hk, h⟩ := Finset.mem_biUnion.1 h
  obtain ⟨-, hc, -⟩ := (Balaban.Polymer.mem_animals _).1 h
  rw [hc]; exact (Finset.mem_Icc.1 hk).2

theorem card_famT_le (L a m : ℕ) (t0 : Torus d n) :
    (famT L a m t0).card ≤ ((2 * (L - 1) + 1) ^ d * (m * (3 ^ d) ^ (2 * m))) *
      2 ^ (m * (2 * (L - 1) + 1) ^ d * (1 + 3 ^ d)) := by
  classical
  unfold famT
  have hper : ∀ A ∈ Acand L a m t0, (((nbF (L - 1) a A).powerset ×ˢ
      (nbF 1 a (nbF (L - 1) a A)).powerset : Finset _)).card ≤
      2 ^ (m * (2 * (L - 1) + 1) ^ d * (1 + 3 ^ d)) := by
    intro A hA
    have hAm := card_le_of_mem_Acand hA
    have h1 : (nbF (L - 1) a A).card ≤ m * (2 * (L - 1) + 1) ^ d :=
      (card_nbF_le _ _ A).trans (Nat.mul_le_mul_right _ hAm)
    have h2 : (nbF 1 a (nbF (L - 1) a A)).card ≤ m * (2 * (L - 1) + 1) ^ d * 3 ^ d :=
      (card_nbF_le _ _ _).trans (by simpa using Nat.mul_le_mul_right (3 ^ d) h1)
    rw [Finset.card_product, Finset.card_powerset, Finset.card_powerset, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc _ ≤ ∑ A ∈ Acand L a m t0, (((nbF (L - 1) a A).powerset ×ˢ
      (nbF 1 a (nbF (L - 1) a A)).powerset : Finset _)).card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ Acand L a m t0, 2 ^ (m * (2 * (L - 1) + 1) ^ d * (1 + 3 ^ d)) :=
        Finset.sum_le_sum hper
    _ = (Acand L a m t0).card * 2 ^ (m * (2 * (L - 1) + 1) ^ d * (1 + 3 ^ d)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_Acand_le L a m t0)

end Count

end Balaban.Fluctuation
