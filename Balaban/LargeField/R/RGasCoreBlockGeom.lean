/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreConn

/-!
# Block completions of halos (W872, blocker 4): geometry

For a set `X` of cubes of the torus `𝕋_k` and `s ≥ 1`, the block completion of the halo
`nbhd m X` is the union `B` of the boxes `x + [0, s)^d` of `s^d` cubes over the cubes `x` of the halo.
It satisfies `nbhd m X ⊆ B ⊆ nbhd (m + s - 1) X`, every point of `B` lies in a box inside `B`, and
`B` is nearest-neighbour connected when the halo is.  The preimage of such a set under the cube
index of a fine torus is a union of aligned boxes of `s` cells: this is the property
`IsPiPrimeUnion` of `Fluctuation/SizeModDefs.lean` for `s = L`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale

local notation "lbox" => Balaban.Localization.box

section Cube

variable {d n : ℕ} [NeZero n]

/-- A point of a box of side `s` is at sup-distance `≤ s - 1` from the corner. -/
theorem supDist_le_of_mem_lbox {x q : Torus d n} {s : ℕ} (hq : q ∈ lbox x s) :
    supDist x q ≤ s - 1 := by
  obtain ⟨w, hw, rfl⟩ := hq
  rw [supDist_le_iff]
  intro i
  refine (cycNorm_le_iff _ _).2 ⟨-(w i : ℤ), ?_, ?_⟩
  · have := hw i
    rw [abs_neg, Nat.abs_cast]
    exact_mod_cast Nat.le_sub_one_of_lt this
  · simp [natT]

/-- A box is nearest-neighbour connected inside itself. -/
theorem box_reach_nn (x : Torus d n) (s : ℕ) {u : Torus d n} (hu : u ∈ lbox x s) :
    Relation.ReflTransGen (fun a b => a ∈ lbox x s ∧ b ∈ lbox x s ∧ NNAdj a b) x u := by
  obtain ⟨w, hw, rfl⟩ := hu
  have h := reach_box x w (lbox x s) (fun w' hw' => ⟨w', fun μ => (hw' μ).trans_lt (hw μ), rfl⟩)
  refine Relation.ReflTransGen.mono (fun a b hab => ⟨hab.2.1, hab.2.2, ?_⟩) _ _ h
  exact hab.1.2

/-- **Block completion of a halo.**  For `s ≥ 1` the union `B` of the boxes of side `s` based at the
points of `nbhd m X` contains `nbhd m X`, lies in `nbhd (m + (s-1)) X`, contains with each of its
points a box of side `s` through that point, and is nearest-neighbour connected as soon as
`nbhd m X` is. -/
theorem exists_block_completion (X : Set (Torus d n)) (m s : ℕ) (hs : 0 < s) :
    ∃ B : Finset (Torus d n), nbhd m X ⊆ (B : Set (Torus d n)) ∧
      (B : Set (Torus d n)) ⊆ nbhd (m + (s - 1)) X ∧
      (∀ q ∈ B, ∃ x, q ∈ lbox x s ∧ lbox x s ⊆ (B : Set (Torus d n))) ∧
      ((∀ u ∈ nbhd m X, ∀ v ∈ nbhd m X, Relation.ReflTransGen
        (fun a b => a ∈ nbhd m X ∧ b ∈ nbhd m X ∧ NNAdj a b) u v) →
        ∀ u ∈ B, ∀ v ∈ B, Relation.ReflTransGen
          (fun a b => a ∈ (B : Set (Torus d n)) ∧ b ∈ (B : Set (Torus d n)) ∧ NNAdj a b) u v) := by
  classical
  set T : Set (Torus d n) := {q | ∃ x ∈ nbhd m X, q ∈ lbox x s} with hT
  refine ⟨(Set.toFinite T).toFinset, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.Finite.coe_toFinset]
    exact ⟨x, hx, mem_box_self x hs⟩
  · intro q hq
    simp only [Set.Finite.coe_toFinset] at hq
    obtain ⟨x, hx, hqx⟩ := hq
    obtain ⟨y, hy, hxy⟩ := mem_nbhd.1 hx
    refine mem_nbhd.2 ⟨y, hy, ?_⟩
    have h1 := supDist_le_of_mem_lbox hqx
    have h2 := supDist_triangle x q y
    have h3 := supDist_comm x q
    have h4 := supDist_comm x y
    have h5 := supDist_triangle q x y
    omega
  · intro q hq
    simp only [Set.Finite.mem_toFinset] at hq
    obtain ⟨x, hx, hqx⟩ := hq
    refine ⟨x, hqx, fun q' hq' => ?_⟩
    simp only [Set.Finite.coe_toFinset]
    exact ⟨x, hx, hq'⟩
  · intro hconn u hu v hv
    simp only [Set.Finite.mem_toFinset] at hu hv
    obtain ⟨x, hx, hux⟩ := hu
    obtain ⟨y, hy, hvy⟩ := hv
    have hsub : ∀ z ∈ nbhd m X, ∀ q ∈ lbox z s, q ∈ T := fun z hz q hq => ⟨z, hz, hq⟩
    have hsymm : ∀ a b : Torus d n, (a ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧
        b ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧ NNAdj a b) →
        (b ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧
        a ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧ NNAdj b a) :=
      fun _ _ h => ⟨h.2.1, h.1, nnAdj_symm h.2.2⟩
    have hbox : ∀ z ∈ nbhd m X, ∀ q ∈ lbox z s, Relation.ReflTransGen
        (fun a b => a ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧
          b ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧ NNAdj a b) z q := by
      intro z hz q hq
      refine Relation.ReflTransGen.mono (fun a b hab => ⟨?_, ?_, hab.2.2⟩) _ _ (box_reach_nn z s hq)
      · simp only [Set.Finite.coe_toFinset]; exact ⟨z, hz, hab.1⟩
      · simp only [Set.Finite.coe_toFinset]; exact ⟨z, hz, hab.2.1⟩
    have hhalo : Relation.ReflTransGen
        (fun a b => a ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧
          b ∈ (((Set.toFinite T).toFinset : Finset _) : Set (Torus d n)) ∧ NNAdj a b) x y := by
      refine Relation.ReflTransGen.mono (fun a b hab => ⟨?_, ?_, hab.2.2⟩) _ _ (hconn x hx y hy)
      · simp only [Set.Finite.coe_toFinset]; exact ⟨a, hab.1, mem_box_self a hs⟩
      · simp only [Set.Finite.coe_toFinset]; exact ⟨b, hab.2.1, mem_box_self b hs⟩
    exact (rtg_symm hsymm (hbox x hx u hux)).trans (hhalo.trans (hbox y hy v hvy))

end Cube

section Fibre

variable {d : ℕ}

/-- **Preimage of a union of boxes of cubes is a union of aligned boxes of cells.**  If every cube of
`A` lies in a box of side `s` inside `A`, then every fine site over `A` lies in a box of `s`
cells (side `s * a`, with corner aligned to the grid of side `a`) which is contained in the
preimage of `A`. -/
theorem box_fibre {a n N s : ℕ} [NeZero a] [NeZero n] (hN : N = a * n) (A : Set (Torus d n))
    (hA : ∀ q ∈ A, ∃ x, q ∈ lbox x s ∧ lbox x s ⊆ A) :
    ∀ z ∈ (siteCube a n ⁻¹' A : Set (Torus d N)), ∃ b : Torus d N, Aligned a b ∧
      z ∈ lbox b (s * a) ∧ lbox b (s * a) ⊆ (siteCube a n ⁻¹' A : Set (Torus d N)) := by
  subst hN
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  intro z hz
  obtain ⟨x, hqx, hxA⟩ := hA _ hz
  obtain ⟨u, hu, hzu⟩ := hqx
  refine ⟨fun μ => ((a * (x μ).val : ℕ) : ZMod (a * n)), ?_, ?_, ?_⟩
  · intro μ
    rw [ZMod.val_natCast, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt (ZMod.val_lt (x μ))]
    exact Nat.mul_mod_right _ _
  · refine ⟨fun μ => a * u μ + (z μ).val % a, fun μ => ?_, ?_⟩
    · have := hu μ
      have h2 : (z μ).val % a < a := Nat.mod_lt _ ha
      calc a * u μ + (z μ).val % a < a * u μ + a := by omega
        _ = a * (u μ + 1) := by ring
        _ ≤ a * s := Nat.mul_le_mul_left _ this
        _ = s * a := mul_comm _ _
    · funext μ
      have h1 := congrFun hzu μ
      simp only [siteCube, cubeQ, Pi.add_apply, natT] at h1
      have h3 : (((z μ).val / a : ℕ) : ZMod n) = (((x μ).val + u μ : ℕ) : ZMod n) := by
        rw [h1]; push_cast; rw [ZMod.natCast_zmod_val]
      rw [ZMod.natCast_eq_natCast_iff] at h3
      have h4 := Nat.ModEq.mul_left' a h3
      have h5 : (((a * ((z μ).val / a) : ℕ)) : ZMod (a * n)) =
          ((a * ((x μ).val + u μ) : ℕ) : ZMod (a * n)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).2 h4
      have h6 : z μ = (((a * ((z μ).val / a) + (z μ).val % a : ℕ)) : ZMod (a * n)) := by
        rw [Nat.div_add_mod, ZMod.natCast_zmod_val]
      conv_lhs => rw [h6]
      push_cast at h5 ⊢
      rw [h5]
      simp only [Pi.add_apply, natT]
      push_cast
      ring
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    apply hxA
    refine ⟨fun μ => w μ / a, fun μ => ?_, ?_⟩
    · exact (Nat.div_lt_iff_lt_mul ha).2 (by have := hw μ; linarith [mul_comm s a])
    · funext μ
      simp only [siteCube, cubeQ, Pi.add_apply]
      have e : (((a * (x μ).val : ℕ) : ZMod (a * n)) + (natT w : Torus d (a * n)) μ) =
          (((a * (x μ).val + w μ : ℕ)) : ZMod (a * n)) := by
        simp [natT]
      rw [e, ZMod.val_natCast, Nat.mod_mul_right_div_self, Nat.mul_add_div ha, ZMod.natCast_mod]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp [natT]

end Fibre

end Balaban.LargeField
