/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasCoreConn

/-!
# Aligned boxes of cells over unions of boxes of cubes (W872, blocker 4): geometry

The preimage of a set `A` of cubes of `𝕋_k` under the cube index of a fine torus is a union of
aligned boxes of `s` cells as soon as every cube of `A` lies in a box of `s` cubes inside `A`:
this is the property `IsPiPrimeUnion` of `Fluctuation/SizeModDefs.lean` for `s = L`
(`box_fibre`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale

local notation "lbox" => Balaban.Localization.box

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
