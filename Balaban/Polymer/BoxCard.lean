/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PolymerGeometry
import Mathlib.Tactic.Linarith

/-!
# Cardinality of a box

A box `box b s` of side `s` on the torus `Torus d n` has at least `(min s n) ^ d` sites.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Finset

theorem ncard_box_ge {d n : ℕ} [NeZero n] (b : Torus d n) (s : ℕ) :
    (min s n) ^ d ≤ (box b s).ncard := by
  classical
  set t := min s n with ht
  have hts : t ≤ s := min_le_left _ _
  have htn : t ≤ n := min_le_right _ _
  let f : (Fin d → Fin t) → Torus d n := fun w => b + natT (fun μ => (w μ : ℕ))
  have hf : Function.Injective f := by
    intro w w' hww
    have h1 : (natT (fun μ => (w μ : ℕ)) : Torus d n) = natT (fun μ => (w' μ : ℕ)) :=
      add_left_cancel hww
    funext μ
    have h2 := congrFun h1 μ
    simp only [natT_apply] at h2
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [Nat.mod_eq_of_lt ((w μ).2.trans_le htn), Nat.mod_eq_of_lt ((w' μ).2.trans_le htn)] at h2
    exact Fin.ext h2
  have hsub : (↑(Finset.univ.image f) : Set (Torus d n)) ⊆ box b s := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨fun μ => (w μ : ℕ), fun μ => (w μ).2.trans_le hts, rfl⟩
  calc t ^ d = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf]; simp
    _ = (↑(Finset.univ.image f) : Set (Torus d n)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (box b s).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

end Balaban.Localization
