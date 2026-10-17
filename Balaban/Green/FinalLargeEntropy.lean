/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailGas

/-!
# Entropy input for the singleton last-integral gas
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban.Polymer

namespace Balaban.Green

/-- Connected charged supports with bounded multiplicity satisfy the gas entropy condition. -/
theorem final_large_entropy_of_connected
    {d m : ℕ} [NeZero m] (hd : 1 ≤ d) {Yt : Type*} [Fintype Yt]
    (cy : Yt → Finset (Torus d m))
    (hne : ∀ y, (cy y).Nonempty)
    (hconn : ∀ y, ((blockGraph d m).induce (cy y : Set (Torus d m))).Connected)
    {mY κ : ℝ}
    (hfib : ∀ T, ((Finset.univ.filter fun y => cy y = T).card : ℝ) ≤ mY)
    (hmY : 1 ≤ mY)
    (hκ : Real.log (mY * (((2 * d : ℕ) : ℝ)) ^ 2) + 3 ≤ κ)
    (b : Torus d m) :
    ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
      Real.exp (-κ * ((cy y).card : ℝ)) ≤ 1 := by
  have h := coupling_entropy_le_one (κ := κ) (blockGraph d m) (Δ := 2 * d)
    (blockGraph_degree_le d m) (by omega) hne hconn (fun T => by
      refine le_of_eq_of_le ?_ (hfib T)
      congr 2
      ext y
      simp) hmY hκ b
  exact le_of_eq_of_le (Finset.sum_congr (by ext; simp) (fun _ _ => rfl)) h

end Balaban.Green
