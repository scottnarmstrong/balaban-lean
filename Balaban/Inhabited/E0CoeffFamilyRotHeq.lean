/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubes

/-!
# Activities related by a heterogeneous equality have equal values

Two families of label activities of the same type up to the instance of `Fintype` on the labels
(a subsingleton) and equal numerical constants, related by `HEq`, have the same values `H`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer

theorem labelAct_H_of_heq {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}
    {Ω : Set (CTorus d L N₁ m₁ K)} {Lb : Type} (i1 i2 : Fintype Lb)
    (Lab : CubeLabels m₀ j Ω Lb) (Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type)
    (ms : ∀ b, MeasurableSpace (Ωb b)) {ε κ κ0 Kc ε' κ' κ0' Kc' : ℝ} {E : Type}
    (f : E → ℂ → @LabelAct d L N₁ m₁ K _ _ m₀ j Ω Lb i1 Lab Ωb ms ε κ κ0 Kc)
    (g : E → ℂ → @LabelAct d L N₁ m₁ K _ _ m₀ j Ω Lb i2 Lab Ωb ms ε' κ' κ0' Kc')
    (hε : ε = ε') (hκ : κ = κ') (hκ0 : κ0 = κ0') (hKc : Kc = Kc') (h : HEq f g) :
    ∀ θ u y Φ, @LabelAct.H d L N₁ m₁ K _ _ m₀ j Ω Lb i1 Lab Ωb ms ε κ κ0 Kc (f θ u) y Φ =
      @LabelAct.H d L N₁ m₁ K _ _ m₀ j Ω Lb i2 Lab Ωb ms ε' κ' κ0' Kc' (g θ u) y Φ := by
  subst hε hκ hκ0 hKc
  have hi : i1 = i2 := Subsingleton.elim _ _
  subst hi
  have := eq_of_heq h
  subst this
  intros
  rfl

end Balaban.Fluctuation
