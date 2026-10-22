/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoOps
public import Balaban.Polymer.LocalBBoxCorr

/-!
# The local generating sets of corresponding polymers are carried onto each other

`omegaIso_localB`: for a set `X` in the box of radius `ρ₀` of the step torus `N₁` and its image
`X' = bm '' X` on the torus `N₁'`, the local generating sets `𝔹_j(X)` and `𝔹_j(X')` satisfy
`OmegaIso` with the radius `ρ₀ + 6 j L^(j+m₁)` (`localB_omega_boxMap_all`), when the sides have the
room of `OmegaIso` and of `localB_omega_boxMap_all`.  This is the inhabitation of `OmegaIso`.
-/

@[expose] public section

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Polymer Balaban.Polymer.TwoTorusStep

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₁' * L ^ m₁) * L ^ k)

/-- **The local generating sets of corresponding polymers are carried onto each other by the box
map** (inhabitation of `OmegaIso`). -/
theorem omegaIso_localB {j : ℕ} (hj : j ≤ k) (hK : 1 ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    {X' : Set (CTorus d L N₁' m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)}
    {hsep' : ϱ' ≤ minSep L (L ^ m₁)} {ρ0 : ℕ}
    (hX : ∀ x ∈ X, InBox d ρ0 ((N₁ * L ^ m₁) * L ^ k) x) (hXX : X' = bm '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁ * L ^ m₁ * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁' * L ^ m₁ * L ^ k)
    (hroom : 2 * (ρ0 + 6 * j * L ^ (j + m₁)) + 16 * L ^ (k + m₁ + 2) + 16 <
      (N₁ * L ^ m₁) * L ^ k)
    (hroom' : 2 * (ρ0 + 6 * j * L ^ (j + m₁)) + 16 * L ^ (k + m₁ + 2) + 16 <
      (N₁' * L ^ m₁) * L ^ k) :
    OmegaIso (localB j hj X hsep) (localB j hj X' hsep') (ρ0 + 6 * j * L ^ (j + m₁)) := by
  obtain ⟨h1, h2, -⟩ := localB_omega_boxMap_all hj hX hXX
    (fun n hn => by have := hmA n hn; omega) (fun n hn => by have := hmB n hn; omega)
    (hsep := hsep) (hsep' := hsep')
  obtain ⟨-, -, h3⟩ := localB_omega_boxMap_all hj (ρ0 := ρ0 + 1)
    (fun x hx => inBox_mono (Nat.le_succ ρ0) (hX x hx)) hXX hmA hmB (hsep := hsep)
    (hsep' := hsep')
  refine ⟨fun x hx => h1 1 x hx, fun x hx => h2 1 x hx, fun x hx n _ _ => ?_, hroom, hroom', hK⟩
  refine h3 x ?_ n
  have : ρ0 + 1 + 6 * j * L ^ (j + m₁) = ρ0 + 6 * j * L ^ (j + m₁) + 1 := by ring
  rwa [this]

end Balaban.Polymer.LocalIso
