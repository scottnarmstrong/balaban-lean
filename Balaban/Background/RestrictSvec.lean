/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Composition

/-!
# The extension of a restricted field and the barred field

Two elementary identities of the extensions of fields on `Ω₁` (cores of the landed
`Localization.svec_restrictφ`, `Localization.barField_eq_svec` and of `Fluctuation.RegionPair`):

* `Precedes.svec_restrictφ`: for `G ≺ G'`, the extension of `φ'|_{Ω₁(G)}` agrees with that of `φ'` on
  `Ω₁(G)`;
* `barField_eq_ite_svec`: the barred field `φ̄` is the extension of `φ` on `Ω₁` and the data off `Ω₁`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **The extension of a restricted field agrees with the extension of the field on `Ω₁`.** -/
theorem Precedes.svec_restrictφ (h : Precedes G G') (φ' : G'.Ω 1 × Fin N → ℂ)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (i : Fin N) :
    svec G (h.restrictφ φ') y i = svec G' φ' y i := by
  rw [svec_of_mem G (h.restrictφ φ') ⟨y, hy⟩ i, svec_of_mem G' φ' ⟨y, h.mem_Ω1 hy⟩ i]
  rfl

/-- **The barred field** is the extension `svec` of `φ` on `Ω₁` and the data off `Ω₁`. -/
theorem barField_eq_ite_svec (G : GeneratingSet d L N₀ k ϱ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    barField G Ψ φ x i = if x ∈ G.Ω 1 then svec G φ x i else Ψ x i := by
  classical
  unfold barField
  by_cases h : x ∈ G.Ω 1
  · rw [dite_eq_left h, ite_eq_left h, svec_of_mem G φ ⟨x, h⟩ i]
  · rw [dite_eq_right h, ite_eq_right h]

end Balaban.Background
