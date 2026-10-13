/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRowCoeff

/-!
# The kernel `obsHker` is supported on polymer labels

The label of a domain `Y ∈ 𝒟_K` has the sites `Y`, and `Y` has finite whole-lattice size.  So
`dOmega (sitesOf (obsRowLabel Y)) ≠ ⊤`, and the kernel `obsHker 𝒴 c m₀ T` can be nonzero only at
such `T`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The label of a domain has finite whole-lattice size.** -/
theorem dOmega_sitesOf_obsRowLabel_ne_top (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) :
    dOmega m₀ K Set.univ (sitesOf (obsRowLabel m₀ K Y)) ≠ ⊤ := by
  have hle : dOmega m₀ K Set.univ (sitesOf (obsRowLabel m₀ K Y)) ≤
      ENNReal.ofReal (treeLenCovOne m₀ K Y) := by
    rw [sitesOf_obsRowLabel hN hY]
    simpa using G4_dOmega_le (Ω := Set.univ) hY (by simpa using hY.1)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- **Support of the kernel.**  If every domain of `𝒴` is in `𝒟_K`, then a nonzero value of
`obsHker 𝒴 c m₀` sits at a set of cubes of finite whole-lattice size. -/
theorem dOmega_ne_top_of_obsHker_ne_zero {𝒴 : Finset (Set (CTorus d L N₁ m₁ K))}
    {c : Set (CTorus d L N₁ m₁ K) → ℂ} (hN : L ^ m₀ ∣ N₁) (hdj : ∀ Y ∈ 𝒴, IsDj m₀ K Y) {T}
    (h : obsHker 𝒴 c m₀ T ≠ 0) : dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤ := by
  obtain ⟨Y, hY, rfl, -⟩ := exists_of_obsHker_ne_zero h
  exact dOmega_sitesOf_obsRowLabel_ne_top hN (hdj Y hY)

end Balaban.Fluctuation
