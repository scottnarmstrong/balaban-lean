/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseMarkedFootprint

/-!
# The good region of a base record and the retained sites

For a base record `(P₁, Q₁, R₁, S₁)` the good region `Ω₁ ⊆ 𝕋₁` is a union of cubes, so the set of
fine sites whose cube lies in `Ω₁` is a union of complete cubes. The `3`-neighbourhood of `P₁`
lies in the complement of `Ω₁`, and every failed factor of a cube of `P₁` reads only fine sites
whose cube lies in the complement of `Ω₁` (the retained sites).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background

variable {d N : ℕ} {nn : ℕ → ℕ} {L M K : ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- The good region of a base record: the set of fine sites whose cube lies in `Ω₁` is a union of
complete cubes; `P₁^{∼3} ⊆ Ω₁ᶜ`; every cube of `P₁` has its whole test footprint in the retained
sites (cubes outside `Ω₁`); and the failed factor `χ'^{(0)}(c)` of a cube of `P₁` does not change
when the spins on the sites of `Ω₁` are changed. -/
theorem baseRecord_good_region (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K)
    (regimeB : Prop) (ν δ₀ : ℝ) (h : Fin N → ℝ) {Rk : ℝ} [NeZero (nn 1)]
    (br : BaseRecord d L (nn 1) Rk) :
    (∀ x y : Torus d (M * nn K * L ^ K), cubeMap nn L M K 1 x = cubeMap nn L M K 1 y →
        (cubeMap nn L M K 1 x ∈ br.Omega ↔ cubeMap nn L M K 1 y ∈ br.Omega)) ∧
      nbhd 3 br.P ⊆ br.Omegaᶜ ∧
      (∀ c ∈ br.P, ∀ x ∈ baseFootprint nn L M K regimeB c,
        cubeMap nn L M K 1 x ∉ br.Omega) ∧
      (∀ c ∈ br.P, ∀ (φ φ' : Torus d (M * nn K * L ^ K) → Fin N → ℝ)
        (θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ),
        (∀ x, cubeMap nn L M K 1 x ∉ br.Omega → φ x = φ' x) →
          chiPrimeZero nn L M K regimeB ν δ₀ h c (φ, θ) =
            chiPrimeZero nn L M K regimeB ν δ₀ h c (φ', θ)) := by
  have hfoot : ∀ c ∈ br.P, ∀ x ∈ baseFootprint nn L M K regimeB c,
      cubeMap nn L M K 1 x ∉ br.Omega := by
    intro c hc x hx hxo
    exact Set.disjoint_left.mp
      (baseFootprint_disjoint_of_mem_P hnn hK regimeB br hc
        (Dplus := {x | cubeMap nn L M K 1 x ∈ br.Omega}) (fun x hx => hx)) hx hxo
  refine ⟨fun x y hxy => by rw [hxy], br.nbhd_P_subset_compl_Omega, hfoot, ?_⟩
  intro c hc φ φ' θ hφ
  exact chiPrimeZero_congr_footprint regimeB ν δ₀ h c φ φ' θ
    fun x hx => hφ x (hfoot c hc x hx)

end Balaban.LargeField
