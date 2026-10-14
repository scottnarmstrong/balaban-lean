/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRecordGoodRegion

/-!
# Transfer of the old cutoff factors (BASE-KERNEL-4 Lemma 2.2)

Let `D₊` be a set of integrated fine sites in cubes of `Ω₁`, and let the strict margins (2.4) of
BASE-KERNEL-4 hold for the background `e` on the footprints of the cubes of `𝒥₊`. Then every
factor `A_c B_c` with `c ∈ 𝒥₊` equals one, the old factor `∏_{c∈P₁}(1 - A_c B_c) ∏_{c∉P₁} A_c B_c`
equals the same product with the cubes of `𝒥₊` deleted, and the deleted product does not change
when the spins on `D₊` are changed.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background

variable {d N : ℕ} {nn : ℕ → ℕ} {L M K : ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- **BASE-KERNEL-4 Lemma 2.2.** Under the margins (2.4) on the footprints of `𝒥₊`, the factors
of `𝒥₊` are all one, the old base factor is the deleted factor, and the deleted factor is
independent of the spins on the integrated sites `D₊ ⊆ Ω₁`. -/
theorem baseCutoffTransfer (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K)
    {regimeB : Prop} {ν δ₀ r : ℝ} (hν : 0 ≤ ν) {h : Fin N → ℝ} {Rk : ℝ}
    (br : BaseRecord d L (nn 1) Rk) (P : Finset (Torus d (nn 1)))
    (hP : (P : Set (Torus d (nn 1))) = br.P)
    {Dplus : Set (Torus d (M * nn K * L ^ K))}
    (hD : ∀ x ∈ Dplus, cubeMap nn L M K 1 x ∈ br.Omega)
    {φ e : Torus d (M * nn K * L ^ K) → Fin N → ℝ}
    {θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ}
    (hm : BaseCutoffMargins nn L M K regimeB ν δ₀ r h (P : Set _) Dplus φ e θ) :
    (∀ c ∈ baseJPlus nn L M K regimeB (P : Set _) Dplus,
        chiPrimeZero nn L M K regimeB ν δ₀ h c (φ, θ) = 1) ∧
      baseOldFactor regimeB ν δ₀ h P (φ, θ) = baseDeletedFactor regimeB ν δ₀ h P Dplus (φ, θ) ∧
      ∀ φ' : Torus d (M * nn K * L ^ K) → Fin N → ℝ, (∀ x ∉ Dplus, φ x = φ' x) →
        baseOldFactor regimeB ν δ₀ h P (φ, θ) =
          baseDeletedFactor regimeB ν δ₀ h P Dplus (φ', θ) := by
  refine ⟨fun c hc => chiPrimeZero_eq_one_of_margins hK hν hm hc,
    baseOldFactor_eq_deleted hK hν P hm, fun φ' hφ => ?_⟩
  rw [baseOldFactor_eq_deleted hK hν P hm]
  exact baseDeleted_indep hnn hK ν δ₀ h br P hP hD φ φ' θ hφ

end Balaban.LargeField
