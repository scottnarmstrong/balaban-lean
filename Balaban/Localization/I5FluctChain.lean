/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctSol
public import Balaban.Localization.DomainLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chain of the analyticity spaces with the fluctuation (LOCALIZATION.md §4.3, P3 (4.41))

The datum of `𝔹_k(X)` in the composite `F(s)` of P3 (4.41) is
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) + δψ(𝔹_k(X), 𝔹_k; ψ', s)`, where `δψ` is the composed fluctuation field
`composeField Gk Hm a δφ 0`.  It is a layer-constant perturbation of the datum of the background
part (`flDatum`), of size at most `δ_fl = N · 5 · K₂' δ₁` on the data sites (`flPsi_bound`), so it
stays in `Ξ^c_K(𝔹_k(X); 1, ε₃)`, `ε₃ = ε₂ + K₂' δ_fl` (`xiCData_perturb`), by (Ξ2).

* `FlNum`: the smallness conditions for the radius `ε₃`;
* `flDatum`: the perturbed datum;
* `i5f_stage1`: the datum lies in `Ξ^c_K(𝔹_k(X); 1, ε₃)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

section Perturb

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- (Ξ2) for realizations: `Ξ^c_K(𝔹; 1, ε')` is stable under layer-constant perturbations. -/
theorem xiCData_perturb (H : BgHyp d L K ϱ a ν) {ε' δ₃ : ℝ} (hδ₃ : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε') ≤ 1)
    (hδ₂ : xiC1 d * ε' + 5 * δ₃ ≤ bgC1 d L N)
    (hstar : δ₃ ≤ deltaStar d L N) (hK1s : bgK1 d L N * (xiC1 d * ε') ≤ deltaStar d L N)
    (hsm : bgK1 d L N * (xiC1 d * ε') + cK2 d L N * δ₃ < bgC0 d L N)
    {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hδΨc : IsLayerConstant G δΨ)
    (hδΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₃) {D : BgData G N}
    (hX : XiCData G a ν K 1 ε' D) :
    XiCData G a ν K 1 (ε' + xiK2 d L N * δ₃) (perturbData G D δΨ hδΨc) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hX
  refine ⟨Ψ₀, h₀, fun x i => Ψ'' x i + δΨ x i, h'',
    xiC_perturb H hδ₃ hδ₃1 hsmall hδ₂ hstar hK1s hsm hδΨc hδΨ hX, ⟨fun x hx i => ?_, fun x hx i => ?_⟩⟩
  · rw [perturbData_Ψ hx, hR.1 x hx i]; ring
  · exact hR.2 x hx i

end Perturb

section Stage

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The composed fluctuation** `δψ(𝔹_k(X), 𝔹_k; ψ', s)`, layer-constant on `𝔹_k(X)`. -/
theorem flPsi_layerConst (hPm : Precedes Gk Hm) (a : ℕ → ℝ) (δφ : Hm.Ω 1 × Fin N → ℂ) :
    IsLayerConstant Gk (fun x i => composeField Gk Hm a δφ (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) x i) :=
  composeField_layerConst hPm a δφ (isLayerConstant_zero Hm)

/-- **The size of the composed fluctuation**: `|δψ| ≤ N · 5 V` if `|δφ| ≤ V`. -/
theorem flPsi_bound (hPm : Precedes Gk Hm) {a : ℕ → ℝ} (ha : IsAdmissibleWeights K a)
    {δφ : Hm.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V)
    (hδ : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), ‖svec Hm δφ y i‖ ≤ V)
    (x : CTorus d L N₁ m₁ K) :
    vn (fun i => composeField Gk Hm a δφ (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) x i) ≤
      N * (5 * V) := by
  classical
  have hsup : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), ‖svec Hm δφ y i‖ ≤
      V * decay 0 (siteSetDist Hm Finset.univ y) := by
    intro y i
    by_cases hy : y ∈ Hm.Ω 1
    · have : decay 0 (siteSetDist Hm Finset.univ y) = 1 := by
        rw [setDist_of_mem (W := Finset.univ) (Finset.mem_univ y) hy]
        simp [decay]
      rw [this, mul_one]; exact hδ y i
    · rw [svec_of_not_mem Hm δφ hy i, norm_zero]
      exact mul_nonneg hV (decay_nonneg _ _)
  refine vn_le_card_mul (by positivity) fun i => ?_
  have h := composeField_close hPm ha le_rfl hV hsup x i
  have hd1 := decay_le_one (le_refl (0 : ℝ)) (siteSetDist Hm Finset.univ x)
  refine h.trans ?_
  simp only [zero_mul, Real.exp_zero, mul_one]
  nlinarith [mul_nonneg hV (decay_nonneg 0 (siteSetDist Hm Finset.univ x))]

variable (Gk) in
/-- **The datum of `𝔹_k(X)` with the fluctuation**: `composeData` perturbed by `δψ`. -/
noncomputable def flDatum (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N) : BgData Gk N :=
  perturbData Gk (composeData hP a φ D)
    (fun x i => composeField Gk Hm a δφ (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) x i)
    (flPsi_layerConst hPm a δφ)

theorem flDatum_Ψ (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N)
    (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    (flDatum Gk hP hPm a φ δφ D).Ψ x i = composeField Gk Gp a φ D.Ψ x i +
      composeField Gk Hm a δφ (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) x i := by
  classical
  by_cases hx : x ∈ dataSites Gk
  · rw [flDatum, perturbData_Ψ hx]; rfl
  · simp [flDatum, perturbData, composeData, hx, composeField_of_not_mem _ _ _ hx]

theorem flDatum_h (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm) (a : ℕ → ℝ)
    (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N) :
    (flDatum Gk hP hPm a φ δφ D).h = (composeData hP a φ D).h := rfl

end Stage

end Balaban.Localization
