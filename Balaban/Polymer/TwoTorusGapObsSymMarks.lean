/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsSymLabels

/-!
# Translation covariance of the marks of the observable

The unit vectors of the marks `(u, a)` and `(unitAct u, a)`, the coefficients of the terms along them
and the remainder marks correspond under a lattice symmetry acting on the unit points by `unitAct`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} (SS : LatSymm S.G' S.G' σ) (hU : UnitBlockPres σ)

/-- The unit vectors of corresponding marks correspond. -/
theorem obsUnitVec_sym (m : ObsMarkIdx S) (p : S.U × Fin N) :
    obsUnitVec S (unitAct S.G' SS hU m.1, m.2) (unitAct S.G' SS hU p.1, p.2) =
      obsUnitVec S m p := by
  unfold obsUnitVec
  by_cases h : p = m
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    rw [Prod.mk.injEq] at h'
    exact h (Prod.ext ((unitAct S.G' SS hU).injective h'.1) h'.2)

/-- The coefficients along the unit vectors of corresponding marks agree, for terms that agree at
corresponding hat variables. -/
theorem hatCoeff_obsUnitVec_sym {Rw Rw' : Type*} {E : Rw × (S.U × Fin N → ℂ) → ℂ}
    {E' : Rw' × (S.U × Fin N → ℂ) → ℂ} {r : Rw} {r' : Rw'} {cψ : ℝ} (hcψ : 0 < cψ)
    (hE : ∀ (ψh ψh' : S.U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) → (∀ q, ‖ψh' q‖ ≤ cψ) →
      (∀ u i, ψh' (unitAct S.G' SS hU u, i) = ψh (u, i)) → E' (r', ψh') = E (r, ψh))
    (m : ObsMarkIdx S) :
    hatCoeff E' r' (obsUnitVec S (unitAct S.G' SS hU m.1, m.2)) = hatCoeff E r (obsUnitVec S m) := by
  refine hatCoeff_congr_of_eqOn hcψ fun ζ hζ => hE _ _ (smul_mem_ball (norm_obsUnitVec_le _ _) hζ)
    (smul_mem_ball (norm_obsUnitVec_le _ _) hζ) fun u i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [obsUnitVec_sym S SS hU m (u, i)]

variable (hp : 0 < S.p₁)

/-- **The remainder marks under a lattice symmetry.**  For terms agreeing at corresponding hat
variables and block variables corresponding under `unitAct`, the remainder marks of corresponding
domains agree. -/
theorem obsGrRawC_sym {Ev Ev' : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ}
    {𝒴 𝒴' : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (Y : {Y // Y ∈ 𝒴}) (Y' : {Y' // Y' ∈ 𝒴'})
    {r r' : RawData d L (N₁ * L ^ m₁) (k + 1) N} {cψ : ℝ} (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hE : ∀ (ψh ψh' : S.U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) → (∀ q, ‖ψh' q‖ ≤ cψ) →
      (∀ u i, ψh' (unitAct S.G' SS hU u, i) = ψh (u, i)) → Ev' Y'.1 (r', ψh') = Ev Y.1 (r, ψh))
    {Φ Φ' : ∀ c, (S.blockSplit m₀ hp).Ωb c}
    (hΦ : ∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) (u : ℂ) :
    obsGrRawC S m₀ hp Ev' 𝒴' r' (some Y') u Φ' = obsGrRawC S m₀ hp Ev 𝒴 r (some Y) u Φ := by
  have h4 : 4 ≤ cψ / S.p₁ := four_le_of hcψ hp hq
  show remExt (fun ζ : ℂ => Ev' Y'.1 (r', ζ • S.hatOf m₀ S.p₁ hp Φ')) u =
    remExt (fun ζ : ℂ => Ev Y.1 (r, ζ • S.hatOf m₀ S.p₁ hp Φ)) u
  refine remExt_congr_of_eqOn (ρ := cψ / S.p₁) (by linarith) (fun ζ hζ => ?_) u
  refine hE _ _ (smul_mem_ball_p hp (norm_hatOf_p₁_le Φ) hζ)
    (smul_mem_ball_p hp (norm_hatOf_p₁_le Φ') hζ) fun v i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hatOf_sym S m₀ hp SS hU _ hΦ v i]

end Marks

end Balaban.Polymer.TwoTorusStep
