/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLocalActivity
public import Balaban.LargeField.Base.BaseChartRotTerm
public import Balaban.LargeField.Base.BasePstRot

/-!
# Rotation invariance of the cluster-expansion coefficient of the masked activities

`maskedTerm_rot`: the masked activity at the rotated datum, source and field is the masked activity;
`masked_Pst_rot`: `P(T)` is invariant under a rotation of the datum (the clause (A4) of the local family),
when the rotation acts on the block variables by a measure-preserving equivalence compatible with the
assembled field.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6 Balaban.Green Balaban.Analysis
  Balaban.Polymer Matrix MeasureTheory

section Rot

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

open Classical in
/-- **Covariance of the masked activity.** -/
theorem maskedTerm_rot (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (g ψ : G.Ω 1 × Fin N → ℂ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hW : ∀ u, W (rotBg R u) *ᵥ rotVec R ψ = rotVec R (W u *ᵥ ψ))
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (hF : ∀ s e, F (s, rotRaw R e) = rotBg R (F (s, e)))
    (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hD : ∀ ψ x, defPt G Dm (rotVec R ψ) x = defPt G Dm ψ x) (ρs rD : ℕ)
    (Rr : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ 1)) (e : RawData d L (N₁ * L ^ m₁) 1 N) :
    maskedTerm G a ν β (rotVec R g) W F Dm m₀ ρs rD Rr Y (rotRaw R e) (rotVec R ψ) =
      maskedTerm G a ν β g W F Dm m₀ ρs rD Rr Y e ψ := by
  unfold maskedTerm
  by_cases hY : Y ⊆ Rr
  · simp only [hY, ↓reduceIte]
    rw [chartTerm_rot G a ν β hR g ψ W hW F hF m₀ ρs Y e, defTerm_rot G Dm hD m₀ rD Y ψ]
  · simp only [hY, ↓reduceIte]

section PstRot

variable {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ → Type*}
  [∀ b, MeasurableSpace (Ωb b)]

open Classical in
/-- **Rotation invariance of the cluster-expansion coefficient of the masked activities** (the clause (A4) of
the local family).  Let `A` be a family of `LabelAct` whose activities at `q ∈ V` are the masked activities; if
`q'` is the rotation of `q` (datum and source), the whitening, the background map and the defect form are
covariant, and the rotation acts on the block variables by a measure-preserving equivalence `e` with
`fld (e Φ) = rotVec R (fld Φ)`, then `P(T)` is the same at `q` and `q'`. -/
theorem masked_Pst_rot (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hW : ∀ ψ u, W (rotBg R u) *ᵥ rotVec R ψ = rotVec R (W u *ᵥ ψ))
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (hF : ∀ s e, F (s, rotRaw R e) = rotBg R (F (s, e)))
    (Dm : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hD : ∀ ψ x, defPt G Dm (rotVec R ψ) x = defPt G Dm ψ x) (ρs rD : ℕ)
    (Rr : Set (Balaban.Localization.CTorus d L N₁ m₁ 1))
    (fld : (∀ b, Ωb b) → G.Ω 1 × Fin N → ℂ)
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (e : (∀ b, Ωb b) ≃ᵐ (∀ b, Ωb b)) (he : MeasurePreserving e (Measure.pi μ) (Measure.pi μ))
    (hfe : ∀ Φ, fld (e Φ) = rotVec R (fld Φ))
    {E : Type*} (V : Set E) (dat : E → RawData d L (N₁ * L ^ m₁) 1 N) (sr : E → G.Ω 1 × Fin N → ℂ)
    (𝒴 : Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1))) (hdom : ∀ Y ∈ 𝒴, IsDj m₀ 1 Y)
    {εH κH κ0 Kc' : ℝ}
    (A : E → LabelAct (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) Ωb εH κH κ0 Kc')
    (hA1 : ∀ q ∈ V, ∀ (y : {Y // Y ∈ 𝒴}) Φ,
      (A q).H y Φ = maskedTerm G a ν β (sr q) W F Dm m₀ ρs rD Rr y.1 (dat q) (fld Φ))
    {q q' : E} (hq : q ∈ V) (hq' : q' ∈ V) (hdq : dat q' = rotRaw R (dat q))
    (hsq : sr q' = rotVec R (sr q))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)) :
    Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) (A q').H T =
      Pst μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) (A q).H T := by
  refine Pst_equiv μ (thickLabels (m₀ := m₀) (j := 1) 𝒴 hdom) (A q).H (A q').H (A q).dep e he
    (fun y Φ => ?_) T
  rw [hA1 q' hq' y (e Φ), hA1 q hq y Φ, hdq, hsq, hfe Φ]
  exact maskedTerm_rot G a ν β hR (sr q) (fld Φ) W (hW (fld Φ)) F hF Dm hD ρs rD Rr y.1 (dat q)

end PstRot

end Rot

end Balaban.LargeField.Base
