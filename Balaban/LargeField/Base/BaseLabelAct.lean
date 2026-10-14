/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseConstrainedCov
public import Balaban.LargeField.Base.BaseMarked
public import Balaban.Fluctuation.HatLabelsAct

/-!
# The first step's localized activity in the `LabelAct` form (BASEPLAN leaf G3)

* `baseActivity_LabelAct`: localized terms `T_Y(e; Φ)` on the labels `Y ∈ 𝒴`, analytic in a
  parameter `e` on a set `V`, measurable in the block variables, depending only on the blocks of
  `Y`, bounded by `ε_H e^{-κ_H 𝗱(Y)}`, form a family `e ↦ A e` of `LabelAct` with the entropy bound
  `K₀(d, L, κ₀)` and `H = T` on `V`.
* `baseActivity_LabelAct_parametrix`: the same with the parameters the data `(s, φ₀, α)` of the
  parametrix on its full domain `DecDom G N κ δ`, and each term an analytic function of the
  entries of the constrained covariance of `baseConstrainedCov_analytic`.
* `baseActivity_markSum_bound`: the mark sum of `sum_gst_marks_bound` for this family.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Polymer Balaban.Fluctuation
  MeasureTheory

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

open Classical in
/-- **The localized activity family.**  For terms `T Y e Φ` that are analytic in the parameter `e`
on `V`, measurable in the block variables, depend on `Φ` only through the blocks of `Y`, and are
bounded by `ε_H e^{-κ_H 𝗱(Y)}`, there is a family of `LabelAct` on the labels `𝒴` (entropy bound
`K_c ≥ K₀(d, L, κ₀)`) whose activity at `e ∈ V` is `T`. -/
theorem baseActivity_LabelAct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {V : Set E} (hV : IsOpen V)
    {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (𝒴 : Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ K)))
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ j Y)
    (T : Set (Balaban.Localization.CTorus d L N₁ m₁ K) → E → (∀ b, Ωb b) → ℂ) {εH κH κ0 Kc : ℝ} (hε : 0 ≤ εH)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
    (hmeas : ∀ Y ∈ 𝒴, ∀ e ∈ V, Measurable (T Y e))
    (hdep : ∀ Y ∈ 𝒴, ∀ e ∈ V, DepOn (blocksOf m₀ j Set.univ Y) (T Y e))
    (hbd : ∀ Y ∈ 𝒴, ∀ e ∈ V, ∀ Φ, ‖T Y e Φ‖ ≤ εH * Real.exp (-κH * treeLenCovOne m₀ j Y))
    (han : ∀ Y ∈ 𝒴, ∀ Φ, AnalyticOnNhd ℂ (fun e => T Y e Φ) V) :
    ∃ A : E → LabelAct (thickLabels (m₀ := m₀) (j := j) 𝒴 hdom) Ωb εH κH κ0 Kc,
      (∀ e ∈ V, ∀ (y : {Y // Y ∈ 𝒴}) Φ, (A e).H y Φ = T y.1 e Φ) ∧
      (∀ (y : {Y // Y ∈ 𝒴}) Φ, AnalyticOnNhd ℂ (fun e => (A e).H y Φ) V) := by
  let Hf : E → {Y // Y ∈ 𝒴} → (∀ b, Ωb b) → ℂ := fun e Y Φ => if e ∈ V then T Y.1 e Φ else 0
  refine ⟨fun e => ⟨Hf e, fun Y => ?_, fun Y => ?_, fun Y Φ => ?_, fun b => ?_⟩, ?_, ?_⟩
  · by_cases he : e ∈ V
    · simpa [Hf, he] using hmeas Y.1 Y.2 e he
    · simp [Hf, he]
  · by_cases he : e ∈ V
    · simpa [Hf, he, thickLabels] using hdep Y.1 Y.2 e he
    · intro Φ Φ' _
      simp [Hf, he]
  · by_cases he : e ∈ V
    · simpa [Hf, he, thickLabels] using hbd Y.1 Y.2 e he Φ
    · simp only [Hf, he, ite_false, norm_zero]
      exact mul_nonneg hε (Real.exp_pos _).le
  · exact (entropy_thick hN hj 𝒴 hdom hκ0 b).trans hKc
  · intro e he Y Φ
    simp [Hf, he]
  · intro Y Φ e he
    refine ((han Y.1 Y.2 Φ) e he).congr ?_
    filter_upwards [hV.mem_nhds he] with e' he'
    simp [Hf, he']

end Generic

section Parametrix

variable {d L : ℕ} [NeZero L]

/-- **The first step's activity family in the parameters of the parametrix.**  The parameters are
the data `(s, φ₀, α)` on the full domain `DecDom G N κ δ` of `baseConstrainedCov_analytic` (one
`s_P` per cover cube, `|s_P| < e^κ`).  Terms that are analytic functions `Ψ_Y(Φ, ·)` of the
entries of the constrained covariance `Cov`, measurable in `Φ`, depending on the blocks of `Y`
only and bounded by `ε_H e^{-κ_H 𝗱(Y)}`, form a family of `LabelAct` with the entropy bound
`K₀(d, L, κ₀)`, analytic in `(s, φ₀, α)` on `DecDom G N κ δ`. -/
theorem baseActivity_LabelAct_parametrix (hd : 3 ≤ d) (hL : 3 ≤ L) (N : ℕ) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {κ : ℝ}, 0 ≤ κ → ∃ δs : ℝ, 0 < δs ∧
      ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ δs →
      ∀ (Cov : DecData G N → (G.Ω 1 × Fin N) → (G.Ω 1 × Fin N) → ℂ),
      (∀ p ∈ DecDom G N κ δ, ∀ x y, Cov p x y =
        (basePart (restrictField G p.2.1) +
            liftOp N (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1)) -
            liftOp N (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1)) *
              fieldMul (restrictField G p.2.1) *
              (constraintM (dirichletOperator G a ν p.2.2)
                (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1))
                (restrictField G p.2.1))⁻¹ *
              constraintN (dirichletOperator G a ν p.2.2)
                (Dec2.Gs (coverOf G) G a ν p.2.2 (Dec2.extS (coverOf G) p.1))
                (restrictField G p.2.1)) x y) →
      ∀ {m₀ j : ℕ} [NeZero N₁] {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ j Set.univ → Type*}
      [∀ b, MeasurableSpace (Ωb b)],
      L ^ m₀ ∣ N₁ → j ≤ 1 →
      ∀ (𝒴 : Finset (Set (Balaban.Localization.CTorus d L N₁ m₁ 1)))
        (hdom : ∀ Y ∈ 𝒴, IsDj m₀ j Y)
        (Ψ : Set (Balaban.Localization.CTorus d L N₁ m₁ 1) → (∀ b, Ωb b) →
          ((G.Ω 1 × Fin N) → (G.Ω 1 × Fin N) → ℂ) → ℂ) {εH κH κ0 Kc : ℝ}, 0 ≤ εH →
      aEnt d L + 1 ≤ κ0 → K0 d L κ0 ≤ Kc →
      (∀ Y ∈ 𝒴, ∀ p ∈ DecDom G N κ δ, Measurable (fun Φ => Ψ Y Φ (Cov p))) →
      (∀ Y ∈ 𝒴, ∀ p ∈ DecDom G N κ δ, DepOn (blocksOf m₀ j Set.univ Y) (fun Φ => Ψ Y Φ (Cov p))) →
      (∀ Y ∈ 𝒴, ∀ p ∈ DecDom G N κ δ, ∀ Φ,
        ‖Ψ Y Φ (Cov p)‖ ≤ εH * Real.exp (-κH * treeLenCovOne m₀ j Y)) →
      (∀ Y ∈ 𝒴, ∀ Φ, AnalyticOnNhd ℂ (Ψ Y Φ) (Cov '' DecDom G N κ δ)) →
      ∃ A : DecData G N → LabelAct (thickLabels (m₀ := m₀) (j := j) 𝒴 hdom) Ωb εH κH κ0 Kc,
        (∀ p ∈ DecDom G N κ δ, ∀ (y : {Y // Y ∈ 𝒴}) Φ, (A p).H y Φ = Ψ y.1 Φ (Cov p)) ∧
        (∀ (y : {Y // Y ∈ 𝒴}) Φ, AnalyticOnNhd ℂ (fun p => (A p).H y Φ) (DecDom G N κ δ)) := by
  obtain ⟨cstar, hc, H⟩ := baseConstrainedCov_analytic (d := d) (L := L) hd hL N
  refine ⟨cstar, hc, fun {κ} hκ => ?_⟩
  obtain ⟨δs, hδs, H2⟩ := H hκ
  refine ⟨δs, hδs, ?_⟩
  intro N₁ m₁ _ ϱ G a ν S hM δ hδ hδδs Cov hCov m₀ j _ Ωb _ hN hj 𝒴 hdom Ψ εH κH κ0 Kc hε hκ0 hKc
    hmeas hdep hbd hΨ
  have hCan : AnalyticOnNhd ℂ Cov (DecDom G N κ δ) := by
    refine AnalyticOnNhd.pi fun x => AnalyticOnNhd.pi fun y => ?_
    refine (H2 G S hM hδ hδδs x y).congr (isOpen_decDom κ δ) fun p hp => ?_
    exact (hCov p hp x y).symm
  exact baseActivity_LabelAct (K := 1) (isOpen_decDom κ δ) hN hj 𝒴 hdom
    (fun Y p Φ => Ψ Y Φ (Cov p)) hε hκ0 hKc hmeas hdep hbd
    (fun Y hY Φ => (hΨ Y hY Φ).comp hCan (Set.mapsTo_image _ _))

end Parametrix

end Balaban.LargeField.Base
