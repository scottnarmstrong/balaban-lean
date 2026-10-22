/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActAlg
public import Balaban.LargeField.Base.BaseXSqrt
public import Balaban.LargeField.Base.BaseXLocal

/-!
# The decoupled chart activities of the first fluctuation integral, definitions (row A3-1 (a3))

For a datum `u = (θ, ψ', g)` (raw block data `θ`, fluctuation `ψ'`, source `g`, all complex) and
decoupling parameters `s`, the decoupled background `(φ(s, θ), α(s, θ)) = F (s, θ)` (a function
supplied by `baseBackground_analytic_whole` / `…localB`), the decoupled square root
`C^{1/2}(s) = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s; φ, α) dx` (`baseSqrtCov`, the integral of `baseCovX_sqrt`),
and the Hessian `H = baseHamiltonian G a ν α 1`, the site exponent is

`baseChartV x s u = chartSite β φ H g (C^{1/2}(s) ψ') x`.

* `baseSqrtCov_one`: at `s ≡ 1` the square root is the principal inverse square root of the first
  step's operator `A_e` (`baseCovX_sqrt_one`);
* `baseChartV_one`: at `s ≡ 1` the site exponent is `chartSite` at the physical objects
  (`sqrtMat (baseOp …)`), which for real data is the real chart exponent (`chartSite_real`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization MeasureTheory Set Matrix

section Defs

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (aT ν : ℝ)

/-- **The decoupled square root** at the extended parameters `s`, the multiplier `α` and the
field `φ₀`: the entries of `π⁻¹ ∫₀^∞ x^{-1/2} ((1 + x)⁻¹ P_e + Ĝ_{0,s}(ν + x) - Π_{0,s}(ν + x)) dx`
of `baseCovX_sqrt`. -/
noncomputable def baseSqrtCovS (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ)
    (α : G.Ω 1 → ℂ) (φ₀ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) :
    Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ := fun y z =>
  ((1 / Real.pi : ℝ) : ℂ) * ∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField G φ₀) +
      liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) α s) -
      Dec2.decPi (coverOf G) G a aT 0 (ν + x) α s φ₀) y z

/-- **The decoupled square root `C^{1/2}(e)`**, `e = (s, φ₀, α) ∈ DecData`. -/
noncomputable def baseSqrtCov (e : DecData G N) : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  baseSqrtCovS G a aT ν (Dec2.extS (coverOf G) e.1) e.2.2 e.2.1

open Classical in
/-- Extension of a field on `Ω₁ × Fin N` to the torus (by `0` outside `Ω₁`). -/
noncomputable def extField (φ : G.Ω 1 × Fin N → ℂ) : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ :=
  fun z i => if h : z ∈ G.Ω 1 then φ (⟨z, h⟩, i) else 0

theorem restrictField_extField (φ : G.Ω 1 × Fin N → ℂ) (z : G.Ω 1) (i : Fin N) :
    restrictField G (extField G φ) z i = φ (z, i) := by
  simp [restrictField, extField, z.2]

/-- The decoupled background datum `(s, φ, α)` of a parameter `s` and raw data `θ`, from a
background map `F`. -/
noncomputable def bgDataOf
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (s : Dec2.DecParams (coverOf G)) (θ : RawData d L (N₁ * L ^ m₁) 1 N) : DecData G N :=
  (s, (extField G (F (s, θ)).1, (F (s, θ)).2))

/-- **The site exponent `V_x` at a decoupled datum `e`**, source `g` and fluctuation `ψ'`. -/
noncomputable def baseChartVAt (β : ℝ) (e : DecData G N) (ψ' g : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) : ℂ :=
  chartSite β (restrictField G e.2.1) (baseHamiltonian G a ν e.2.2 (fun _ => 1)) g
    (baseSqrtCov G a aT ν e *ᵥ ψ') x

/-- **The decoupled chart activity** `V_x(s; θ, ψ', g)` for a background map `F`. -/
noncomputable def baseChartV
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (β : ℝ) (x : G.Ω 1) (s : Dec2.DecParams (coverOf G))
    (u : RawData d L (N₁ * L ^ m₁) 1 N × (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 × Fin N → ℂ)) : ℂ :=
  baseChartVAt G a aT ν β (bgDataOf G F s u.1) u.2.1 u.2.2 x

theorem dec2_extS_one : Dec2.extS (coverOf G) (fun _ => (1 : ℂ)) = fun _ => 1 := by
  funext P; unfold Dec2.extS; split_ifs <;> rfl

end Defs

section One

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {ν Cx : ℝ}

/-- **At the physical point `s ≡ 1` the decoupled square root is `sqrtMat A_e`.** -/
theorem baseSqrtCov_one {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} [Nonempty (G.Ω 1 × Fin N)]
    {a : ℕ → ℝ} {aT : ℝ} (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    {α : G.Ω 1 → ℂ} (hα : AdmPot G α) (hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1) :
    baseSqrtCov G a aT ν ((fun _ => 1, (φ, α)) : DecData G N) =
      Localization.sqrtMat (baseOp N (restrictField G φ)
        (baseHamiltonian G a ν α (fun _ => 1))) := by
  funext y z
  have h := (baseCovX_sqrt_one S hCx ha0 ha1 ha1' haT hα hM hδ hsm hφ hsq).2.1 y z
  show baseSqrtCovS G a aT ν (Dec2.extS (coverOf G) (fun _ => 1)) α φ y z = _
  rw [dec2_extS_one]
  exact h

/-- **The site exponent at `s ≡ 1`** is `chartSite` at the physical square root. -/
theorem baseChartVAt_one {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} [Nonempty (G.Ω 1 × Fin N)]
    {a : ℕ → ℝ} {aT : ℝ} (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    {α : G.Ω 1 → ℂ} (hα : AdmPot G α) (hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1) (β : ℝ) (ψ' g : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    baseChartVAt G a aT ν β ((fun _ => 1, (φ, α)) : DecData G N) ψ' g x =
      chartSite β (restrictField G φ) (baseHamiltonian G a ν α (fun _ => 1)) g
        (Localization.sqrtMat (baseOp N (restrictField G φ)
          (baseHamiltonian G a ν α (fun _ => 1))) *ᵥ ψ') x := by
  unfold baseChartVAt
  rw [baseSqrtCov_one S hCx ha0 ha1 ha1' haT hα hM hδ hsm hφ hsq]

/-- **`baseChartV_one`**: for the decoupled datum of `s ≡ 1` (the physical background `(φ, α) =
F (1, θ)` of the datum `θ`, extended by `0` off `Ω₁`), `baseChartV` is `chartSite` at the physical
square root. -/
theorem baseChartV_one {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} [Nonempty (G.Ω 1 × Fin N)]
    {a : ℕ → ℝ} {aT : ℝ} (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    (hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (F : Dec2.DecParams (coverOf G) × RawData d L (N₁ * L ^ m₁) 1 N →
      (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (θ : RawData d L (N₁ * L ^ m₁) 1 N) (hα : AdmPot G (F (fun _ => 1, θ)).2)
    (hφ : IsConstraintField G δ (extField G (F (fun _ => 1, θ)).1))
    (hsq : ∀ z : G.Ω 1, ∑ i, (F (fun _ => 1, θ)).1 (z, i) * (F (fun _ => 1, θ)).1 (z, i) = 1)
    (β : ℝ) (x : G.Ω 1) (ψ' g : G.Ω 1 × Fin N → ℂ) :
    baseChartV G a aT ν F β x (fun _ => 1) (θ, ψ', g) =
      chartSite β (fun z i => (F (fun _ => 1, θ)).1 (z, i))
        (baseHamiltonian G a ν (F (fun _ => 1, θ)).2 (fun _ => 1)) g
        (Localization.sqrtMat (baseOp N (fun z i => (F (fun _ => 1, θ)).1 (z, i))
          (baseHamiltonian G a ν (F (fun _ => 1, θ)).2 (fun _ => 1))) *ᵥ ψ') x := by
  have hres : restrictField G (extField G (F (fun _ => 1, θ)).1) =
      fun z i => (F (fun _ => 1, θ)).1 (z, i) := by
    funext z i; exact restrictField_extField G _ z i
  unfold baseChartV bgDataOf
  have := baseChartVAt_one (N := N) (a := a) (aT := aT) S hCx ha0 ha1 ha1' haT hα hM hδ hsm hφ
    (fun z => by
      have e : ∀ i, extField G (F (fun _ => 1, θ)).1 (z : Balaban.Localization.CTorus d L N₁ m₁ 1) i =
          (F (fun _ => 1, θ)).1 (z, i) := fun i => restrictField_extField G _ z i
      simp only [e]; exact hsq z) β ψ' g x
  simp only [hres] at this ⊢
  exact this

end One

end Balaban.LargeField.Base
