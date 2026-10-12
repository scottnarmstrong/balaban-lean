/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionFPart
public import Balaban.Fluctuation.InteractionETerm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable terms of the localized interaction (FLUCTUATION §3.3, "the `δ𝓕`-part", `𝓜`-terms)

The source `𝓕_k` contains the terms `g(y, i) 𝓜^{(j)}_i(y, X)`, each a function of the raw data of
`𝔹_j(X)`; they are treated as the `δ𝓔`-part with the amplitude `g(y, i)` analytic in the source
(`mterms_locInt`; P6 (4.23): "without volume factor, `‖g‖_{ℓ¹} < 1`").
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section MPart

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- **The `𝓜`-terms of the source along the fluctuation.**  For a finite family of terms
`τ ∈ 𝒯`, each a function `E τ` of the raw data of `𝔹_j(X)` with the site `(y τ, i τ) ∈ X₁` and
the amplitude `g (y τ) (i τ)`. -/
theorem mterms_locInt {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ K)} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ K)} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ K) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ K)))
      (T : τι → Set (CTorus d L N₁ m₁ K) → (CTorus d L N₁ m₁ K → Fin N → ℂ) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) K N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (flComp (hB τ h) (hF τ h) (E τ)) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ p => p.2 (ys τ) (is τ) * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (flComp (hB τ h) (hF τ h) (E τ)) ω x₀ w σ p.1 else 0)
        (fun Y => 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt (hB τ hτ) (hF τ hτ) (hcov τ hτ) (hX₁ τ hτ) hconn hrow
        (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ) (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω
        hωb hr (Rσ := Rσ)
      refine ⟨Ev, fun _ => ?_⟩
      have := hEv.mulAmp (SG := l1Ball d L N₁ m₁ K N) (amp := fun g => g (ys τ) (is τ)) (Ma := 1)
        ((analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
        (fun g hg => norm_le_of_mem_l1Ball hg (ys τ) (is τ))
        (AgG := fun Y g g' => ∀ x ∈ Y, g x = g' x) (by
          intro Y hY g _ g' _ hag
          have hyY : ys τ ∈ Y := subset_of_mem_polymerDomains hY (by
            rw [← hX₁ τ hτ]; exact hys τ hτ)
          exact congrFun (hag _ hyY) _)
      simpa [hτ] using this
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ => polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ K)) => i.1.1)
      Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)),
    fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ, LocInt.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

end MPart

end Balaban.Localization
