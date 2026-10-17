/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyGenAct
public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Positivity

/-!
# The amplitude bound of the activity family (`LocalClassDensityFamilyGenAmp`)

The activity of a domain `Y` at the first mark `u` is the difference
`H(u) = ∑_τ β (evDec(u, 0) - evDec(0, 0))`, so `H(0) = 0`, and `u ↦ H(u)` is holomorphic on the
disc `‖u‖ < a′` and bounded there by `B_Y = ∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d(Y)}`
(`classActivityFamily_fields_gen`, radius `a′`, `(a′ + b′) · markedRad < δ₁`).  The Schwarz lemma
at the radius `a′` gives `‖H(u)‖ ≤ (r / a′) B_Y` for `‖u‖ ≤ r < a′`.  For `r = corrU` this is the
factor `corrU / a′` of the fluctuation: with `markedRad = √N ‖cc‖ C_sup c_ψ` and `‖cc‖ = β_k^{-1/2}`,
the choice `a′ = δ₁ / (2 markedRad)`, `b′ = 0` is admissible and `r / a′ = 2 r markedRad / δ₁`.

* `norm_le_of_ball_bound_zero`: the Schwarz bound `‖f c‖ ≤ B ‖c‖ / R` for `f 0 = 0`;
* `markedRad_radius_admissible`, `div_markedRad_radius_eq`: the radius `a′ = δ₁ / (2 markedRad)`;
* `classActivityFamily_amplitude_gen`: the amplitude bound for the activities of
  `classActivityFamily_fields_gen`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix Metric

section Schwarz

/-- **The Schwarz bound for a function vanishing at `0`**: if `f` is complex differentiable on the
disc `|w| < R`, `‖f‖ ≤ B` there and `f 0 = 0`, then `‖f c‖ ≤ B ‖c‖ / R` for `|c| < R`. -/
theorem norm_le_of_ball_bound_zero {f : ℂ → ℂ} {R B : ℝ}
    (hd : DifferentiableOn ℂ f (ball 0 R)) (hB : ∀ w ∈ ball (0 : ℂ) R, ‖f w‖ ≤ B)
    (h0 : f 0 = 0) {c : ℂ} (hc : ‖c‖ < R) : ‖f c‖ ≤ B * ‖c‖ / R := by
  have hmaps : Set.MapsTo f (ball 0 R) (closedBall (f 0) B) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, h0, sub_zero]
    exact hB w hw
  have hcm : c ∈ ball (0 : ℂ) R := by rwa [mem_ball, dist_zero_right]
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hcm
  rw [dist_eq_norm, dist_zero_right, h0, sub_zero] at h
  calc ‖f c‖ ≤ B / R * ‖c‖ := h
    _ = B * ‖c‖ / R := by ring

/-- **The radius `a′ = δ₁ / (2 markedRad)` is admissible**: `(a′ + 0) · markedRad = δ₁ / 2 < δ₁`. -/
theorem markedRad_radius_admissible (d L N k : ℕ) (a₁ κ cψ : ℝ) (cc : ℂ) {δ₁ : ℝ}
    (hδ : 0 < δ₁) (hm : 0 < markedRad d L N k a₁ κ cψ cc) :
    (δ₁ / (2 * markedRad d L N k a₁ κ cψ cc) + 0) * markedRad d L N k a₁ κ cψ cc < δ₁ := by
  rw [add_zero, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **The amplitude factor**: at the radius `a′ = δ₁ / (2 markedRad)`, `r / a′ = 2 r markedRad / δ₁`,
that is `2 r √N ‖cc‖ C_sup c_ψ / δ₁`; for `‖cc‖ = β_k^{-1/2}` this is proportional to
`β_k^{-1/2} c_ψ / δ₁`. -/
theorem div_markedRad_radius_eq (d L N k : ℕ) (a₁ κ cψ : ℝ) (cc : ℂ) {δ₁ : ℝ} (r : ℝ)
    (hδ : 0 < δ₁) :
    r / (δ₁ / (2 * markedRad d L N k a₁ κ cψ cc)) =
      2 * r * (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) / δ₁ := by
  have : markedRad d L N k a₁ κ cψ cc =
      Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) := rfl
  rw [← this]
  field_simp

end Schwarz

section AmpGen

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The amplitude bound of the activity family of a generic label functional.**  Under the
hypotheses of `classActivityFamily_fields_gen` at the radius `a` (`1 < a`, `0 ≤ b′`,
`(a + b′) · markedRad < δ₁`), the activities `H θ Y u` of the domains of `𝒴C` satisfy, for
`θ ∈ physV`, `‖u‖ ≤ r < a`,
`‖H θ Y u Φ‖ ≤ (r / a) ∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{m₀}(Y)}`:
the bound of `classActivityFamily_fields_gen` is multiplied by `r / a` (Schwarz at the radius `a`,
`H θ Y 0 Φ = 0`). -/
theorem classActivityFamily_amplitude_gen {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d)
    (Zm : Finset (unitPts S.G')) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0) :
    ∀ θ ∈ physV S a₁ ν eps, ∀ (Y : {Y // Y ∈ 𝒴C}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) (u : ℂ)
      (r : ℝ), ‖u‖ ≤ r → r < a → ‖H θ Y u Φ‖ ≤ r / a *
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
            2 * κdec * treeLenCov S.G' m₀ Y.1)
        else 0 := by
  obtain ⟨-, -, hbd, -, -, hhol, -⟩ := classActivityFamily_fields_gen S hb₁ hbC Eτ Bτ hBτ hβ jL
    XL Gk Gj X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hEan hEbd F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hN hm1 hd Zm hρ hρc hp ha1 hbb hab 𝒴C
    h𝒴 H hH
  intro θ hθ Y Φ u r hu hra
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have h0 : H θ Y 0 Φ = 0 := by
    rw [hH θ Y 0 Φ]
    split_ifs
    · simp
    · rfl
  have hB0 := (norm_nonneg (H θ Y 0 Φ)).trans (hbd θ Y 0 Φ)
  have hu' : ‖u‖ < a := lt_of_le_of_lt hu hra
  have hS := norm_le_of_ball_bound_zero (f := fun w => H θ Y w Φ) (hhol θ hθ Y Φ)
    (fun w _ => hbd θ Y w Φ) h0 hu'
  refine hS.trans ?_
  calc _ ≤ _ * r / a := by gcongr
    _ = _ := by ring

end AmpGen

end Balaban.Fluctuation
