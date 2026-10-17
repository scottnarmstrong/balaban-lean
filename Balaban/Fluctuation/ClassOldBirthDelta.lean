/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldBirthConsts
public import Balaban.Localization.I5Close
public import Balaban.Localization.I5FluctFacts
import Mathlib.Tactic.Positivity

/-!
# The closeness radius `δ₃` and the fluctuation radius `δfl` as multiples of `ε_k`

`ChainNum.close` asks `N · composedCloseBound(…, C_{Ξ1} ε′, r₀) ≤ δ₃`, and `composedCloseBound` is
linear in the radius (`closeConst` is linear in its last argument).  The smallest admissible
choice `δ₃ = N · composedCloseBound(…)` is at most `c₃ ε_k` with
`c₃ = N C_{Ξ1} L^{-α} · composedCloseBound(…, 1, r₀)`, and `c₃` is at most `η` as soon as
`γ_w (r₀ − 4dL³) L^{m₁} / L ≥ log (Λ₀ / η)`.  `FlNum.flb` asks `N (5 K₂″ δ₁ + δ₁) ≤ δfl` for the
free radius `δ₁`; with `δ₁ ≤ c_δ ε_k` the choice `δfl = N (5 K₂″ δ₁ + δ₁)` is at most
`c_fl ε_k`, `c_fl = N (5 K₂″ + 1) c_δ`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

theorem composedCloseBound_smul (d L N m₁ : ℕ) [NeZero L] (BG κ δ r₀ : ℝ) :
    composedCloseBound d L N m₁ BG κ δ r₀ = δ * composedCloseBound d L N m₁ BG κ 1 r₀ := by
  unfold composedCloseBound closeConst
  ring

theorem delta3_nonneg {d L N m₁ : ℕ} [NeZero L] {BG κ eps r₀ δ₃ : ℝ} (hBG : 0 ≤ BG)
    (hd : 0 < d) (heps : 0 ≤ eps)
    (hδ₃ : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀) : 0 ≤ δ₃ := by
  have h0 : 0 ≤ xiC1 d := by unfold xiC1; positivity
  rw [hδ₃]
  have := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG (mul_nonneg h0 heps) hd
  positivity

/-- **`δ₃ ≤ c₃ ε_k`.**  The choice `δ₃ = N · composedCloseBound(…, C_{Ξ1} ε′, r₀)` (the smallest
value allowed by `ChainNum.close`) satisfies `δ₃ ≤ c₃ ε_k` with
`c₃ = N C_{Ξ1} L^{-α} composedCloseBound(…, 1, r₀)`, for `ε′ ≤ ε_{k+1}`. -/
theorem delta3_le_of_close {d L N m₁ k : ℕ} [NeZero L] {BG κ eps r₀ δ₃ α α₀ c₃ : ℝ}
    (hα₀ : 0 ≤ α₀) (hα : 0 ≤ α) (hBG : 0 ≤ BG) (hd : 0 < d)
    (hepsK : eps ≤ epsSeq L α α₀ (k + 1))
    (hδ₃ : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀)
    (hc₃ : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀) :
    δ₃ ≤ c₃ * epsSeq L α α₀ k := by
  have h0 : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hc1 := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG (zero_le_one) hd
  have hs := epsSeq_succ_le_of_le L α α₀ hα₀ hα (le_refl k)
  have he : eps ≤ (L : ℝ) ^ (-α) * epsSeq L α α₀ k := hepsK.trans hs
  rw [hδ₃, hc₃, composedCloseBound_smul d L N m₁ BG κ (xiC1 d * eps) r₀]
  have : xiC1 d * eps ≤ xiC1 d * ((L : ℝ) ^ (-α) * epsSeq L α α₀ k) :=
    mul_le_mul_of_nonneg_left he h0
  have h2 : N * ((xiC1 d * eps) * composedCloseBound d L N m₁ BG κ 1 r₀) ≤
      N * ((xiC1 d * ((L : ℝ) ^ (-α) * epsSeq L α α₀ k)) *
        composedCloseBound d L N m₁ BG κ 1 r₀) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hc1) (Nat.cast_nonneg _)
  calc _ ≤ _ := h2
    _ = _ := by ring

/-- **`c₃` is small for a long decay length.**  If `Λ₀ = N C_{Ξ1} · 10 e^{2dγ_w} closeConst(…,
lemma53Const)` is positive, `η > 0` and
`log (Λ₀ / η) ≤ γ_w (r₀ − 4dL³) L^{m₁} / L`, then `c₃ ≤ η` (`α ≥ 0`). -/
theorem c3_le_of_decay {d L N m₁ : ℕ} [NeZero L] {BG κ r₀ α η c₃ : ℝ} (hα : 0 ≤ α)
    (hBG : 0 ≤ BG) (hd : 0 < d) (hη : 0 < η)
    (hΛ : 0 < N * xiC1 d * (10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * 1)))
    (hM : Real.log ((N * xiC1 d * (10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * 1))) / η) ≤
      gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))
    (hc₃ : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀) :
    c₃ ≤ η := by
  set Λ := N * xiC1 d * (10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * 1)) with hΛdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hq : (L : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hq0 : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hexp : Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) ≤
      η / Λ := by
    have h1 : Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) ≤
        Real.exp (-Real.log (Λ / η)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg (Real.log (Λ / η)), Real.exp_log (div_pos hΛ hη), inv_div] at h1
    exact h1
  have hc1 := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG (zero_le_one) hd
  have hB : composedCloseBound d L N m₁ BG κ 1 r₀ =
      10 * Real.exp (gammaW d * (2 * d)) * closeConst d L N BG κ (lemma53Const d L * 1) *
        Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := rfl
  have hN : 0 ≤ (N : ℝ) * xiC1 d := by
    have : 0 ≤ xiC1 d := by unfold xiC1; positivity
    positivity
  have h1 : c₃ ≤ N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀ := by
    rw [hc₃]
    have : (N : ℝ) * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀ =
        (N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀) * (L : ℝ) ^ (-α) := by ring
    rw [this]
    have h2 : 0 ≤ N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀ := by positivity
    calc _ ≤ (N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀) * 1 :=
          mul_le_mul_of_nonneg_left hq h2
      _ = _ := mul_one _
  have h3 : N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀ =
      Λ * Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
    rw [hB, hΛdef]; ring
  have h4 : Λ * Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) ≤ η := by
    calc _ ≤ Λ * (η / Λ) := mul_le_mul_of_nonneg_left hexp hΛ.le
      _ = η := by field_simp
  linarith

/-- **`δfl ≤ c_fl ε_k`.**  The choice `δfl = N (5 K₂″ δ₁ + δ₁)` (the smallest value allowed by
`FlNum.flb`) satisfies `δfl ≤ c_fl ε_k`, `c_fl = N (5 K₂″ + 1) c_δ`, when the free fluctuation
radius satisfies `δ₁ ≤ c_δ ε_k`. -/
theorem deltafl_le_of_flb {d L N k : ℕ} [NeZero L] {BG₂ κ δ₁ δfl α α₀ cδ cfl : ℝ}
    (hBG₂ : 0 ≤ BG₂) (hd : 0 < d) (hδ₁ : 0 ≤ δ₁)
    (hδ₁k : δ₁ ≤ cδ * epsSeq L α α₀ k)
    (hδfl : δfl = N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁))
    (hcfl : cfl = N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) * cδ) :
    0 ≤ δfl ∧ δfl ≤ cfl * epsSeq L α α₀ k := by
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
  have hK := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  refine ⟨by rw [hδfl]; positivity, ?_⟩
  rw [hδfl, hcfl]
  have h : 0 ≤ (N : ℝ) * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) := by positivity
  calc (N : ℝ) * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁)
      = (N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1)) * δ₁ := by ring
    _ ≤ (N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1)) * (cδ * epsSeq L α α₀ k) :=
        mul_le_mul_of_nonneg_left hδ₁k h
    _ = _ := by ring

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **The birth-domain old-cover expansion with constant conditions only.**  The radii are
`δ₃ = N · composedCloseBound(…, C_{Ξ1} ε′, r₀)` and `δfl = N (5 K₂″ δ₁ + δ₁)`, with `δ₁ ≤ c_δ ε_k`;
the remaining hypotheses are the constants `L^α`, `c₃`, `c_fl`, `α₀`, `r`. -/
theorem classOldDec_expansion_cover_birth_consts_delta [NeZero N] {P : Consts} {μ : ℝ}
    {α α₀ c₃ cfl A cδ : ℝ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    {j : ℕ} {y : CTorus d L N₁ m₁ (k + 1)}
    (hgs : X ⊆ ↑((C.Tm.gs j X).Ω 1) ∧ ∀ i, j < i → (C.Tm.gs j X).Ω i = ∅)
    (hAn : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => C.Tm.E j y X p.1 p.2)
      {p | (xiFieldDom (compWeight L a₁) μ (epsSeq L α α₀) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (C.Tm.gs j X) p.1 p.2})
    (hBd : ∀ Ψ h, (xiFieldDom (compWeight L a₁) μ (epsSeq L α α₀) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (C.Tm.gs j X) Ψ h → ‖C.Tm.E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X))
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) (hN : L ^ C.m₀ ∣ N₁) (hjk : j ≤ k)
    (hXp : IsPolyDom C.m₀ j X)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    {K : ℕ} {ξ : ℕ → Fin 3 → ℂ} {q c₈ r : ℝ}
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (H' : BgHyp d L (k + 1) ϱ (compWeight L a₁) μ)
    (heps : 0 < eps)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hα₀ : 0 ≤ α₀) (hα0 : 0 ≤ α) (hBG : 0 ≤ BG) (hBG₂ : 0 ≤ BG₂) (hδ₁0 : 0 ≤ δ₁) (hd : 0 < d) (hcδ : 0 ≤ cδ)
    (hδ₃def : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀)
    (hδfldef : δfl = N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁))
    (hδ₁k : δ₁ ≤ cδ * epsSeq L α α₀ k)
    (hc₃def : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀)
    (hcfldef : cfl = N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) * cδ)
    (hepsK : eps ≤ epsSeq L α α₀ (k + 1)) (hLα : 16 * scaledC0 d ^ 4 ≤ (L : ℝ) ^ α)
    (hcc : 16 * scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) ≤ 1)
    (hAdef : A = α₀ * epsTail 0)
    (hAK : ((N : ℝ) + 1) * cK2 d L N * A ≤ 4)
    (hrK : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * r ≤ 1)
    (hsmA : (4 * d + 6) * ((2 * d + 1) * A) ≤ 1) (hc1A : 4 * (xiC1 d * A) ≤ bgC1 d L N)
    (hKA : bgK1 d L N * (xiC1 d * A) + 3 * r ≤ deltaStar d L N)
    (hζA : 8 * A * r ≤ deltaStar d L N) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)),
      ∀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1)),
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X →
        ∀ (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f),
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
        (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
          ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
          flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
            (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
          Ev Y u = Ev Y u') ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
        (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hc₃0 : 0 ≤ c₃ := by
    have h0 : 0 ≤ xiC1 d := by unfold xiC1; positivity
    have hq0 : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
      hBG (zero_le_one) hd
    rw [hc₃def]; positivity
  have hδ₃ := delta3_nonneg hBG hd heps.le hδ₃def
  obtain ⟨hδfl, hδflK⟩ := deltafl_le_of_flb (L := L) (k := k) (α := α) (α₀ := α₀) (κ := κ)
    hBG₂ hd hδ₁0 hδ₁k hδfldef hcfldef
  have hcfl : 0 ≤ cfl := by
    have hB0 : 0 ≤ famConst d L BG₂ κ := by
      have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
    have hK := cK2'_nonneg (d := d) (L := L) (N := N) hB0
    rw [hcfldef]; positivity
  exact classOldDec_expansion_cover_birth_consts C hm hgs hAn hBd hβ hE₀ hN hjk hXp hk hG hG' cc
    hcψ hMX hdm hα hsm hδ₁ hconn hrow hκ₀ hκdec hκ h1 hlog hκP H H' heps hδ₃ hδfl hq0 hq1 hc hs
    hξ hμ hτr hr hα₀ hα0 hc₃0 hcfl hepsK
    (delta3_le_of_close hα₀ hα0 hBG hd hepsK hδ₃def hc₃def) hδflK hLα hcc hAdef hAK hrK hsmA hc1A
    hKA hζA

end Balaban.Fluctuation
