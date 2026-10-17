/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassBirthResponse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Birth-mass domains of the old terms: the chart of `ClassOldCover.hchart`

The chart points of `classOldDec_expansion_cover` are the raw data of
`Ξ^c_j(𝔹_j(X); C₀, e)` at the step mass `ν`, with `C₀ = scaledC0 d` and
`e = C₀² ε′ + K₂ δ₃ + K₂ δfl`.  The old terms keep the domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` at the birth
mass `μ = ν (1 + t)` (decision D2(b)).

* `xiDom_birth_of_unit_realization`: the inclusion for a chart point that has a realization with a
  unit real witness `|h₀| = 1` (the pinned scheme of `notes/phase1/MASS-LEVEL.md` §5).  This is
  weaker than `xiDom_birth_of_unit`, which asks the unit property of every realization.
* `xiDom_birth_chart`: the same with all smallness hypotheses reduced to inequalities on the
  class radius `ε_j` and on the mass defect `τ ≥ |t|`, and the exact (DL-gap)
  `C₀² (C₀² ε′ + K₂ δ₃ + K₂ δfl) (1 + K_m τ) ≤ ε_j`, `K_m = 1 + 16 (N+1) cK2`.
* `xiCRaw_dom_birth`: `hchart` at the birth mass, as an inclusion of `XiCRaw` into the domain
  `xiFieldDom A μ ε`.
* `xiCRaw_dom_birth_flow`: the same with `μ = ν ∏_{n ∈ [j, K)} (1 + ξ₃)/(1 + ξ₂)` and the flow
  bound `‖ξ_n‖ ≤ (c₈/4) q^{n+1}`.
* `xiDom_birth_chart_top`: the case `j = K` (the top level), with no witness condition.

Which inequality is the (DL-gap): the displayed one.  The landed `ChainNum` fields `small₂`, `th2`,
`c1`, `K1s` are about `C₀² ε′ + K₂ δ₃` (without the factor `C₀²` of the rescaling `Ξ^c(C₀, e) ⊆
Ξ^c(1, C₀² e)` and without `δfl`), so they do not imply the smallness of `C₀² e`; that is why the
smallness hypotheses `hsmε`, `hc1ε`, `hKε`, `hζε` are stated for `ε_j` (note `C₀² e ≤ ε_j`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6v2 Balaban.Flow

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The birth inclusion for a chart point with a unit real witness.**  As `xiDom_birth_of_unit`,
but the unit property `∑ h₀² = 1` is required only for one realization of the chart point at
scale `C₀`. -/
theorem xiDom_birth_of_unit_realization {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ C₀ e e₁ εj t r : ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (hσ : 1 ≤ C₀) (hrad : C₀ ^ 2 * e ≤ e₁)
    (hε : 0 < e₁) (hsm : (4 * d + 6) * ((2 * d + 1) * e₁) ≤ 1)
    (hc1 : 4 * (xiC1 d * e₁) ≤ bgC1 d L N) (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1)
    (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * e₁) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * e₁ * r ≤ deltaStar d L N)
    (hee : e₁ * (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t|) ≤ εj)
    {D : BgData G N}
    (hD : ∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
      XiC G A ν j C₀ e Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'' ∧ ∑ i, h₀ i ^ 2 = 1) :
    Def6.XiDom G A μ j εj D.Ψ D.h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hxc, hR, hu⟩ := hD
  have hR' : RealizesC D Ψ₀ h₀ (fun x i => D.Ψ x i - Ψ₀ x i) (fun x i => D.h x i - h₀ i) :=
    ⟨fun x hx i => by simp [hR.1 x hx i], fun x hx i => by simp [hR.2 x hx i]⟩
  have hx1 : XiC G A ν j 1 e₁ Ψ₀ h₀ (fun x i => D.Ψ x i - Ψ₀ x i) (fun x i => D.h x i - h₀ i) :=
    xiC_rescale_of_agree hσ hrad (fun x hx i => by rw [hR.1 x hx i]; ring)
      (fun x hx i => by rw [hR.2 x hx i]; ring) hxc
  refine ⟨Ψ₀, h₀, fun x i => D.Ψ x i - Ψ₀ x i, fun x i => D.h x i - h₀ i,
    fun x i => by ring, fun x i => by ring, Def6v2.xiC_mono_eps zero_le_one hee
      (xiC_massResponse H H' hε hsm hc1 hμ ht1 htr hr hK hζ ?_ hx1)⟩
  rw [hu]; simpa using by positivity

/-- The arithmetic of the chart radius `e₁ = C₀² e`, `e = C₀² ε′ + K₂ δ₃ + K₂ δfl`: the five
smallness hypotheses of the birth inclusion follow from their `ε_j`-forms and the (DL-gap). -/
theorem chart_numerics {eps δ₃ δfl εj τ r t : ℝ} (hd : 0 < d) (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃)
    (hδfl : 0 ≤ δfl) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ εj)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εj) ≤ 1) (hc1ε : 4 * (xiC1 d * εj) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εj) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εj * r ≤ deltaStar d L N) :
    0 < scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ∧
    (4 * d + 6) * ((2 * d + 1) * (scaledC0 d ^ 2 *
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) ≤ 1 ∧
    4 * (xiC1 d * (scaledC0 d ^ 2 *
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) ≤ bgC1 d L N ∧
    |t| ≤ 1 ∧ |t| < r ∧
    bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 *
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) + 3 * r ≤ deltaStar d L N ∧
    8 * (scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) * r ≤
      deltaStar d L N ∧
    scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t|) ≤ εj := by
  have hC : 0 < scaledC0 d := by unfold scaledC0; positivity
  have hQ := cK2_pos d L N
  have hK2 : 0 < xiK2 d L N := by unfold xiK2; positivity
  have hx1 : 1 ≤ xiC1 d := one_le_xiC1 d
  have hB := bgK1_pos (d := d) (L := L) (N := N)
  have hds : 0 ≤ deltaStar d L N := (deltaStar_pos (d := d) (L := L) (N := N) hd).le
  set e₁ := scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) with he₁
  have he₁0 : 0 < e₁ := by rw [he₁]; positivity
  have hτ0 : 0 ≤ τ := (abs_nonneg t).trans ht
  have hKm : 0 ≤ 1 + 16 * ((N : ℝ) + 1) * cK2 d L N := by positivity
  have hle : e₁ ≤ εj := by
    refine le_trans ?_ hDL
    have : 0 ≤ (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ := by positivity
    nlinarith
  have hr0 : 0 ≤ r := hτ0.trans hτr.le
  refine ⟨he₁0, ?_, ?_, ?_, ht.trans_lt hτr, ?_, ?_, ?_⟩
  · refine le_trans ?_ hsmε; gcongr
  · refine le_trans ?_ hc1ε; gcongr
  · linarith [ht.trans hτr.le]
  · refine le_trans ?_ hKε; gcongr
  · refine le_trans ?_ hζε; gcongr
  · refine le_trans ?_ hDL
    have : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t| ≤
        (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ := by gcongr
    nlinarith

/-- **The chart point lies in the birth-mass domain** (decision D2(b)), for the actual chart data
of `ClassOldCover.hchart`: `D` realizes a member of `Ξ^c_j(𝔹; C₀, e)` at the step mass `ν`,
`C₀ = scaledC0 d`, `e = C₀² ε′ + K₂ δ₃ + K₂ δfl`, with a unit real witness; the birth mass is
`μ = ν (1 + t)`, `|t| ≤ τ`.  Hypotheses: `heps`, `hδ₃`, `hδfl` (fields `eps_pos`, `δ₃_nn` of
`ChainNum`, and `0 ≤ δfl`); the exact (DL-gap) `hDL`; the smallness of `ε_j`, `hsmε`, `hc1ε`,
`hKε`, `hζε`, with `τ < r ≤ 1/16`. -/
theorem xiDom_birth_chart {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ eps δ₃ δfl εj τ r t : ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hμ : μ = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ εj)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εj) ≤ 1) (hc1ε : 4 * (xiC1 d * εj) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εj) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εj * r ≤ deltaStar d L N)
    {D : BgData G N}
    (hD : ∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
      XiC G A ν j (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'' ∧ ∑ i, h₀ i ^ 2 = 1) :
    Def6.XiDom G A μ j εj D.Ψ D.h := by
  have hd : 0 < d := by have := H.hd; omega
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := chart_numerics (L := L) (N := N) hd heps hδ₃ hδfl
    ht hτr hr hDL hsmε hc1ε hKε hζε
  exact xiDom_birth_of_unit_realization H H' (one_le_scaledC0 d) le_rfl n0 n1 n2 hμ n3 n4 hr n5 n6
    n7 hD

/-- **`hchart` at the birth mass.**  The raw data of the chart `Ξ^c_j(𝔹; C₀, e)` at the step mass
`ν` that have a unit real witness lie in `xiFieldDom A μ ε`, the domain `Ξ^c_j(𝔹; 1, ε_j)` of the
old terms at their birth mass `μ`. -/
theorem xiCRaw_dom_birth {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ eps δ₃ δfl τ r t : ℝ} {εs : ℕ → ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν)
    (H' : BgHyp d L k ϱ A μ)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hμ : μ = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ εs j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εs j) ≤ 1) (hc1ε : 4 * (xiC1 d * εs j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εs j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εs j * r ≤ deltaStar d L N)
    (hunit : ∀ D : BgData G N,
      Localization.XiCData G A ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) D →
      ∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
        XiC G A ν j (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
          Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'' ∧ ∑ i, h₀ i ^ 2 = 1) :
    ∀ p ∈ Localization.XiCRaw G A ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      (xiFieldDom A μ εs : FieldDom d L N₁ m₁ k N ϱ).dom j G p.1 p.2 := by
  rintro p ⟨D, hD, rfl⟩
  exact xiDom_birth_chart H H' heps hδ₃ hδfl hμ ht hτr hr hDL hsmε hc1ε hKε hζε (hunit D hD)

/-- **`xiCRaw_dom_birth` with the birth mass given by the flow.**  If
`μ = ν ∏_{n ∈ [j, K)} (1 + ξ₃^{(n)})/(1 + ξ₂^{(n)})` (the ratio `δ_K/δ_j` of `deltaSeq`) and
`‖ξ_n‖ ≤ (c₈/4) q^{n+1}` (P4 (5.31)), the mass defect is
`τ = exp (3 (c₈/4) q^{j+1}/(1-q)) - 1` and (DL-gap) is
`C₀² e (1 + K_m τ) ≤ ε_j`. -/
theorem xiCRaw_dom_birth_flow {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ eps δ₃ δfl r : ℝ} {εs : ℕ → ℝ} {j K : ℕ} {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}
    (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hDL : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
        (Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1)) ≤ εs j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εs j) ≤ 1) (hc1ε : 4 * (xiC1 d * εs j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εs j) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εs j * r ≤ deltaStar d L N)
    (hunit : ∀ D : BgData G N,
      Localization.XiCData G A ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) D →
      ∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
        XiC G A ν j (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
          Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'' ∧ ∑ i, h₀ i ^ 2 = 1) :
    ∀ p ∈ Localization.XiCRaw G A ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      (xiFieldDom A μ εs : FieldDom d L N₁ m₁ k N ϱ).dom j G p.1 p.2 := by
  have hbd := norm_ratio_prod_sub_one_le_geom hq0 hq1 hc hs hξ j K
  obtain ⟨t, ht, htb⟩ : ∃ t : ℝ, μ = ν * (1 + t) ∧
      |t| ≤ ‖∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)) - 1‖ := by
    by_cases hν : ν = 0
    · have : μ = 0 := by
        have h0 : (μ : ℂ) = 0 := by rw [hμ, hν]; simp
        exact_mod_cast h0
      exact ⟨0, by simp [this, hν], by simp⟩
    · refine ⟨μ / ν - 1, by field_simp; ring, ?_⟩
      have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
      have e : (((μ / ν - 1 : ℝ)) : ℂ) = ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)) - 1 := by
        push_cast
        rw [hμ]; field_simp
      rw [← e, Complex.norm_real, Real.norm_eq_abs]
  exact xiCRaw_dom_birth H H' heps hδ₃ hδfl ht (htb.trans hbd) hτr hr hDL hsmε hc1ε hKε hζε hunit

/-- **The top level `j = K`**: no condition on the real witness (the norm clause is part of the
level-`K` class). -/
theorem xiDom_birth_chart_top {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ eps δ₃ δfl εj τ r t : ℝ} (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hμ : μ = ν * (1 + t)) (ht : |t| ≤ τ) (hτr : τ < r) (hr : r ≤ 1 / 16)
    (hDL : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ εj)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * εj) ≤ 1) (hc1ε : 4 * (xiC1 d * εj) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * εj) + 3 * r ≤ deltaStar d L N)
    (hζε : 8 * εj * r ≤ deltaStar d L N)
    {D : BgData G N}
    (hD : Localization.XiCData G A ν k (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) D) :
    Def6.XiDom G A μ k εj D.Ψ D.h := by
  have hd : 0 < d := by have := H.hd; omega
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := chart_numerics (L := L) (N := N) hd heps hδ₃ hδfl
    ht hτr hr hDL hsmε hc1ε hKε hζε
  exact xiDom_birth_top H H' (one_le_scaledC0 d) le_rfl n0 n1 n2 hμ n3 n4 hr n5 n6 n7 hD

end Balaban.Fluctuation
