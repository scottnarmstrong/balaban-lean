/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldCoverSlices
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The DL-gap and the smallness of the birth-domain inclusion from the class constants

The class radii are `ε_j = α₀ (1 + ∑_{m ≥ j} m^{-2}) L^{-jα}`.  With `ε′ ≤ ε_{k+1}`,
`δ₃, δ_fl ≤ c ε_k`, `L^α ≥ 16 C₀⁴`, `16 C₀² K₂' (c₃ + c_fl) ≤ 1`, `K_m τ ≤ 1` and
`α₀ (1 + ∑ m^{-2})` small, the DL-gap and the four smallness conditions of
`classOldDec_expansion_cover_birth_slices` hold for every `j ≤ k`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

/-- The sequence `ε_j` is nonnegative for `α₀ ≥ 0`. -/
theorem epsSeq_nonneg' (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) (j : ℕ) :
    0 ≤ epsSeq L α α₀ j := by
  unfold epsSeq
  have := epsTail_pos j
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

/-- `ε_i ≤ ε_j` for `j ≤ i` (for `α ≥ 0`, `α₀ ≥ 0`). -/
theorem epsSeq_anti (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hα : 0 ≤ α) {j i : ℕ}
    (h : j ≤ i) : epsSeq L α α₀ i ≤ epsSeq L α α₀ j := by
  have hq1 : 1 - (1 - (L : ℝ) ^ (-α)) = (L : ℝ) ^ (-α) := by ring
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hq : (L : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  induction i, h using Nat.le_induction with
  | base => exact le_rfl
  | succ i _ ih =>
    have h1 := epsSeq_gapE L α α₀ hα₀ i
    rw [hq1] at h1
    have h0 := epsSeq_nonneg' L α α₀ hα₀ i
    nlinarith

/-- `ε_{k+1} ≤ L^{-α} ε_j` for `j ≤ k`. -/
theorem epsSeq_succ_le_of_le (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hα : 0 ≤ α)
    {j k : ℕ} (h : j ≤ k) :
    epsSeq L α α₀ (k + 1) ≤ (L : ℝ) ^ (-α) * epsSeq L α α₀ j := by
  have hq1 : 1 - (1 - (L : ℝ) ^ (-α)) = (L : ℝ) ^ (-α) := by ring
  have h1 := epsSeq_gapE L α α₀ hα₀ k
  rw [hq1] at h1
  have hq0 : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact h1.trans (mul_le_mul_of_nonneg_left (epsSeq_anti L α α₀ hα₀ hα h) hq0)

/-- `ε_j ≤ α₀ (1 + ∑_{m ≥ 0} m^{-2})`. -/
theorem epsSeq_le_tail_zero (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hα : 0 ≤ α) (j : ℕ) :
    epsSeq L α α₀ j ≤ α₀ * epsTail 0 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hq : (L : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hq0 : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT : epsTail j ≤ epsTail 0 := by
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (epsTail_succ_le j).trans ih
  have h1 : ((L : ℝ) ^ (-α)) ^ j ≤ 1 := pow_le_one₀ hq0 hq
  have hp := epsTail_pos j
  unfold epsSeq
  calc α₀ * epsTail j * ((L : ℝ) ^ (-α)) ^ j ≤ α₀ * epsTail j * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ α₀ * epsTail 0 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hT hα₀

/-- **The DL-gap from constants (abstract form).**  With `ε′ ≤ s / Λ`, `Λ ≥ 16 C₀⁴`,
`δ₃ ≤ c₃ s`, `δ_fl ≤ c_fl s`, `16 C₀² K₂′ (c₃ + c_fl) ≤ 1`, `s ≤ A`, `(N+1) K₂ A ≤ 4` and
`K_m τ ≤ 1`, the left side of the DL-gap is at most `s`. -/
theorem dlGap_of_consts (d L N : ℕ) [NeZero L]
    {eps δ₃ δfl s Λ c₃ cfl τ A : ℝ} (hs0 : 0 ≤ s) (hsA : s ≤ A)
    (hA : ((N : ℝ) + 1) * cK2 d L N * A ≤ 4) (heps0 : 0 ≤ eps) (hδ₃0 : 0 ≤ δ₃)
    (hδfl0 : 0 ≤ δfl) (hΛ : 16 * scaledC0 d ^ 4 ≤ Λ) (heps : eps ≤ s / Λ)
    (hδ₃ : δ₃ ≤ c₃ * s) (hδfl : δfl ≤ cfl * s)
    (hc : 16 * scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) ≤ 1) (hτ0 : 0 ≤ τ)
    (hτ : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ ≤ 1) :
    (2 * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) +
        2 * ((N : ℝ) + 1) * (cK2 d L N * (scaledC0 d ^ 2 *
          (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)) ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ) ≤ s := by
  have hC : 0 < scaledC0 d := by unfold scaledC0; positivity
  have hK2 : 0 < cK2 d L N := cK2_pos d L N
  have hX : 0 ≤ xiK2 d L N := by unfold xiK2; positivity
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ
  -- C₀⁴ ε′ ≤ s/16
  have e1 : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps) ≤ s / 16 := by
    have : eps * Λ ≤ s := (le_div_iff₀ hΛ0).mp heps
    have h4 : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps) * 16 ≤ eps * Λ := by
      have : scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps) * 16 = eps * (16 * scaledC0 d ^ 4) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hΛ heps0
    linarith
  have e2 : scaledC0 d ^ 2 * (xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤ s / 16 := by
    have h5 : scaledC0 d ^ 2 * (xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤
        scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) * s := by
      have : scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) * s =
          scaledC0 d ^ 2 * (xiK2 d L N * (c₃ * s) + xiK2 d L N * (cfl * s)) := by ring
      rw [this]
      gcongr
    have h6 : scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) * s * 16 ≤ s := by
      have : scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) * s * 16 =
          (16 * scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl)) * s := by ring
      rw [this]; nlinarith
    linarith
  set E := scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
    with hE
  have hE0 : 0 ≤ E := by positivity
  have hE1 : E ≤ s / 8 := by
    have : E = scaledC0 d ^ 2 * (scaledC0 d ^ 2 * eps) +
        scaledC0 d ^ 2 * (xiK2 d L N * δ₃ + xiK2 d L N * δfl) := by rw [hE]; ring
    linarith
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hNK : 0 ≤ ((N : ℝ) + 1) * cK2 d L N := by positivity
  have h2 : 2 * (((N : ℝ) + 1) * cK2 d L N) * E ≤ 1 := by
    have : ((N : ℝ) + 1) * cK2 d L N * E ≤ ((N : ℝ) + 1) * cK2 d L N * (A / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hNK
    nlinarith
  have h3 : 2 * E + 2 * ((N : ℝ) + 1) * (cK2 d L N * E ^ 2) ≤ 3 * E := by
    have : 2 * ((N : ℝ) + 1) * (cK2 d L N * E ^ 2) =
        (2 * (((N : ℝ) + 1) * cK2 d L N) * E) * E := by ring
    rw [this]; nlinarith
  have h4 : 0 ≤ 2 * E + 2 * ((N : ℝ) + 1) * (cK2 d L N * E ^ 2) := by positivity
  calc (2 * E + 2 * ((N : ℝ) + 1) * (cK2 d L N * E ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * τ)
      ≤ (3 * E) * 2 := mul_le_mul h3 (by linarith) (by positivity) (by positivity)
    _ ≤ s := by linarith

/-! ### The composed theorem -/

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **`classOldDec_expansion_cover_birth` from the level-`j` slices.**  Of the term clauses on the
birth-mass domain only three slices at the label `(j, y, X)` are used: the specification of the
generating set `𝔹_j(X)` (clause `gs_spec`, whose part above `j` gives `hΩ` of the chart inclusion),
analyticity of `ℰ^{(j)}(y, X)` on the level-`j` domain and its bound there (clauses `analyticE`,
`boundE`).  These are what `SFTermClauses.inherit_le` returns at the level `j ≤ k` for the class of
the birth step. -/
theorem classOldDec_expansion_cover_birth_consts [NeZero N] {P : Consts} {μ : ℝ}
    {α α₀ c₃ cfl A : ℝ}
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
    (heps : 0 < eps) (hδ₃ : 0 ≤ δ₃) (hδfl : 0 ≤ δfl)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hα₀ : 0 ≤ α₀) (hα0 : 0 ≤ α) (hc₃ : 0 ≤ c₃) (hcfl : 0 ≤ cfl)
    (hepsK : eps ≤ epsSeq L α α₀ (k + 1)) (hδ₃K : δ₃ ≤ c₃ * epsSeq L α α₀ k)
    (hδflK : δfl ≤ cfl * epsSeq L α α₀ k)
    (hLα : 16 * scaledC0 d ^ 4 ≤ (L : ℝ) ^ α)
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
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
  have hs0 := epsSeq_nonneg' L α α₀ hα₀ j
  have hsA : epsSeq L α α₀ j ≤ A := hAdef ▸ epsSeq_le_tail_zero L α α₀ hα₀ hα0 j
  have hτ0 : 0 ≤ Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 := by
    have : 0 ≤ 3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q))) := by
      have : 0 < 1 - q := by linarith
      positivity
    linarith [Real.one_le_exp this]
  have hr0 : 0 ≤ r := hτ0.trans hτr.le
  have hτ1 : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
      (Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1) ≤ 1 := by
    have h0 : 0 ≤ 1 + 16 * ((N : ℝ) + 1) * cK2 d L N := by
      have := cK2_pos d L N; positivity
    exact (mul_le_mul_of_nonneg_left hτr.le h0).trans hrK
  have hLpos : 0 < (L : ℝ) ^ α := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hε1 : eps ≤ epsSeq L α α₀ j / (L : ℝ) ^ α := by
    have h := epsSeq_succ_le_of_le L α α₀ hα₀ hα0 hjk
    rw [Real.rpow_neg (Nat.cast_nonneg _), inv_mul_eq_div] at h
    exact hepsK.trans h
  have hkj := epsSeq_anti L α α₀ hα₀ hα0 hjk
  have hDL := dlGap_of_consts d L N hs0 hsA hAK heps.le hδ₃ hδfl hLα hε1
    (hδ₃K.trans (mul_le_mul_of_nonneg_left hkj hc₃))
    (hδflK.trans (mul_le_mul_of_nonneg_left hkj hcfl)) hcc hτ0 hτ1
  have hsmε : (4 * d + 6) * ((2 * d + 1) * epsSeq L α α₀ j) ≤ 1 := by
    refine le_trans ?_ hsmA
    gcongr
  have hc1ε : 4 * (xiC1 d * epsSeq L α α₀ j) ≤ bgC1 d L N := by
    refine le_trans ?_ hc1A
    have : 0 ≤ xiC1 d := by unfold xiC1; positivity
    gcongr
  have hKε : bgK1 d L N * (xiC1 d * epsSeq L α α₀ j) + 3 * r ≤ deltaStar d L N := by
    refine le_trans ?_ hKA
    have : 0 ≤ xiC1 d := by unfold xiC1; positivity
    have : 0 ≤ bgK1 d L N := (bgK1_pos d L N).le
    gcongr
  have hζε : 8 * epsSeq L α α₀ j * r ≤ deltaStar d L N := by
    refine le_trans ?_ hζA
    gcongr
  classOldDec_expansion_cover_of_slices C hm hAn hBd hβ hE₀ hN hjk hXp hk hG hG' cc hcψ hMX hdm hα
    hsm hδ₁ hconn hrow hκ₀ hκdec hκ h1 hlog hκP
    (xiCRaw_dom_birth_flow_unitfree H H' (hgs.2 (j + 1) (Nat.lt_succ_self j))
      heps hδ₃ hδfl hq0 hq1 hc hs hξ hμ hτr hr hDL hsmε hc1ε hKε hζε)

end Balaban.Fluctuation
