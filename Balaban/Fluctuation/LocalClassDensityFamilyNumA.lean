/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyGenCount
public import Balaban.Fluctuation.LocalClassDensityFamilyIdx
public import Balaban.Fluctuation.LocalClassDensityFamilyGenAmp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# `hnumH` for the generic label family with irrelevant-part bounds (`LocalClassDensityFamilyNumA`)

For labels `τ = (j, y, X)` with `B_τ ≤ C_I E₀ s_{jk}^{d+α₃}` (`k - j ≥ n₁`) and `B_τ ≤ K_L E₀`
(otherwise), the per-domain sum of `classActivity_domainSum_polyDom_le_uniform` is at most
`Λ · #cells(Y) · e^{-2κ_dec d_M(Y)}` with `Λ` independent of `k`; the cells are at most
`c₁ (1 + d_M(Y))` (`cellCount_le_of_admissible`) and `d_1(Y) ≤ A_M d_M(Y) + B_M`
(`treeLenCovOne_one_le_index`).

* `cellCount_le_one_add_treeLenCovOne`: `#cells_M(Y) ≤ c₁ (1 + d^cov_M(Y))` for `Y ∈ 𝒟_j` of index `M`;
* `isDj_cells_subset`: the cells of side `cellSide L M m₁ j` of the points of `Y ∈ 𝒟_j` lie in `Y`;
* `classActivity_hnumH_of_uniform_gen`: the condition `hnumH` of `classActivityFamily_labelAct_gen`
  for the labels with irrelevant-part bounds, with `ε_C = c₁ Λ e^{κ_H B_M}`, under the rate
  condition `κ_H A_M + 1 ≤ 2 κ_dec`; the constant does not depend on `k`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Polymer Finset

section NumA

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- **The cells of a domain of index `M` against its size.**  For `Y ∈ 𝒟_j` of index `M ≥ 1`
(`L^M ∣ N₁`, `j ≤ K`): `#cells_M(Y) ≤ c₁ (1 + d^cov_M(Y))`. -/
theorem cellCount_le_one_add_treeLenCovOne {M j : ℕ} (hN : L ^ M ∣ N₁) (hj : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj M j Y) :
    (cellCount (cellSide L M m₁ j) Y : ℝ) ≤ c1 d L * (1 + treeLenCovOne M j Y) := by
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, he⟩ := treeLenCovOne_attained M j Y (by
    obtain ⟨𝒦, W, E, h⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hY
    obtain ⟨a, b, c, d⟩ := chosen_of_admissible h
    exact ⟨𝒦, W, E, a, b, c, d⟩)
  have hcM := cellCount_le_of_admissible hN hj (admissible_of_chosen h1 h2 h3 h4)
  rwa [Set.inter_univ, he] at hcM

/-- **The cell of a point of `Y ∈ 𝒟_j` lies in `Y`.** -/
theorem isDj_cells_subset {M j : ℕ} (hN : L ^ M ∣ N₁) (hj : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj M j Y) :
    ∀ y ∈ Y, box (cbase (cellSide L M m₁ j) y) (cellSide L M m₁ j) ⊆ Y := by
  intro y hy
  obtain ⟨b, hb, hyb, hbY⟩ := hY.2.1 y hy
  exact (cell_subset_cube (cellSide_dvd hN hj) (cellSide_pos M m₁ j) hb hyb).trans hbY

end NumA

section NumB

/-- The real-number step of `classActivity_hnumH_of_uniform_gen`. -/
theorem arith_step {c Λ n D κdec κH A B d1 S : ℝ} (hc : 0 ≤ c) (hΛ : 0 ≤ Λ) (hκH : 0 ≤ κH)
    (hrate : κH * A + 1 ≤ 2 * κdec) (hcell : n ≤ c * (1 + D)) (hcmp : d1 ≤ A * D + B)
    (hD : 0 ≤ D) (hsum : S ≤ n * Λ * Real.exp (-(2 * κdec * D))) :
    S ≤ c * Λ * Real.exp (κH * B) * Real.exp (-κH * d1) := by
  have h1D : 1 + D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hexp : Real.exp D * Real.exp (-(2 * κdec * D)) ≤
      Real.exp (κH * B) * Real.exp (-κH * d1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : κH * d1 ≤ κH * (A * D + B) := mul_le_mul_of_nonneg_left hcmp hκH
    have h2 : (κH * A + 1) * D ≤ 2 * κdec * D := mul_le_mul_of_nonneg_right hrate hD
    linarith
  have hE : 0 ≤ Real.exp (-(2 * κdec * D)) := (Real.exp_pos _).le
  calc S ≤ n * Λ * Real.exp (-(2 * κdec * D)) := hsum
    _ ≤ c * (1 + D) * Λ * Real.exp (-(2 * κdec * D)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcell hΛ) hE
    _ ≤ c * Real.exp D * Λ * Real.exp (-(2 * κdec * D)) := by
        have := mul_le_mul_of_nonneg_left h1D hc
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hΛ) hE
    _ = c * Λ * (Real.exp D * Real.exp (-(2 * κdec * D))) := by ring
    _ ≤ c * Λ * (Real.exp (κH * B) * Real.exp (-κH * d1)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hc hΛ)
    _ = _ := by ring

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)

open Classical in
/-- **`hnumH` for the generic label family with irrelevant-part bounds, uniformly in `k`.**
Labels `τ = (j_τ, y_τ, X_τ)` (`1 ≤ j_τ ≤ k`, `X_τ ∈ 𝒟_{j_τ}` of index `m₀ ≥ 1`, `y_τ ∈ X_τ`
aligned to `L^{j_τ}`), bounds `B_τ ≤ C_I E₀ s_{jk}^{d+α₃}` for `k - j ≥ n₁` and `B_τ ≤ K_L E₀`
for the last `n₁` levels, the domains `𝒴C` of index `m₀`, the entropy rate `κ₀ ≥ a_ent + 1` and the
rate condition `κ_H A_{m₀} + 1 ≤ 2 κ_dec` (`A_M` of `treeLenCovOne_one_le_index`).  Then on every
`Y ∈ 𝒴C`, with `Λ = (L^{(1+m₀+m₁)})^d E₀ · 2K₀(κ₀)(C_I (1 - L^{-α₃})⁻¹ + n₁ K_L L^{(n₁-1)d})`
(no dependence on `k`),
`∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d_{m₀}(Y)} ≤ c₁ Λ e^{κ_H B_{m₀}} ·
e^{-κ_H d_1(Y)}`: the hypothesis `hnumH` of `classActivityFamily_labelAct_gen` with
`ε_C = c₁ Λ e^{κ_H B_{m₀}}`. -/
theorem classActivity_hnumH_of_uniform_gen {ι : Type*} [Fintype ι] {m₀ : ℕ}
    (hm1 : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {κ₀ κdec κH : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (hκH : 0 ≤ κH)
    (hrate : κH * ((L : ℝ) ^ (m₀ - 1) + 2 * d * (L : ℝ) ^ m₀ *
      (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj : ∀ τ, 1 ≤ jL τ ∧ jL τ ≤ k) (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ) (hal : ∀ τ, Aligned (L ^ jL τ) (yL τ))
    (hinj : ∀ τ τ', jL τ = jL τ' → yL τ = yL τ' → XL τ = XL τ' → τ = τ')
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj m₀ (k + 1) Y)
    (Bτ : ι → ℝ) {CI KL E₀ α₃ : ℝ} (n₁ : ℕ) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL)
    (hE₀ : 0 ≤ E₀) (hα : 0 < α₃)
    (hEbI : ∀ τ, jL τ + n₁ ≤ k →
      Bτ τ ≤ CI * E₀ * (((L : ℝ)⁻¹ ^ (k - jL τ)) ^ ((d : ℝ) + α₃)))
    (hEbL : ∀ τ, k < jL τ + n₁ → Bτ τ ≤ KL * E₀) :
    ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y)
      else 0) ≤ (c1 d L * ((((L : ℝ) ^ (1 + m₀ + m₁)) ^ d) * E₀ *
        (2 * K0 d L κ₀ * (CI * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d)))) *
        Real.exp (κH * (2 * d * (L : ℝ) ^ m₀ * (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L))) *
        Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
  intro Y hY
  set B : ℝ := 2 * d * (L : ℝ) ^ m₀ * (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L with hB
  set A : ℝ := (L : ℝ) ^ (m₀ - 1) + B with hA
  set Λ : ℝ := (((L : ℝ) ^ (1 + m₀ + m₁)) ^ d) * E₀ *
    (2 * K0 d L κ₀ * (CI * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
      n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d))) with hΛ
  have hL0 : (0 : ℝ) < L := by positivity
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hK0 : 0 ≤ K0 d L κ₀ := by
    unfold K0
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have : 0 < 1 - Real.exp (-1) := by linarith
    positivity
  have hq1 : (L : ℝ) ^ (-α₃) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have hq0 : 0 < 1 - (L : ℝ) ^ (-α₃) := by linarith
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    positivity
  have hc10 : 0 ≤ c1 d L := by unfold c1; positivity
  have hdj := h𝒴dj Y hY
  have hsum := classActivity_domainSum_polyDom_le_uniform S.G' (mc := m₀) (κdec := κdec) hN hκ hL jL yL XL X₁f
    𝒦X hj hXp hy hal hinj hcov (Y := Y) (isDj_cells_subset hN le_rfl hdj) Bτ n₁ hCI hKL hE₀ hα
    hEbI hEbL
  have hd : treeLenCov S.G' m₀ Y = treeLenCovOne m₀ (k + 1) Y :=
    treeLenCov_eq_treeLenCovOne S.hG' m₀ Y
  have hcell := cellCount_le_one_add_treeLenCovOne hN le_rfl hdj
  have hcmp : treeLenCovOne 1 (k + 1) Y ≤ A * treeLenCovOne m₀ (k + 1) Y + B :=
    treeLenCovOne_one_le_index hm1 hN le_rfl hdj
  have hdM := treeLenCovOne_nonneg (m₁ := m₁) (N₁ := N₁) (L := L) (d := d) (K := k + 1) m₀
    (k + 1) Y
  rw [hd] at hsum ⊢
  have hsum' : _ ≤ (cellCount (cellSide L m₀ m₁ (k + 1)) Y : ℝ) * Λ *
      Real.exp (-(2 * κdec * treeLenCovOne m₀ (k + 1) Y)) :=
    le_of_le_of_eq hsum (by rw [hΛ]; ring)
  have key := arith_step (c := c1 d L) (Λ := Λ) (κdec := κdec) (κH := κH) (A := A) (B := B)
    (d1 := treeLenCovOne 1 (k + 1) Y) hc10 hΛ0 hκH hrate hcell hcmp hdM hsum'
  exact key

end NumB

section NumSmall

open Classical in
/-- **The amplitude of the activity is small for large `β`.**  If the activity satisfies the
bound of `classActivityFamily_amplitude_gen` at the radius `a = δ₁ / (2 markedRad)` (so that
`r / a = 2 r markedRad / δ₁`), the sum of `hnumH` is at most `ε_C e^{-κ_H d_1(Y)}`, and
`2 r √N ‖cc‖ C_sup c_ψ ≤ η δ₁` (for `‖cc‖ = β_k^{-1/2}` this holds for `β_k` large, uniformly in `k`
and `Y`), then the activity at `‖u‖ ≤ r` is at most `η ε_C e^{-κ_H d_1(Y)}`. -/
theorem amplitude_small_of_hnumH (d L N k : ℕ) (a₁ κ cψ : ℝ) (cc : ℂ) {δ₁ r η εC κH d1 Sg h : ℝ}
    (hδ : 0 < δ₁) (hη0 : 0 ≤ η)
    (hamp : h ≤ r / (δ₁ / (2 * markedRad d L N k a₁ κ cψ cc)) * Sg)
    (hnum : Sg ≤ εC * Real.exp (-κH * d1))
    (hSg : 0 ≤ Sg)
    (hη : 2 * r * (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) ≤
      η * δ₁) :
    h ≤ η * (εC * Real.exp (-κH * d1)) := by
  rw [div_markedRad_radius_eq d L N k a₁ κ cψ cc r hδ] at hamp
  have hfac : 2 * r * (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) /
      δ₁ ≤ η := by
    rw [div_le_iff₀ hδ]; exact hη
  calc h ≤ _ := hamp
    _ ≤ η * Sg := mul_le_mul_of_nonneg_right hfac hSg
    _ ≤ _ := mul_le_mul_of_nonneg_left hnum hη0

end NumSmall

section Margin

/-- **The corner margin against `hr₀` at `L = d = 3`.**  The margin `r₀ ≤ (L - 1) L^{m₀}` of a site
in a corner of its cell of side `L^{k+1+m₀+m₁}` (`X₁` contains the `(L - 1)` cells around it)
together with `BgSetting.hr₀ : 4 d L^3 ≤ r₀` forces `m₀ ≥ 5` at `L = d = 3`: for `m₀ ≤ 4` there is
no `r₀`. -/
theorem no_corner_margin_of_le_four {r₀ : ℝ} {m₀ : ℕ} (hm : m₀ ≤ 4)
    (hr₀ : 4 * (3 : ℕ) * ((3 : ℕ) : ℝ) ^ 3 ≤ r₀) :
    ¬ r₀ ≤ (((3 : ℕ) : ℝ) - 1) * ((3 : ℕ) : ℝ) ^ m₀ := by
  intro h
  have h3 : ((3 : ℕ) : ℝ) ^ m₀ ≤ ((3 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_right₀ (by norm_num) hm
  norm_num at hr₀ h h3
  nlinarith

/-- For `m₀ = 5` the corner margin and `hr₀` are compatible at `L = d = 3` (`r₀ = 324 ≤ 486`). -/
theorem corner_margin_five : 4 * (3 : ℕ) * ((3 : ℕ) : ℝ) ^ 3 ≤
    (((3 : ℕ) : ℝ) - 1) * ((3 : ℕ) : ℝ) ^ 5 := by norm_num

end Margin

end Balaban.Fluctuation
