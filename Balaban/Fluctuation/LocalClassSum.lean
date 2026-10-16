/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassExtend
public import Balaban.Fluctuation.Prop33Bound
public import Balaban.Fluctuation.Prop33Count
public import Balaban.Fluctuation.SizeModG1
public import Balaban.SmallField.Def6BridgeGeom

/-!
# The clause `boundE` of the local class: the sum over the old labels

The term of a polymer `Y` of level `k + 1` of the local class collects, over the labels `τ` of the
old terms (scale `j_τ`, polymer `X_τ`, root `r_τ`), the terms `𝓔_τ(Y)` of the localization
expansion recomputed on `𝔹_{k+1}(Y⁺)` (P3 (4.46)-(4.47)), each extended to all pairs of fields by
the completion of `LocalClassExtend.lean`.  The bound of one label is
`Eb_τ γ(K) e^{-κ₀ d_{j_τ}(X_τ) - 2 κ_dec d̃^cov(Y)}` (`localB_eTermHat_evTerm_ext`, clause 4).  The sum
is resummed as in Proposition 3.3 (`interaction_expansion_bound`, FLUCTUATION (3.5)):

* `evTerm_eq_zero_of_not_subset`: the term `𝓔(X, Y)` vanishes unless `Y ⊇ X₁` (every domain
  `Y[𝒞]` of a connected family contains `X₁`), so a label contributes only if its root lies in `Y`;
* `norm_sum_rooted_le_boundE`: for terms bounded by `Eb_τ γ e^{-κ₀ d_{j_τ}(X_τ) - 2 κ_dec d̃^cov(Y)}`
  and vanishing unless the root lies in `Y`, with per-site sums of `Eb_τ e^{-κ₀ d_{j_τ}(X_τ)}` at
  most `ρ_E` (`classE_siteSum_le` for the labels of a class) and a generating set of level `lev`
  (so `d̃^cov = d^cov_{lev}`), the sum is at most `E₀ e^{-κ d_{lev}(Y)}` for
  `γ ρ_E c₁ (L^{lev} M)^d ≤ E₀`, `M = L^{m₀ + m₁}`, and `κ ≤ 2 κ_dec - 1`.  The count is
  `|Y| ≤ c₁ (L^{lev} M)^d (1 + d_{lev}(Y))` for `Y ∈ 𝒟_{lev}` ((G1), `G1_card`), and
  `(1 + t) e^{-2 κ_dec t} ≤ e^{-(2 κ_dec - 1) t}`;
* `norm_sum_evTerm_le_boundE`: the same for the terms `𝓔_τ(Y) = evTerm … (X₁(τ)) (F τ) Y` with
  roots in `X₁(τ)`, at any argument; with the argument `clipRaw 𝔹 (cpl (Ψ, h))` and the per-label
  bound of `localB_eTermHat_evTerm_ext` this is the clause `boundE` of the sum of the extended terms.

The prefactor `E₀` contains the volume `(L^{k+1} M)^d` of a `(k+1)`-cube times the per-site sum
`ρ_E`, as the amplitude `prop33Eps` of the ambient step.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Finset

section Vanish

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {c : ι → ℕ × CTorus d L N₁ m₁ K} {U : Type*}

/-- **A term `𝓔(X, Y)` vanishes unless `X₁ ⊆ Y`**: the domain `Y[𝒞]` of every connected family
contains `X₁`. -/
theorem evTerm_eq_zero_of_not_subset {X₁ Y : Set (CTorus d L N₁ m₁ K)} (hXY : ¬ X₁ ⊆ Y)
    (F : U → (ι → ℂ) → ℂ) (u : U) : evTerm c G m₀ X₁ F Y u = 0 := by
  unfold evTerm
  refine Finset.sum_eq_zero fun C hC => absurd ?_ hXY
  obtain ⟨-, hY⟩ := (mem_connFams c).1 hC
  rw [← hY]
  exact subset_Ysites X₁ C

end Vanish

section Sum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱa : ℝ}

/-- **The sum over rooted labels in the form of the clause `boundE`.**  Terms `T_τ` bounded by
`Eb_τ γ e^{-κ₀ d_{j_τ}(X_τ) - 2 κ_dec d̃^cov(Y)}` and vanishing unless their root lies in `Y`, with
per-site sums of `Eb_τ e^{-κ₀ d_{j_τ}(X_τ)}` at most `ρ_E`, add up to at most `E₀ e^{-κ d_{lev}(Y)}`
for `Y ∈ 𝒟_{lev}`, a generating set of level `lev`, `γ ρ_E c₁ (L^{lev} L^{m₀ + m₁})^d ≤ E₀` and
`κ ≤ 2 κ_dec - 1`. -/
theorem norm_sum_rooted_le_boundE {τι U : Type*} [DecidableEq τι] (𝒯E : Finset τι)
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) K ϱa} {lev m₀ : ℕ} (hGa : IsLevel Ga lev)
    (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPolyDom m₀ lev Y)
    (rE : τι → CTorus d L N₁ m₁ K) (jE : τι → ℕ) (XE : τι → Set (CTorus d L N₁ m₁ K))
    (EbE : τι → ℝ) (hEb0 : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {κ₀ ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ K, ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {γ κdec κ E₀ : ℝ} (hγ : 0 ≤ γ) (hκ : κ ≤ 2 * κdec - 1)
    (hE₀ : γ * ρE * c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d ≤ E₀)
    (T : τι → U → ℂ) (u : U)
    (hT : ∀ τ ∈ 𝒯E, ‖T τ u‖ ≤ EbE τ * γ *
      Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) - 2 * κdec * treeLenCov Ga m₀ Y))
    (hT0 : ∀ τ ∈ 𝒯E, rE τ ∉ Y → T τ u = 0) :
    ‖∑ τ ∈ 𝒯E, T τ u‖ ≤ E₀ * Real.exp (-κ * sizeJ m₀ lev Y) := by
  classical
  set t := treeLenCovOne m₀ lev Y with ht
  have ht0 : 0 ≤ t := treeLenCovOne_nonneg _ _ _
  have hconv : treeLenCov Ga m₀ Y = t := treeLenCov_eq_treeLenCovOne hGa m₀ Y
  set w : τι → ℝ := fun τ => EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) with hw
  have hw0 : ∀ τ ∈ 𝒯E, 0 ≤ w τ := fun τ hτ => mul_nonneg (hEb0 τ hτ) (Real.exp_pos _).le
  have hs := sum_roots_le 𝒯E w hw0 rE Y hρE
  have hnc : (Y.ncard : ℝ) ≤ c1 d L * ((cellSide L m₀ m₁ lev : ℕ) : ℝ) ^ d * (1 + t) :=
    G1_card hN hGa.bounds.2 (isDj_of_isPolyDom hY)
  have hcell : ((cellSide L m₀ m₁ lev : ℕ) : ℝ) ^ d =
      ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by
    unfold cellSide
    push_cast
    rw [← mul_pow, ← pow_add]
    congr 2
    ring
  have hq : 0 ≤ γ * Real.exp (-2 * κdec * t) := mul_nonneg hγ (Real.exp_pos _).le
  have e1 : ∀ τ ∈ 𝒯E, ‖T τ u‖ ≤ (if rE τ ∈ Y then w τ else 0) * (γ * Real.exp (-2 * κdec * t)) := by
    intro τ hτ
    by_cases hin : rE τ ∈ Y
    · simp only [hin, ite_true, hw]
      refine (hT τ hτ).trans (le_of_eq ?_)
      rw [hconv, sub_eq_add_neg, Real.exp_add]
      ring_nf
    · simp only [hin, ite_false, zero_mul, hT0 τ hτ hin, norm_zero, le_refl]
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  calc ‖∑ τ ∈ 𝒯E, T τ u‖ ≤ ∑ τ ∈ 𝒯E, ‖T τ u‖ := norm_sum_le _ _
    _ ≤ ∑ τ ∈ 𝒯E, (if rE τ ∈ Y then w τ else 0) * (γ * Real.exp (-2 * κdec * t)) :=
        Finset.sum_le_sum e1
    _ = (∑ τ ∈ 𝒯E, (if rE τ ∈ Y then w τ else 0)) * (γ * Real.exp (-2 * κdec * t)) := by
        rw [Finset.sum_mul]
    _ ≤ (ρE * (c1 d L * (((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d) * (1 + t))) *
          (γ * Real.exp (-2 * κdec * t)) := by
        refine mul_le_mul_of_nonneg_right (hs.trans ?_) hq
        rw [← hcell]
        exact mul_le_mul_of_nonneg_left hnc hρE0
    _ = (γ * ρE * c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((1 + t) * Real.exp (-2 * κdec * t)) := by ring
    _ ≤ (γ * ρE * c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          Real.exp (-κ * t) := by
        refine mul_le_mul_of_nonneg_left ((one_add_mul_exp_le t κdec).trans ?_) (by positivity)
        exact Real.exp_le_exp.2 (by nlinarith)
    _ ≤ E₀ * Real.exp (-κ * sizeJ m₀ lev Y) :=
        mul_le_mul_of_nonneg_right hE₀ (Real.exp_pos _).le

/-- **The clause `boundE` for a sum of terms of the localization expansion over old labels**: the
terms `evTerm … (X₁(τ)) (F τ) Y u` with roots `r_τ ∈ X₁(τ)` (they vanish unless `r_τ ∈ Y`,
`evTerm_eq_zero_of_not_subset`), at any argument `u` at which each satisfies the per-label bound. -/
theorem norm_sum_evTerm_le_boundE {τι ι U : Type*} [DecidableEq τι] [DecidableEq ι] [Fintype ι]
    (cI : ι → ℕ × CTorus d L N₁ m₁ K) (𝒯E : Finset τι)
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) K ϱa} {lev m₀ : ℕ} (hGa : IsLevel Ga lev)
    (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPolyDom m₀ lev Y)
    (rE : τι → CTorus d L N₁ m₁ K) (jE : τι → ℕ) (XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ K))
    (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X1 Ga m₀ (jE τ) (𝒦XE τ))
    (EbE : τι → ℝ) (hEb0 : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {κ₀ ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ K, ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {γ κdec κ E₀ : ℝ} (hγ : 0 ≤ γ) (hκ : κ ≤ 2 * κdec - 1)
    (hE₀ : γ * ρE * c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d ≤ E₀)
    (F : τι → U → (ι → ℂ) → ℂ) (u : U)
    (hT : ∀ τ ∈ 𝒯E, ‖evTerm cI Ga m₀ (X1 Ga m₀ (jE τ) (𝒦XE τ)) (F τ) Y u‖ ≤ EbE τ * γ *
      Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) - 2 * κdec * treeLenCov Ga m₀ Y)) :
    ‖∑ τ ∈ 𝒯E, evTerm cI Ga m₀ (X1 Ga m₀ (jE τ) (𝒦XE τ)) (F τ) Y u‖ ≤
      E₀ * Real.exp (-κ * sizeJ m₀ lev Y) :=
  norm_sum_rooted_le_boundE 𝒯E hGa hN hY rE jE XE EbE hEb0 hρE0 hρE hγ hκ hE₀
    (fun τ u => evTerm cI Ga m₀ (X1 Ga m₀ (jE τ) (𝒦XE τ)) (F τ) Y u) u hT
    (fun τ hτ hn => evTerm_eq_zero_of_not_subset (fun h => hn (h (hrE τ hτ))) _ _)

end Sum

end Balaban.Localization
