/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyNumA
public import Balaban.Fluctuation.HatPolyDom

/-!
# `hnumH` for labels whose support polymers repeat (`LocalClassDensityIrrelCount`)

`classActivity_hnumH_of_uniform_gen` counts labels `τ = (j, y, X)` whose triples
`(j_τ, y_τ, X_τ)` are pairwise different.  For the irrelevant parts the support of the label
functional is `X^⋆ = X ∪ st₊(y)` enlarged to a polymer, and a polymer can be the support of at most
`mult` different labels.  `classActivity_hnumH_of_uniform_mult` is the same bound multiplied by
`mult`: the labels are split into `mult` classes of pairwise different triples by their rank in
the fibre of the triple (`rank_lt`, `rank_injective`), and the injective count is applied to each
class.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Polymer Finset

section Rank

variable {ι : Type*} [Fintype ι] {γ : Type*} [DecidableEq γ]

open Classical in
/-- The rank of a label in the fibre of its triple, for the enumeration of `ι`. -/
noncomputable def fibreRank (tr : ι → γ) (τ : ι) : ℕ :=
  (Finset.univ.filter fun τ' => tr τ' = tr τ ∧ Fintype.equivFin ι τ' < Fintype.equivFin ι τ).card

open Classical in
theorem fibreRank_lt {tr : ι → γ} {mult : ℕ}
    (hmult : ∀ τ, (Finset.univ.filter fun τ' => tr τ' = tr τ).card ≤ mult) (τ : ι) :
    fibreRank tr τ < mult := by
  refine lt_of_lt_of_le (Finset.card_lt_card ?_) (hmult τ)
  refine ⟨fun τ' h => ?_, fun h => ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.1⟩
  · have := Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨Finset.mem_univ τ, rfl⟩))
    exact lt_irrefl _ this.2.2

open Classical in
theorem fibreRank_injective {tr : ι → γ} {τ τ' : ι} (h : tr τ = tr τ')
    (hr : fibreRank tr τ = fibreRank tr τ') : τ = τ' := by
  by_contra hne
  have hne' : Fintype.equivFin ι τ ≠ Fintype.equivFin ι τ' := fun e => hne ((Fintype.equivFin ι).injective e)
  have key : ∀ a b : ι, tr a = tr b → Fintype.equivFin ι a < Fintype.equivFin ι b →
      fibreRank tr a < fibreRank tr b := by
    intro a b hab hlt
    refine Finset.card_lt_card ⟨fun c hc => ?_, fun hs => ?_⟩
    · obtain ⟨-, hc1, hc2⟩ := Finset.mem_filter.1 hc
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hc1.trans hab, hc2.trans hlt⟩
    · obtain ⟨-, -, h3⟩ := Finset.mem_filter.1 (hs (Finset.mem_filter.2
        ⟨Finset.mem_univ a, hab, hlt⟩))
      exact lt_irrefl _ h3
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact absurd hr (key τ τ' h hlt).ne
  · exact absurd hr (key τ' τ h.symm hlt).ne'

end Rank

section Count

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)

open Classical in
/-- **`hnumH` when a support polymer repeats at most `mult` times.**  As
`classActivity_hnumH_of_uniform_gen`, without the injectivity of the triples
`(j_τ, y_τ, X_τ)` but with at most `mult` labels with the same triple; the bound is multiplied by
`mult`. -/
theorem classActivity_hnumH_of_uniform_mult {ι : Type*} [Fintype ι] {m₀ : ℕ}
    (hm1 : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {κ₀ κdec κH : ℝ}
    (hκ : aEnt d L + 1 ≤ κ₀) (hκH : 0 ≤ κH)
    (hrate : κH * ((L : ℝ) ^ (m₀ - 1) + 2 * d * (L : ℝ) ^ m₀ *
      (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj : ∀ τ, 1 ≤ jL τ ∧ jL τ ≤ k) (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ) (hal : ∀ τ, Aligned (L ^ jL τ) (yL τ)) (mult : ℕ)
    (hmult : ∀ τ, (Finset.univ.filter fun τ' =>
      jL τ' = jL τ ∧ yL τ' = yL τ ∧ XL τ' = XL τ).card ≤ mult)
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
      else 0) ≤ mult * (c1 d L * ((((L : ℝ) ^ (1 + m₀ + m₁)) ^ d) * E₀ *
        (2 * K0 d L κ₀ * (CI * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d)))) *
        Real.exp (κH * (2 * d * (L : ℝ) ^ m₀ * (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L))) *
        Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
  intro Y hY
  set tr : ι → ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)) :=
    fun τ => (jL τ, yL τ, XL τ) with htr
  have hmult' : ∀ τ, (Finset.univ.filter fun τ' => tr τ' = tr τ).card ≤ mult := fun τ => by
    refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun τ' _ => ?_))) (hmult τ)
    simp only [htr, Prod.mk.injEq]
  set R : ℝ := (c1 d L * ((((L : ℝ) ^ (1 + m₀ + m₁)) ^ d) * E₀ *
        (2 * K0 d L κ₀ * (CI * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
          n₁ * KL * (((L : ℝ) ^ (n₁ - 1)) ^ d)))) *
        Real.exp (κH * (2 * d * (L : ℝ) ^ m₀ * (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L))) *
        Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) with hR
  set f : ι → ℝ := fun τ => if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y)
      else 0 with hf
  have hmaps : ∀ τ ∈ (Finset.univ : Finset ι), fibreRank tr τ ∈ Finset.range mult :=
    fun τ _ => Finset.mem_range.2 (fibreRank_lt hmult' τ)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hcls : ∀ i ∈ Finset.range mult,
      ∑ τ ∈ Finset.univ.filter (fun τ => fibreRank tr τ = i), f τ ≤ R := by
    intro i _
    rw [Finset.sum_subtype (Finset.univ.filter (fun τ => fibreRank tr τ = i))
      (p := fun τ => fibreRank tr τ = i) (fun τ => by simp) f]
    exact classActivity_hnumH_of_uniform_gen S hm1 hN hL hκ hκH hrate
      (fun τ : {τ // fibreRank tr τ = i} => jL τ.1) (fun τ => yL τ.1) (fun τ => XL τ.1)
      (fun τ => X₁f τ.1) (fun τ => 𝒦X τ.1) (fun τ => hj τ.1) (fun τ => hXp τ.1)
      (fun τ => hy τ.1) (fun τ => hal τ.1)
      (fun τ τ' h1 h2 h3 => Subtype.ext (fibreRank_injective
        (by simp only [htr, h1, h2, h3]) (τ.2.trans τ'.2.symm)))
      (fun τ => hcov τ.1) 𝒴C h𝒴dj (fun τ => Bτ τ.1) n₁ hCI hKL hE₀ hα
      (fun τ => hEbI τ.1) (fun τ => hEbL τ.1) Y hY
  calc _ ≤ ∑ i ∈ Finset.range mult, R := Finset.sum_le_sum hcls
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hR]; ring

end Count

end Balaban.Fluctuation
