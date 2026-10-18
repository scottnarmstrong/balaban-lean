/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedRootGeometry
public import Balaban.Fluctuation.SizeModEntropy

/-!
# Sums over the contributing pairs of a root (`StepTowerNewLevelE0Sum`)

The sums over the pairs `(b, Y)` that contribute to the marks at a root `z` (`markedIdx`), in the
form needed for the constant `B` of the class chain (WIDEGEN, W1068).  With `t(Y) = d^cov_{m₀}(Y)`
and `K₀ = K0 d L κ₀`, `κ₀ ≥ a_ent + 1`:

* `sum_exp_le_of_subset`: for every set `𝒴` of domains of contributing pairs,
  `∑_{Y ∈ 𝒴} e^{-κ₀ t(Y)} ≤ n_fibre e^{κ₀ c_Br} K₀`;
* `markedIdx_sum_exp_bridge_le`: if the pairs with the domain `Y` have total weight at most
  `c e^{-κ_G t(Y)}` (`κ₀ ≤ κ_G`), then
  `∑_{(b,Y)} g(b,Y) e^{(κ_G - κ₀) t(bridge z Y)} ≤ c n_fibre e^{κ_G c_Br} K₀`;
* `markedIdx_sum_weight_le`: `∑_{(b,Y)} ϖ(b) e^{-κ₀ t(Y)} ≤ (∑_b ϖ(b)) n_fibre e^{κ₀ c_Br} K₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale

section Sum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {β : Type*} [Fintype β]

open Classical in
/-- The domains of the contributing pairs, weighted by `e^{-κ₀ d^cov}`: at most
`n_fibre e^{κ₀ c_Br} K₀`, independently of the torus. -/
theorem sum_exp_le_of_subset (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) {κ0 : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (𝒴 : Finset (Set (CTorus d L N₁ m₁ K)))
    (h𝒴 : 𝒴 ⊆ (markedIdx reads dom z).image Prod.snd) :
    ∑ Y ∈ 𝒴, Real.exp (-κ0 * treeLenCovOne m₀ K Y) ≤
      (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0 := by
  have hκ : 0 ≤ κ0 := (add_nonneg (aEnt_nonneg d L) zero_le_one).trans hκ0
  have hmem : ∀ Y ∈ 𝒴, ∃ b, (b, Y) ∈ markedIdx reads dom z := fun Y hY => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (h𝒴 hY)
    exact ⟨q.1, hq⟩
  have hdj : ∀ Y ∈ 𝒴, IsDj m₀ K Y := fun Y hY => by
    obtain ⟨b, hb⟩ := hmem Y hY
    exact hdom b Y (mem_markedIdx.1 hb).1
  have hmaps : ∀ Y ∈ 𝒴, bridge m₀ z Y ∈ bridgeFamily m₀ reads dom z := fun Y hY => by
    obtain ⟨b, hb⟩ := hmem Y hY
    exact Finset.mem_image.2 ⟨(b, Y), hb, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ Y' ∈ bridgeFamily m₀ reads dom z, ∑ Y ∈ 𝒴.filter (fun Y => bridge m₀ z Y = Y'),
        Real.exp (-κ0 * treeLenCovOne m₀ K Y)
      ≤ ∑ Y' ∈ bridgeFamily m₀ reads dom z, (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) *
          Real.exp (-κ0 * treeLenCovOne m₀ K Y') := by
        refine Finset.sum_le_sum fun Y' _ => ?_
        have := fibre_weighted_le hN z 𝒴 hdj Y' hκ
        calc _ ≤ _ := this
          _ = _ := by ring
    _ = ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
          (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * Real.exp (-κ0 * treeLenCovOne m₀ K Y'.1) :=
        (Finset.sum_coe_sort (bridgeFamily m₀ reads dom z) fun Y' =>
          (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) *
            Real.exp (-κ0 * treeLenCovOne m₀ K Y')).symm
    _ ≤ (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0 :=
        bridgeFamily_entropy hN hL hdom z hκ0 (by positivity)

open Classical in
/-- **The marks sum at the bridged sizes.**  If the pairs `(b, Y)` with the domain `Y` have total
weight `g` at most `c e^{-κ_G d^cov(Y)}` (`κ₀ ≤ κ_G`), then the sum of `g(b, Y)` weighted by
`e^{(κ_G - κ₀) d^cov(bridge z Y)}` over the contributing pairs is at most
`c n_fibre e^{κ_G c_Br} K₀`. -/
theorem markedIdx_sum_exp_bridge_le (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) {κ0 κG c : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκG : κ0 ≤ κG) (hc : 0 ≤ c)
    (g : β × Set (CTorus d L N₁ m₁ K) → ℝ) (hg : ∀ q, 0 ≤ g q)
    (hY : ∀ Y ∈ (markedIdx reads dom z).image Prod.snd,
      ∑ q ∈ (markedIdx reads dom z).filter (fun q => q.2 = Y), g q ≤
        c * Real.exp (-κG * treeLenCovOne m₀ K Y)) :
    ∑ q ∈ markedIdx reads dom z, g q *
        Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.2)) ≤
      c * ((nFibre d L : ℝ) * Real.exp (κG * cBr d L)) * K0 d L κ0 := by
  have hκ'0 : 0 ≤ κG - κ0 := sub_nonneg.2 hκG
  have hdj : ∀ q ∈ markedIdx reads dom z, IsDj m₀ K q.2 := fun q hq =>
    hdom q.1 q.2 (mem_markedIdx.1 hq).1
  have hstep : ∀ q ∈ markedIdx reads dom z, g q *
      Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.2)) ≤
      g q * (Real.exp ((κG - κ0) * cBr d L) *
        Real.exp ((κG - κ0) * treeLenCovOne m₀ K q.2)) := fun q hq => by
    refine mul_le_mul_of_nonneg_left ?_ (hg q)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := treeLenCovOne_bridge_le hN z (hdj q hq)
    nlinarith
  have hmaps : ∀ q ∈ markedIdx reads dom z, q.2 ∈ (markedIdx reads dom z).image Prod.snd :=
    fun q hq => Finset.mem_image.2 ⟨q, hq, rfl⟩
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ Y ∈ (markedIdx reads dom z).image Prod.snd,
      ∑ q ∈ (markedIdx reads dom z).filter (fun q => q.2 = Y), g q *
        (Real.exp ((κG - κ0) * cBr d L) * Real.exp ((κG - κ0) * treeLenCovOne m₀ K q.2)) ≤
      c * Real.exp ((κG - κ0) * cBr d L) * Real.exp (-κ0 * treeLenCovOne m₀ K Y) := by
    intro Y hYm
    have h1 : ∑ q ∈ (markedIdx reads dom z).filter (fun q => q.2 = Y), g q *
        (Real.exp ((κG - κ0) * cBr d L) * Real.exp ((κG - κ0) * treeLenCovOne m₀ K q.2)) =
        (∑ q ∈ (markedIdx reads dom z).filter (fun q => q.2 = Y), g q) *
          (Real.exp ((κG - κ0) * cBr d L) * Real.exp ((κG - κ0) * treeLenCovOne m₀ K Y)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [(Finset.mem_filter.1 hq).2]
    rw [h1]
    calc _ ≤ (c * Real.exp (-κG * treeLenCovOne m₀ K Y)) *
          (Real.exp ((κG - κ0) * cBr d L) * Real.exp ((κG - κ0) * treeLenCovOne m₀ K Y)) :=
          mul_le_mul_of_nonneg_right (hY Y hYm) (by positivity)
      _ = c * Real.exp ((κG - κ0) * cBr d L) * (Real.exp (-κG * treeLenCovOne m₀ K Y) *
          Real.exp ((κG - κ0) * treeLenCovOne m₀ K Y)) := by ring
      _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have := sum_exp_le_of_subset hN hL reads dom hdom z hκ0 _ (subset_refl
    ((markedIdx reads dom z).image Prod.snd))
  calc c * Real.exp ((κG - κ0) * cBr d L) * ∑ Y ∈ (markedIdx reads dom z).image Prod.snd,
        Real.exp (-κ0 * treeLenCovOne m₀ K Y)
      ≤ c * Real.exp ((κG - κ0) * cBr d L) * ((nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) *
        K0 d L κ0) := mul_le_mul_of_nonneg_left this (by positivity)
    _ = c * ((nFibre d L : ℝ) * Real.exp (κG * cBr d L)) * K0 d L κ0 := by
        have : Real.exp (κG * cBr d L) = Real.exp ((κG - κ0) * cBr d L) *
            Real.exp (κ0 * cBr d L) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring

open Classical in
/-- **The padding sum.**  For nonnegative weights `ϖ(b)`,
`∑_{(b,Y)} ϖ(b) e^{-κ₀ d^cov(Y)} ≤ (∑_b ϖ(b)) n_fibre e^{κ₀ c_Br} K₀`. -/
theorem markedIdx_sum_weight_le (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) {κ0 : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (ϖ : β → ℝ) (hϖ : ∀ b, 0 ≤ ϖ b) :
    ∑ q ∈ markedIdx reads dom z, ϖ q.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.2) ≤
      (∑ b, ϖ b) * ((nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0) := by
  have hmaps : ∀ q ∈ markedIdx reads dom z, q.1 ∈ (Finset.univ : Finset β) :=
    fun q _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 : ∑ q ∈ (markedIdx reads dom z).filter (fun q => q.1 = b),
      ϖ q.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.2) =
      ϖ b * ∑ q ∈ (markedIdx reads dom z).filter (fun q => q.1 = b),
        Real.exp (-κ0 * treeLenCovOne m₀ K q.2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [(Finset.mem_filter.1 hq).2]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (hϖ b)
  have hinj : Set.InjOn (Prod.snd : β × Set (CTorus d L N₁ m₁ K) → _)
      ↑((markedIdx reads dom z).filter (fun q => q.1 = b)) := fun q hq q' hq' h => by
    have h1 := (Finset.mem_filter.1 hq).2
    have h2 := (Finset.mem_filter.1 hq').2
    exact Prod.ext (h1.trans h2.symm) h
  rw [← Finset.sum_image (f := fun Y => Real.exp (-κ0 * treeLenCovOne m₀ K Y))
    (g := Prod.snd) hinj]
  exact sum_exp_le_of_subset hN hL reads dom hdom z hκ0 _ (fun Y hY => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hY
    exact Finset.mem_image.2 ⟨q, (Finset.mem_filter.1 hq).1, rfl⟩)

end Sum

end Balaban.Fluctuation
