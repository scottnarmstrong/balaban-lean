/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivCoef
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugation of the coefficients between two functions

`DecEquivCoef.evTerm_conj` states: if `F u (conj s) = conj (F u s)` then `𝓔(X, Y)(u)` is real.
Here the two-function version: if `F' u' (conj s) = conj (F u s)` on the polydisc then
`conj 𝓔(X, Y)[F](u) = 𝓔(X, Y)[F'](u')` (`evTerm_conj_two`).  It is used with
`u' = (Θ, conj ψ')`, which gives the reality of the terms for complex fluctuations `ψ'` and real `Θ`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Analysis

section Coef2

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
theorem pder_conj_two {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f g : (ι → ℂ) → ℂ} (h : ∀ w ∈ U, g (cjv w) = starRingEnd ℂ (f w)) (i : ι) :
    ∀ w ∈ U, pder i g (cjv w) = starRingEnd ℂ (pder i f w) := by
  intro w hw
  unfold pder
  set G : ℂ → ℂ := fun t => f (w + t • (Pi.single i 1 : ι → ℂ)) with hG
  have hc : Continuous fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ) := by fun_prop
  have hmem : (fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ)) ⁻¹' U ∈ nhds (0 : ℂ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hw)
  have hmem' : (fun t : ℂ => w + (starRingEnd ℂ t) • (Pi.single i 1 : ι → ℂ)) ⁻¹' U ∈ nhds (0 : ℂ) :=
    (Complex.continuous_conj.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hmem))
  have e : (fun t : ℂ => g (cjv w + t • (Pi.single i 1 : ι → ℂ))) =ᶠ[nhds 0]
      (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) := by
    filter_upwards [hmem'] with t ht
    simp only [Function.comp, hG]
    have := h _ ht
    rw [cjv_add_smul, starRingEnd_self_apply] at this
    exact this
  rw [Filter.EventuallyEq.deriv_eq e]
  have := congrFun (deriv_conj_conj (f := G)) 0
  simp

omit [Fintype ι] in
theorem pderList_conj_two {U : Set (ι → ℂ)} (hU : IsOpen U) :
    ∀ (l : List ι) {f g : (ι → ℂ) → ℂ}, (∀ w ∈ U, g (cjv w) = starRingEnd ℂ (f w)) →
      ∀ w ∈ U, pderList l g (cjv w) = starRingEnd ℂ (pderList l f w) := by
  intro l
  induction l with
  | nil => intro f g h w hw; exact h w hw
  | cons i l ih =>
    intro f g h w hw
    exact ih (pder_conj_two hU h i) w hw

omit [Fintype ι] in
theorem iterInt_conj_two {h h' : (ι → ℂ) → ℂ}
    (hh : ∀ w ∈ unitCube ι, h' (cjv w) = starRingEnd ℂ (h w)) :
    ∀ (l : List ι) {s : ι → ℂ}, s ∈ cubeOff l → cjv s = s →
      starRingEnd ℂ (iterInt l h s) = iterInt l h' s := by
  intro l
  induction l with
  | nil =>
    intro s hs hcs
    have := hh s (fun j => hs j (by simp))
    rw [hcs] at this
    exact this.symm
  | cons i l ih =>
    intro s hs hcs
    simp only [iterInt]
    calc starRingEnd ℂ (∫ t in (0 : ℝ)..1, iterInt l h (Function.update s i (t : ℂ)))
        = ∫ t in (0 : ℝ)..1, starRingEnd ℂ (iterInt l h (Function.update s i (t : ℂ))) := by
          rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
            integral_conj]
      _ = _ := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          refine ih (update_mem_cubeOff hs ht) ?_
          funext j
          by_cases hj : j = i
          · subst hj; simp [cjv]
          · simpa [cjv, Function.update_of_ne hj] using congrFun hcs j

/-- **Conjugation of the coefficients between two functions.** -/
theorem coef_conj_two {R : ℝ} (hR : 1 < R) {f g : (ι → ℂ) → ℂ}
    (h : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => R), g (cjv w) = starRingEnd ℂ (f w))
    (C : Finset ι) : starRingEnd ℂ (coef f C) = coef g C := by
  unfold coef
  refine iterInt_conj_two (fun w hw => ?_) _ (fun j _ => by simp) ?_
  · exact pderList_conj_two (isOpen_polydisc _ _) _ h w (unitCube_subset_polydisc hR hw)
  · funext j; simp [cjv]

end Coef2

section Terms2

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {U U' : Type*}

/-- **Conjugation of the terms `𝓔(X, Y)` between two functions.** -/
theorem evTerm_conj_two {R : ℝ} (hR : 1 < R) (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {F : U → (ι → ℂ) → ℂ} {F' : U' → (ι → ℂ) → ℂ} {u : U} {u' : U'}
    (h : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), F' u' (cjv s) = starRingEnd ℂ (F u s)) :
    starRingEnd ℂ (evTerm c G m₀ X₁ F Y u) = evTerm c G m₀ X₁ F' Y u' := by
  unfold evTerm
  rw [map_sum]
  exact Finset.sum_congr rfl fun C _ => coef_conj_two hR h C

end Terms2

end Balaban.Localization
