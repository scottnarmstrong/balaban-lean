/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.AbstractExpansion
public import Balaban.Localization.I5Expansion
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The coefficients `F_C` and the terms `𝓔(X, Y)` depend only on the germ of `F` on the polydisc

The mixed-derivative coefficient `coef F C` only involves `F` on the unit polydisc, through
derivatives; hence two functions that agree on the open polydisc `|s_i| < R`, `R > 1`, have the same
coefficients (`coef_congr_polydisc`) and the same terms (`evTerm_congr_polydisc`).  This is the
transfer principle used to show that the expansion terms inherit a symmetry of `F` that holds on the
polydisc only (the decoupled objects are characterized there only).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Analysis

section Coef

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
theorem pder_congr_open {U : Set (ι → ℂ)} (hU : IsOpen U) {f g : (ι → ℂ) → ℂ}
    (h : ∀ w ∈ U, f w = g w) (i : ι) : ∀ w ∈ U, pder i f w = pder i g w := by
  intro w hw
  unfold pder
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ) := by fun_prop
  have hmem : (fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ)) ⁻¹' U ∈ nhds (0 : ℂ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hw)
  filter_upwards [hmem] with t ht using h _ ht

omit [Fintype ι] in
theorem pderList_congr_open {U : Set (ι → ℂ)} (hU : IsOpen U) :
    ∀ (l : List ι) {f g : (ι → ℂ) → ℂ}, (∀ w ∈ U, f w = g w) →
      ∀ w ∈ U, pderList l f w = pderList l g w := by
  intro l
  induction l with
  | nil => intro f g h w hw; exact h w hw
  | cons i l ih =>
    intro f g h w hw
    exact ih (pder_congr_open hU h i) w hw

/-- **The coefficient `F_C` only depends on `F` on the open polydisc of radius `R > 1`.** -/
theorem coef_congr_polydisc {R : ℝ} (hR : 1 < R) {f g : (ι → ℂ) → ℂ}
    (h : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => R), f w = g w) (C : Finset ι) :
    coef f C = coef g C := by
  unfold coef
  refine iterInt_congr (fun w hw => ?_) _ (fun j _ => by simp)
  exact pderList_congr_open (isOpen_polydisc _ _) _ h w (unitCube_subset_polydisc hR hw)

/-- Coordinatewise complex conjugation of a vector of parameters. -/
def cjv (w : ι → ℂ) : ι → ℂ := fun j => starRingEnd ℂ (w j)

omit [Fintype ι] in
theorem cjv_add_smul (w : ι → ℂ) (t : ℂ) (i : ι) :
    cjv (w + t • (Pi.single i 1 : ι → ℂ)) = cjv w + starRingEnd ℂ t • (Pi.single i 1 : ι → ℂ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [cjv]
  · simp [cjv, Pi.single_eq_of_ne h]

omit [Fintype ι] in
/-- **Reality of `∂_i F`**: if `F (conj w) = conj (F w)` on an open set `U` that is stable under
conjugation then so is `∂_i F`. -/
theorem pder_conj {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → ℂ} (h : ∀ w ∈ U, f (cjv w) = starRingEnd ℂ (f w)) (i : ι) :
    ∀ w ∈ U, pder i f (cjv w) = starRingEnd ℂ (pder i f w) := by
  intro w hw
  unfold pder
  set g : ℂ → ℂ := fun t => f (w + t • (Pi.single i 1 : ι → ℂ)) with hg
  have hc : Continuous fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ) := by fun_prop
  have hmem : (fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ)) ⁻¹' U ∈ nhds (0 : ℂ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hw)
  have hmem' : (fun t : ℂ => w + (starRingEnd ℂ t) • (Pi.single i 1 : ι → ℂ)) ⁻¹' U ∈ nhds (0 : ℂ) :=
    (Complex.continuous_conj.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hmem))
  have e : (fun t : ℂ => f (cjv w + t • (Pi.single i 1 : ι → ℂ))) =ᶠ[nhds 0]
      (starRingEnd ℂ ∘ g ∘ starRingEnd ℂ) := by
    filter_upwards [hmem'] with t ht
    simp only [Function.comp, hg]
    have := h _ ht
    rw [cjv_add_smul, starRingEnd_self_apply] at this
    exact this
  rw [Filter.EventuallyEq.deriv_eq e]
  have := congrFun (deriv_conj_conj (f := g)) 0
  simp

omit [Fintype ι] in
theorem pderList_conj {U : Set (ι → ℂ)} (hU : IsOpen U) :
    ∀ (l : List ι) {f : (ι → ℂ) → ℂ}, (∀ w ∈ U, f (cjv w) = starRingEnd ℂ (f w)) →
      ∀ w ∈ U, pderList l f (cjv w) = starRingEnd ℂ (pderList l f w) := by
  intro l
  induction l with
  | nil => intro f h w hw; exact h w hw
  | cons i l ih =>
    intro f h w hw
    exact ih (pder_conj hU h i) w hw

omit [Fintype ι] in
theorem iterInt_conj {h : (ι → ℂ) → ℂ} (hh : ∀ w ∈ unitCube ι, h (cjv w) = starRingEnd ℂ (h w)) :
    ∀ (l : List ι) {s : ι → ℂ}, s ∈ cubeOff l → cjv s = s →
      starRingEnd ℂ (iterInt l h s) = iterInt l h s := by
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

/-- **Reality of the coefficients**: if `F (conj s) = conj (F s)` on the polydisc of radius
`R > 1` then every coefficient `F_C` is real. -/
theorem coef_conj {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (h : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => R), f (cjv w) = starRingEnd ℂ (f w))
    (C : Finset ι) : starRingEnd ℂ (coef f C) = coef f C := by
  unfold coef
  refine iterInt_conj (fun w hw => ?_) _ (fun j _ => by simp) ?_
  · exact pderList_conj (isOpen_polydisc _ _) _ h w (unitCube_subset_polydisc hR hw)
  · funext j; simp [cjv]

end Coef

section Terms

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {U U' : Type*}

/-- **The term `𝓔(X, Y)` only depends on `F` on the open polydisc of radius `R > 1`.** -/
theorem evTerm_congr_polydisc {R : ℝ} (hR : 1 < R) (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {F : U → (ι → ℂ) → ℂ} {F' : U' → (ι → ℂ) → ℂ} {u : U} {u' : U'}
    (h : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), F u s = F' u' s) :
    evTerm c G m₀ X₁ F Y u = evTerm c G m₀ X₁ F' Y u' := by
  unfold evTerm
  exact Finset.sum_congr rfl fun C _ => coef_congr_polydisc hR h C

/-- **Reality of the terms `𝓔(X, Y)`**: if `F u (conj s) = conj (F u s)` on the polydisc then
`𝓔(X, Y)(u)` is real. -/
theorem evTerm_conj {R : ℝ} (hR : 1 < R) (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {F : U → (ι → ℂ) → ℂ} {u : U}
    (h : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), F u (cjv s) = starRingEnd ℂ (F u s)) :
    starRingEnd ℂ (evTerm c G m₀ X₁ F Y u) = evTerm c G m₀ X₁ F Y u := by
  unfold evTerm
  rw [map_sum]
  exact Finset.sum_congr rfl fun C _ => coef_conj hR h C

end Terms

end Balaban.Localization
