/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivRelabel
public import Balaban.Localization.I5Param
public import Balaban.Polymer.TwoTorusDet
public import Balaban.Polymer.TwoTorusLift
public import Balaban.Polymer.TwoTorusDomainFamilies
public import Balaban.Fluctuation.MarkedVRawY
public import Balaban.Fluctuation.MarkedFanAnalytic
public import Balaban.Fluctuation.MarkedVBlockDec
public import Balaban.Fluctuation.MarkedFluctRows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked energy coefficients on two tori

## D1: the coefficients under a partial relabelling of the parameters

* `eq_of_sum_powerset_eq_of_subset`: a function on the subsets of a finite set `C` is determined
  by its sums over the powersets of the subsets of `C`.
* `coef_relabel_injOn`: if `e : ι → ι'` is injective on a finite family `C` of parameters and
  `f' (s') = f (s)` whenever `s` vanishes off `C` with `|s_i| < R` and `s'` vanishes off `e C`
  with `s' (e i) = s i` on `C`, then `coef f' (e C) = coef f C` (`f` analytic on the polydisc of
  radius `R > 1`).  This is `coef_relabel` for a map that is a bijection only between `C` and its
  image; the values of `f` and `f'` off the cut points `supN C R` are not compared.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis

/-! ### D1: the coefficients under a partial relabelling -/

section Relabel

variable {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']

omit [Fintype ι] in
/-- A function on the subsets of a finite set `C` is determined by its sums over the powersets of
the subsets of `C` (`eq_of_sum_powerset_eq` restricted to the subsets of `C`). -/
theorem eq_of_sum_powerset_eq_of_subset {g h : Finset ι → ℂ} {C : Finset ι}
    (hgh : ∀ A ⊆ C, ∑ B ∈ A.powerset, g B = ∑ B ∈ A.powerset, h B) :
    ∀ A ⊆ C, g A = h A := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hAC
    have e := hgh A hAC
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self A),
      ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self A)] at e
    have : ∑ B ∈ A.powerset.erase A, g B = ∑ B ∈ A.powerset.erase A, h B :=
      Finset.sum_congr rfl fun B hB => by
        obtain ⟨hne, hsub⟩ := Finset.mem_erase.1 hB
        have hBA := Finset.mem_powerset.1 hsub
        exact ih B (Finset.ssubset_iff_subset_ne.2 ⟨hBA, hne⟩) (hBA.trans hAC)
    rw [this] at e
    exact add_right_cancel e

/-- **D1: the coefficients under a relabelling that is a bijection between `C` and its image.**
Let `e : ι → ι'` be injective on the finite family `C`, `f` analytic on the polydisc of radius
`R > 1`, and assume `f' (s') = f (s)` for every `s` vanishing off `C` with `|s_i| < R` and every
`s'` vanishing off `e C` with `s' (e i) = s i` for `i ∈ C`.  Then `coef f' (e C) = coef f C`.
Proof: `coef f' (e C)` reads `f'` only on `supN (e C) R` (`coef_congr_near`), where `f'` is the
analytic function `g = f ∘ e^*`, `e^* w = (i ↦ 1_C(i) w (e i))`; the coefficients of `g` on the
subsets of `e C` and of `f` on the subsets of `C` have the same sums over powersets (the values at
the indicator points, `sum_coef_unit`), hence agree (`eq_of_sum_powerset_eq_of_subset`). -/
theorem coef_relabel_injOn {R : ℝ} (hR : 1 < R) (e : ι → ι') {C : Finset ι}
    (he : Set.InjOn e C) {f : (ι → ℂ) → ℂ} {f' : (ι' → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hff : ∀ s ∈ supN C R, ∀ s' : ι' → ℂ, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → f' s' = f s) :
    coef f' (C.image e) = coef f C := by
  classical
  have hR0 : 0 < R := by linarith
  -- the pull-back of the parameters
  set pb : (ι' → ℂ) → (ι → ℂ) := fun w i => if i ∈ C then w (e i) else 0 with hpb
  set g : (ι' → ℂ) → ℂ := fun w => f (pb w) with hg
  have h1 : coef f' (C.image e) = coef g (C.image e) := by
    refine coef_congr_near hR fun w hw => ?_
    refine hff (pb w) ⟨fun i hi => by simp [hpb, hi], fun i => ?_⟩ w hw.1
      (fun i hi => by simp [hpb, hi])
    by_cases hi : i ∈ C
    · simp only [hpb, hi, ↓reduceIte]; exact hw.2 _
    · simp only [hpb, hi, ↓reduceIte, norm_zero]; exact hR0
  rw [h1]
  -- `g` is analytic on the polydisc
  have hpbA : ∀ w, AnalyticAt ℂ pb w := by
    intro w
    rw [analyticAt_pi_iff]
    intro i
    by_cases hi : i ∈ C
    · have : (fun w : ι' → ℂ => pb w i) = fun w => w (e i) := by
        funext w; simp [hpb, hi]
      rw [this]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι' => ℂ) (e i)).analyticAt w
    · have : (fun w : ι' → ℂ => pb w i) = fun _ => 0 := by
        funext w; simp [hpb, hi]
      rw [this]
      exact analyticAt_const
  have hpbP : ∀ w ∈ polydisc (0 : ι' → ℂ) (fun _ => R), pb w ∈ polydisc (0 : ι → ℂ) (fun _ => R) := by
    intro w hw i
    by_cases hi : i ∈ C
    · simpa [hpb, hi] using hw (e i)
    · simpa [hpb, hi] using hR0
  have hgA : AnalyticOnNhd ℂ g (polydisc (0 : ι' → ℂ) (fun _ => R)) := fun w hw =>
    (hf (pb w) (hpbP w hw)).comp (hpbA w)
  -- the indicator points
  have key : ∀ A ⊆ C, g (indic (A.image e)) = f (indic A) := by
    intro A hAC
    simp only [hg]
    congr 1
    funext i
    by_cases hi : i ∈ C
    · have hiff : e i ∈ A.image e ↔ i ∈ A := by
        constructor
        · intro h
          obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 h
          have := he (Finset.mem_coe.2 (hAC ha)) (Finset.mem_coe.2 hi) hae
          exact this ▸ ha
        · intro h; exact Finset.mem_image_of_mem e h
      simp only [hpb, hi, ↓reduceIte, indic, hiff]
    · have hiA : i ∉ A := fun h => hi (hAC h)
      simp [hpb, hi, indic, hiA]
  have hsum : ∀ A ⊆ C, ∑ B ∈ A.powerset, coef g (B.image e) =
      ∑ B ∈ A.powerset, coef f B := by
    intro A hAC
    have e1 : ∑ B ∈ A.powerset, coef g (B.image e) =
        ∑ B' ∈ (A.image e).powerset, coef g B' := by
      refine Finset.sum_nbij' (fun B => B.image e) (fun B' => A.filter fun i => e i ∈ B')
        (fun B hB => ?_) (fun B' hB' => ?_) (fun B hB => ?_) (fun B' hB' => ?_) (fun B _ => rfl)
      · exact Finset.mem_powerset.2 (Finset.image_subset_image (Finset.mem_powerset.1 hB))
      · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
      · have hBA := Finset.mem_powerset.1 (Finset.mem_coe.1 hB)
        ext i
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hiA, b, hb, hbe⟩
          have := he (Finset.mem_coe.2 (hAC (hBA hb))) (Finset.mem_coe.2 (hAC hiA)) hbe
          exact this ▸ hb
        · intro hi
          exact ⟨hBA hi, i, hi, rfl⟩
      · have hB'A := Finset.mem_powerset.1 (Finset.mem_coe.1 hB')
        ext j
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨-, hi⟩, rfl⟩; exact hi
        · intro hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hB'A hj)
          exact ⟨i, ⟨hi, hj⟩, rfl⟩
    rw [e1, ← sum_coef_unit hR hgA, ← sum_coef_unit hR hf, key A hAC]
  exact eq_of_sum_powerset_eq_of_subset hsum C subset_rfl

end Relabel

end Balaban.Polymer.TwoTorusStep
