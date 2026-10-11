/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.Cauchy

/-!
# Iterated coordinate derivatives on a polydisc

For `f : (ι → ℂ) → ℂ`, `pder i f` is the complex derivative along the `i`-th coordinate, defined
as the derivative of a line (so that it is insensitive to values of `f` off the line), and
`pderList l f` applies `pder` for the entries of `l` in turn.  The main result is the Cauchy
estimate for the mixed derivative in distinct coordinates: on a polydisc `polydisc c r`
on which `f` is analytic and bounded by `M`,
`‖∂_{l} f (w)‖ ≤ M / ∏_{i ∈ l} (r i - ‖w i - c i‖)` (`norm_pderList_le`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate derivative `∂_i f`, as the derivative of the line `t ↦ f (s + t e_i)`. -/
noncomputable def pder (i : ι) (f : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  fun s => deriv (fun t : ℂ => f (s + t • (Pi.single i 1 : ι → ℂ))) 0

/-- Iterated coordinate derivatives: the head of the list is differentiated first. -/
noncomputable def pderList : List ι → ((ι → ℂ) → ℂ) → ((ι → ℂ) → ℂ)
  | [], f => f
  | i :: l, f => pderList l (pder i f)

@[simp] theorem pderList_nil (f : (ι → ℂ) → ℂ) : pderList [] f = f := rfl

@[simp] theorem pderList_cons (i : ι) (l : List ι) (f : (ι → ℂ) → ℂ) :
    pderList (i :: l) f = pderList l (pder i f) := rfl

theorem pderList_append_singleton (l : List ι) (i : ι) (f : (ι → ℂ) → ℂ) :
    pderList (l ++ [i]) f = pder i (pderList l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => simp [ih]

section Fin

variable [Fintype ι]

theorem pder_eq_fderiv {f : (ι → ℂ) → ℂ} {s : ι → ℂ} (i : ι) (hf : DifferentiableAt ℂ f s) :
    pder i f s = fderiv ℂ f s (Pi.single i 1) := by
  have h1 : HasDerivAt (fun t : ℂ => s + t • (Pi.single i 1 : ι → ℂ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single i 1 : ι → ℂ)).const_add s
  have h2 : HasFDerivAt f (fderiv ℂ f s) (s + (0 : ℂ) • (Pi.single i 1 : ι → ℂ)) := by
    simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

theorem analyticOnNhd_pder {c : ι → ℂ} {r : ι → ℝ} {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc c r)) (i : ι) :
    AnalyticOnNhd ℂ (pder i f) (polydisc c r) := by
  have hopen := isOpen_polydisc c r
  have ha : AnalyticOnNhd ℂ (fun s => fderiv ℂ f s (Pi.single i 1)) (polydisc c r) := fun w hw =>
    ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1 : ι → ℂ)).analyticAt (fderiv ℂ f w)).comp
      (hf.fderiv w hw)
  have heq : Set.EqOn (pder i f) (fun s => fderiv ℂ f s (Pi.single i 1)) (polydisc c r) :=
    fun w hw => pder_eq_fderiv i (hf w hw).differentiableAt
  exact ha.congr hopen heq.symm

theorem analyticOnNhd_pderList {c : ι → ℂ} {r : ι → ℝ} (l : List ι) :
    ∀ {f : (ι → ℂ) → ℂ}, AnalyticOnNhd ℂ f (polydisc c r) →
      AnalyticOnNhd ℂ (pderList l f) (polydisc c r) := by
  induction l with
  | nil => exact fun h => h
  | cons a l ih => exact fun h => ih (analyticOnNhd_pder h a)

/-- Cauchy estimate for the iterated coordinate derivative in distinct coordinates. -/
theorem norm_pderList_le {c : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    {f : (ι → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f (polydisc c r))
    (hM : ∀ z ∈ polydisc c r, ‖f z‖ ≤ M) (l : List ι) (hl : l.Nodup) {w : ι → ℂ}
    (hw : w ∈ polydisc c r) :
    ‖pderList l f w‖ ≤ M / ∏ i ∈ l.toFinset, (r i - ‖w i - c i‖) := by
  induction l using List.reverseRecOn generalizing w with
  | nil => simpa using hM w hw
  | append_singleton l i ih =>
    have hnd := List.nodup_append.mp hl
    have hil : i ∉ l := by
      intro h; exact hnd.2.2 i h i (by simp) rfl
    have hl' : l.Nodup := hnd.1
    rw [pderList_append_singleton]
    set g := pderList l f with hg
    have hga : AnalyticOnNhd ℂ g (polydisc c r) := analyticOnNhd_pderList l hf
    have hρ : 0 < r i - ‖w i - c i‖ := by have := hw i; linarith
    have hmem : ∀ t : ℂ, ‖t‖ < r i - ‖w i - c i‖ →
        w + t • (Pi.single i 1 : ι → ℂ) ∈ polydisc c r := fun t ht =>
      mem_polydisc_add_single hw i ht
    have hprod : ∀ t : ℂ, ‖t‖ < r i - ‖w i - c i‖ →
        ∏ j ∈ l.toFinset, (r j - ‖(w + t • (Pi.single i 1 : ι → ℂ)) j - c j‖) =
          ∏ j ∈ l.toFinset, (r j - ‖w j - c j‖) := by
      intro t _
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun h => hil (h ▸ List.mem_toFinset.mp hj)
      simp [Pi.single_eq_of_ne hji]
    have hpos : 0 ≤ ∏ j ∈ l.toFinset, (r j - ‖w j - c j‖) :=
      Finset.prod_nonneg fun j _ => by have := hw j; linarith
    have key := norm_fderiv_line_le (f := g) (w := w) (v := (Pi.single i 1 : ι → ℂ)) hρ
      (fun t ht => (hga _ (hmem t ht)).differentiableAt)
      (fun t ht => by
        have := ih hl' (hmem t ht)
        rwa [hprod t ht] at this)
    rw [pder_eq_fderiv i (hga w hw).differentiableAt]
    have hfin : (l ++ [i]).toFinset = insert i l.toFinset := by
      ext x; simp
    rw [hfin, Finset.prod_insert (by simpa using hil), mul_comm, ← div_div]
    exact key

end Fin

end Balaban.Localization
