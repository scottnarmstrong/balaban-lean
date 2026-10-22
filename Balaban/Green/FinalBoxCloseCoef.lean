/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCore
public import Balaban.Green.FinalTaggedTorusClose
public import Balaban.Analysis.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closeness of the rooted coefficients of two cut fields (A6-3 (d), box localization on two tori)

Two systems of cut fields `Φ(s, w) = φ₀ + T(s) w` (`linField`) with the decoupling property
(`CutDecoupling`), on site sets `Ω`, `Ω'` with cells `ι`, `ι'`, are related by a map of sites `f` and a
map of cells `e`: the region of a family `C` of cells is carried by `f` onto the region of `e C`
(injectively), the variables correspond there (`w'(f y) = w(y)`), and the entries of the two cut
families at corresponding parameters and sites differ by at most `δ`. Then:

* `linField_close`: on the read set `S`, the cut fields at corresponding parameters differ by at most
  `ε_φ + |reg C| δ ρ` (`ε_φ` the difference of the centres, `ρ` a bound for `w`);
* `rootedCoef_close_relabel`: if the terms evaluated at the two cut fields differ by at most `B` at
  corresponding parameters of the polydisc of radius `R > 1`, the rooted coefficients differ by at most
  `B / (R - 1)^{|C|}` (`norm_coef_sub_relabel_le`);
* `norm_term_sub_le_of_transport`: the bound `B` for a term `τ` analytic and bounded by `M_τ` on the
  ball of radius `r` around `φ₀`, and a second term `τ'` within `η` of `τ` read through `f` on the read
  set: `B = η + M_τ ε / (r - r₁ - ε)`, `ε` the difference of the fields on the read set.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Close

variable {ι ι' Ω Ω' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype Ω] [Fintype Ω']

open Classical in
/-- The region of a family of cells as a finite set of sites. -/
noncomputable def regFin (P : ι → Set Ω) (C : Finset ι) : Finset Ω :=
  Finset.univ.filter fun y => y ∈ patchReg P C

omit [Fintype ι] [DecidableEq ι] in
theorem mem_regFin {P : ι → Set Ω} {C : Finset ι} {y : Ω} :
    y ∈ regFin P C ↔ y ∈ patchReg P C := by
  classical
  simp [regFin]

omit [Fintype ι] [Fintype ι'] in
/-- **The cut fields of two related systems are close on the read set.** -/
theorem linField_close {P : ι → Set Ω} {P' : ι' → Set Ω'} {R : ℝ}
    {T : (ι → ℂ) → Ω → Ω → ℂ} {T' : (ι' → ℂ) → Ω' → Ω' → ℂ}
    (hT : CutDecoupling P R T) (hT' : CutDecoupling P' R T') (e : ι → ι') (f : Ω → Ω')
    {C : Finset ι} (hinj : Set.InjOn f (patchReg P C))
    (hreg : patchReg P' (C.image e) = f '' patchReg P C)
    {s : ι → ℂ} (hs : s ∈ polydisc (0 : ι → ℂ) (fun _ => R)) (hsC : s ∈ supportedOn C)
    {s' : ι' → ℂ} (hs' : s' ∈ polydisc (0 : ι' → ℂ) (fun _ => R))
    (hs'C : s' ∈ supportedOn (C.image e))
    {φ₀ w : Ω → ℂ} {φ₀' w' : Ω' → ℂ} (hw : ∀ y ∈ patchReg P C, w' (f y) = w y)
    {ρ : ℝ} (hρ : ∀ y, ‖w y‖ ≤ ρ) {S : Set Ω} {δ εφ : ℝ}
    (hTT : ∀ x ∈ S, ∀ y ∈ patchReg P C, ‖T s x y - T' s' (f x) (f y)‖ ≤ δ)
    (hφ : ∀ x ∈ S, ‖φ₀ x - φ₀' (f x)‖ ≤ εφ) :
    ∀ x ∈ S, ‖linField φ₀ T s w x - linField φ₀' T' s' w' (f x)‖ ≤
      εφ + ((regFin P C).card : ℝ) * δ * ρ := by
  classical
  intro x hx
  -- the sum of the first field is over the region
  have h1 : ∑ y, T s x y * w y = ∑ y ∈ regFin P C, T s x y * w y := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_).symm
    by_contra hne
    have hT0 : T s x y ≠ 0 := left_ne_zero_of_mul hne
    exact hy (mem_regFin.2 (hT.supp C s hs hsC x y hT0).2)
  -- the sum of the second field is over the image of the region
  have h2 : ∑ y', T' s' (f x) y' * w' y' = ∑ y ∈ regFin P C, T' s' (f x) (f y) * w y := by
    have hinjF : Set.InjOn f (regFin P C : Set Ω) := fun a ha b hb hab =>
      hinj (mem_regFin.1 ha) (mem_regFin.1 hb) hab
    rw [← Finset.sum_subset (Finset.subset_univ ((regFin P C).image f)) ?_,
      Finset.sum_image hinjF]
    · exact Finset.sum_congr rfl fun y hy => by rw [hw y (mem_regFin.1 hy)]
    · intro y' _ hy'
      by_contra hne
      have hT0 : T' s' (f x) y' ≠ 0 := left_ne_zero_of_mul hne
      have hmem := (hT'.supp (C.image e) s' hs' hs'C (f x) y' hT0).2
      rw [hreg] at hmem
      obtain ⟨y, hy, rfl⟩ := hmem
      exact hy' (Finset.mem_image_of_mem f (mem_regFin.2 hy))
  simp only [linField]
  rw [h1, h2]
  have e : φ₀ x + ∑ y ∈ regFin P C, T s x y * w y -
      (φ₀' (f x) + ∑ y ∈ regFin P C, T' s' (f x) (f y) * w y) =
      (φ₀ x - φ₀' (f x)) + ∑ y ∈ regFin P C, (T s x y - T' s' (f x) (f y)) * w y := by
    rw [Finset.sum_congr rfl fun y _ => sub_mul (T s x y) (T' s' (f x) (f y)) (w y),
      Finset.sum_sub_distrib]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add (hφ x hx) ?_)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y ∈ regFin P C, ‖(T s x y - T' s' (f x) (f y)) * w y‖
      ≤ ∑ _y ∈ regFin P C, δ * ρ := by
        refine Finset.sum_le_sum fun y hy => ?_
        rw [norm_mul]
        exact mul_le_mul (hTT x hx y (mem_regFin.1 hy)) (hρ y) (norm_nonneg _)
          ((norm_nonneg _).trans (hTT x hx y (mem_regFin.1 hy)))
    _ = ((regFin P C).card : ℝ) * δ * ρ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The rooted coefficients of two related systems are close** (the Cauchy estimate under a
relabelling of the cells). -/
theorem rootedCoef_close_relabel {R : ℝ} (hR : 1 < R) (e : ι → ι') {C : Finset ι}
    (he : Set.InjOn e (C : Set ι)) {T : (ι → ℂ) → Ω → Ω → ℂ} {T' : (ι' → ℂ) → Ω' → Ω' → ℂ}
    {τ : (Ω → ℂ) → ℂ} {τ' : (Ω' → ℂ) → ℂ} {φ₀ w : Ω → ℂ} {φ₀' w' : Ω' → ℂ}
    (hg : AnalyticOnNhd ℂ (fun s => τ (linField φ₀ T s w)) (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hg' : AnalyticOnNhd ℂ (fun s' => τ' (linField φ₀' T' s' w'))
      (polydisc (0 : ι' → ℂ) (fun _ => R))) {B : ℝ}
    (hB : ∀ s ∈ supN C R, ∀ s' ∈ supportedOn (C.image e), (∀ i ∈ C, s' (e i) = s i) →
      ‖τ (linField φ₀ T s w) - τ' (linField φ₀' T' s' w')‖ ≤ B) :
    ‖rootedCoef τ φ₀ T w C - rootedCoef τ' φ₀' T' w' (C.image e)‖ ≤ B / (R - 1) ^ C.card :=
  norm_coef_sub_relabel_le hR e he hg hg' hB

omit [Fintype Ω'] in
/-- **The terms at two close fields** (Cauchy estimate). Let `τ` be analytic and bounded by `M_τ` on the ball of radius `r` around `φ₀`, and let `τ'` be within `η` of `τ` read
through `f` on `S`. If `u` lies in the ball of radius `r₁ < r` around `φ₀` and `u'` differs from `u`
through `f` by at most `ε < r - r₁` on `S`, then `|τ u - τ' u'| ≤ η + M_τ ε / (r - r₁ - ε)`. -/
theorem norm_term_sub_le_of_transport {S : Set Ω} {τ : (Ω → ℂ) → ℂ} {τ' : (Ω' → ℂ) → ℂ}
    (f : Ω → Ω') {φ₀ : Ω → ℂ} {r Mτ : ℝ}
    (hτan : AnalyticOnNhd ℂ τ (Metric.ball φ₀ r)) (hτb : ∀ u ∈ Metric.ball φ₀ r, ‖τ u‖ ≤ Mτ)
    {η : ℝ} (hττ : ∀ (u' : Ω' → ℂ) (v : Ω → ℂ), (∀ x ∈ S, v x = u' (f x)) →
      ‖τ' u' - τ v‖ ≤ η)
    {r₁ ε : ℝ} (hε : 0 ≤ ε) (hr : r₁ + ε < r) {u : Ω → ℂ} (hu : u ∈ Metric.ball φ₀ r₁)
    {u' : Ω' → ℂ} (huu : ∀ x ∈ S, ‖u x - u' (f x)‖ ≤ ε) :
    ‖τ u - τ' u'‖ ≤ η + Mτ * ε / (r - r₁ - ε) := by
  classical
  set v : Ω → ℂ := fun x => if x ∈ S then u' (f x) else u x with hv
  have hvS : ∀ x ∈ S, v x = u' (f x) := fun x hx => by simp [hv, hx]
  have hdist : dist v u ≤ ε := by
    rw [dist_pi_le_iff hε]
    intro x
    by_cases hx : x ∈ S
    · rw [dist_eq_norm, hvS x hx, norm_sub_rev]; exact huu x hx
    · simp [hv, hx, hε]
  have hu1 : dist u φ₀ < r₁ := Metric.mem_ball.1 hu
  have hsub : Metric.ball u (r - r₁) ⊆ Metric.ball φ₀ r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith [dist_triangle z u φ₀]
  have hvb : v ∈ Metric.ball u (r - r₁) := Metric.mem_ball.2 (by linarith)
  have hc := norm_sub_le_of_ball (hτan.differentiableOn.mono hsub)
    (fun z hz => hτb z (hsub hz)) hvb
  have hMτ : 0 ≤ Mτ := (norm_nonneg _).trans (hτb u (hsub (Metric.mem_ball_self (by linarith))))
  have h1 : ‖τ v - τ u‖ ≤ Mτ * ε / (r - r₁ - ε) := by
    refine hc.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hdn : 0 ≤ dist v u := dist_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hdist hMτ]
  calc ‖τ u - τ' u'‖ ≤ ‖τ' u' - τ v‖ + ‖τ v - τ u‖ := by
        rw [norm_sub_rev (τ u)]
        calc ‖τ' u' - τ u‖ = ‖(τ' u' - τ v) + (τ v - τ u)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
    _ ≤ η + Mτ * ε / (r - r₁ - ε) := add_le_add (hττ u' v hvS) h1

end Close

end Balaban.Green
