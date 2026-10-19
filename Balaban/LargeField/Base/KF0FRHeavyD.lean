/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRHeavySite
public import Balaban.Polymer.MarkBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRHeavyD`: one term of the expansion of the heavy bound (route FR, (H4)–(H5))

`notes/phase1/KF0-FR.md` (H4), (H5). For a set `A` of terms with site part `D`, the pointwise
majorant of `∏_{t∈A} |F_t|` expands into a sum over `D' ⊆ D` (`prod_norm_frF_le_sum`), each term
being `∏_{z∈D'} w(u_z)` times a product of one-site factors (`frSiteFac`). On the event of the heavy
set `H` (`frEvt`: heavy on `H`, ordinary on `W ∖ H`), the integral of one term is at most
`η^{|H|} 2^{|D|} K₀^{|W'|}` (`lintegral_frDterm_le`), with `η` the cost of a heavy site and
`K₀ = e^{ap + θ p²}` the cost of an ordinary site of `W'`.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green Balaban.Polymer
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)

variable {d ℓ : ℕ} [NeZero ℓ]

/-! ### The event of a heavy set, site by site -/

/-- The event of one site: heavy on `H`, ordinary on `W ∖ H`, free elsewhere. -/
def frEvt (p : ℝ) (W H : Finset (Torus d ℓ)) (y : Torus d ℓ) : Set (perp h × Bool) :=
  if y ∈ H then (frOrd h p)ᶜ else if y ∈ W then frOrd h p else Set.univ

omit [NeZero ℓ] in
theorem measurableSet_frEvt (p : ℝ) (W H : Finset (Torus d ℓ)) (y : Torus d ℓ) :
    MeasurableSet (frEvt h p W H y) := by
  unfold frEvt
  split_ifs
  · exact (measurableSet_frOrd h p).compl
  · exact measurableSet_frOrd h p
  · exact MeasurableSet.univ

omit [NeZero ℓ] in
theorem markEvent_iff {p : ℝ} {W H : Finset (Torus d ℓ)} (ω : Torus d ℓ → perp h × Bool) :
    MarkEvent (fun _ => frOrd h p) W H ω ↔ ∀ y, ω y ∈ frEvt h p W H y := by
  constructor
  · rintro ⟨h1, h2⟩ y
    unfold frEvt
    split_ifs with hH hW
    · exact h1 y hH
    · exact h2 y hW hH
    · trivial
  · intro hy
    refine ⟨fun x hx => ?_, fun x hx hxH => ?_⟩
    · have := hy x; simpa [frEvt, hx] using this
    · have := hy x; simpa [frEvt, hxH, hx] using this

/-- The indicator of the event of a heavy set is the product of the one-site indicators. -/
theorem indicator_markEvent_eq {p : ℝ} {W H : Finset (Torus d ℓ)}
    (F : (Torus d ℓ → perp h × Bool) → ℝ≥0∞) (ω : Torus d ℓ → perp h × Bool) :
    Set.indicator {ω | MarkEvent (fun _ => frOrd h p) W H ω} F ω =
      (∏ y, (frEvt h p W H y).indicator 1 (ω y)) * F ω := by
  by_cases hω : ∀ y, ω y ∈ frEvt h p W H y
  · rw [Set.indicator_of_mem (show ω ∈ {ω | MarkEvent (fun _ => frOrd h p) W H ω} from
      (markEvent_iff h ω).2 hω)]
    simp [Set.indicator_of_mem (hω _)]
  · push Not at hω
    obtain ⟨y, hy⟩ := hω
    rw [Set.indicator_of_notMem (show ω ∉ {ω | MarkEvent (fun _ => frOrd h p) W H ω} from
      fun h' => hy ((markEvent_iff h ω).1 h' y))]
    rw [Finset.prod_eq_zero (Finset.mem_univ y) (Set.indicator_of_notMem hy _), zero_mul]

/-! ### The expansion over the outer band -/

/-- The one-site factor of the term `D'` of the expansion. -/
def frSiteFac (ε β ν G a θ : ℝ) (D D' W' : Finset (Torus d ℓ)) (y : Torus d ℓ)
    (w : perp h × Bool) : ℝ :=
  ((if y ∈ D' then frLam' ε β ν G w.2 else 1) * (if y ∈ D \ D' then 2 * frLam ε β ν G w.2 else 1)) *
    (if y ∈ W' then frEx h a θ w.1 else 1)

omit [NeZero ℓ] in
theorem measurable_frSiteFac (ε β ν G a θ : ℝ) (D D' W' : Finset (Torus d ℓ)) (y : Torus d ℓ) :
    Measurable (frSiteFac h ε β ν G a θ D D' W' y) := by
  unfold frSiteFac
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · split_ifs
    · exact (measurable_from_top (f := frLam' ε β ν G)).comp measurable_snd
    · exact measurable_const
  · split_ifs
    · exact (measurable_const.mul (measurable_from_top (f := frLam ε β ν G))).comp measurable_snd
    · exact measurable_const
  · split_ifs
    · exact (measurable_frEx h a θ).comp measurable_fst
    · exact measurable_const

omit [NeZero ℓ] in
theorem frSiteFac_nonneg {ε : ℝ} (hε : 0 ≤ ε) (β ν G a θ : ℝ) (D D' W' : Finset (Torus d ℓ))
    (y : Torus d ℓ) (w : perp h × Bool) : 0 ≤ frSiteFac h ε β ν G a θ D D' W' y w := by
  unfold frSiteFac
  have h1 := frLam_nonneg hε β ν G w.2
  have h2 := frLam'_nonneg hε β ν G w.2
  have h3 := frEx_pos h a θ w.1
  split_ifs <;> positivity

/-- **(H4) The expansion of the pointwise majorant over the outer band.** -/
theorem prod_norm_frF_le_sum (hh : ‖h‖ = 1) {β ν ε G θ : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    (hε : 0 < ε) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (hg : ∀ x, ∑ i, ‖g x i‖ ≤ G)
    (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ) (A : Finset (FRTerm d ℓ))
    (ω : Torus d ℓ → perp h × Bool) :
    ∏ t ∈ A, ‖frF h hh β ν ε R g t ω‖ ≤
      ∑ D' ∈ A.toLeft.powerset, (∏ z ∈ D', chartWeight h (frField d ℓ β ν R (frPsi h ω) z)) *
        ∏ y, frSiteFac h ε β ν G (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) (θ / 2)
          A.toLeft D' (frSiteHull R A.toLeft) y (ω y) := by
  refine (prod_norm_frF_le h hh hβ hν hε R g hg hQ A ω).trans (le_of_eq ?_)
  set D := A.toLeft
  set W' := frSiteHull R D
  set a := 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹
  have hadd : ∀ x ∈ D, 2 * frLam ε β ν G (frSig h ω x) +
      chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x) =
      chartWeight h (frField d ℓ β ν R (frPsi h ω) x) * frLam' ε β ν G (frSig h ω x) +
        2 * frLam ε β ν G (frSig h ω x) := fun x _ => add_comm _ _
  rw [Finset.prod_congr rfl hadd, Finset.prod_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun D' _ => ?_
  have hfac : ∏ y, frSiteFac h ε β ν G a (θ / 2) D D' W' y (ω y) =
      (∏ y ∈ D', frLam' ε β ν G (frSig h ω y)) * (∏ y ∈ D \ D', 2 * frLam ε β ν G (frSig h ω y)) *
        ∏ y ∈ W', Real.exp (a * ‖frPsi h ω y‖ + θ / 2 * ‖frPsi h ω y‖ ^ 2) := by
    unfold frSiteFac
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter,
      Finset.univ_inter]
    rfl
  rw [hfac, Finset.prod_mul_distrib]
  ring

end

end Balaban.LargeField.KF0FR
