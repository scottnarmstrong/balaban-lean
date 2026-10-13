/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Positivity

/-!
# Cut expansion: Möbius inversion and the mixed-difference bound

For a finite index type `ι` (the cut parameters) and `F : (ι → ℂ) → ℂ`, write `cutPt I` for the
point equal to `1` on `I` and `0` elsewhere, and
`mixDiff J F = ∑_{I ⊆ J} (-1)^{|J \ I|} F (cutPt I)`,
the `J`-th mixed difference of `F` between the cut values `0` and `1`.

* `sum_mixDiff`: `F 1 = ∑_{J ⊆ ι} mixDiff J F` (Möbius inversion on the Boolean lattice; no
  analyticity).  This is the integral-free form of the interpolation
  `F(1) = ∑_J ∫_{[0,1]^J} ∂_J F (s_J, 0)`.
* `norm_oneDiff_le`: for `g` differentiable on the disc of radius `R` and bounded by `M` there,
  `‖g 1 - g 0‖ ≤ 2 M / R` (Schwarz lemma).
* `norm_mixDiff_le`: if `F` is differentiable on the open cutPolydisc `{s | ∀ P, ‖s P‖ < R}`,
  `R > 1`, and bounded there by `M`, then `‖mixDiff J F‖ ≤ M (2 / R)^{|J|}`.

The bound carries no support information.
-/

@[expose] public section

namespace Balaban.Analysis

open Finset Metric Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cut point: `1` on `I`, `0` elsewhere. -/
noncomputable def cutPt (I : Finset ι) : ι → ℂ := fun P => if P ∈ I then 1 else 0

/-- The `J`-th mixed difference of `F` between the cut values `0` and `1`:
`∑_{I ⊆ J} (-1)^{|J \ I|} F (cutPt I)`. -/
noncomputable def mixDiff (J : Finset ι) (F : (ι → ℂ) → ℂ) : ℂ :=
  ∑ I ∈ J.powerset, (-1 : ℂ) ^ (J.card - I.card) * F (cutPt I)

/-- The open cutPolydisc of radius `R`. -/
def cutPolydisc (ι : Type*) [Fintype ι] (R : ℝ) : Set (ι → ℂ) := {s | ∀ P, ‖s P‖ < R}

theorem cutPt_univ : cutPt (Finset.univ : Finset ι) = fun _ => 1 := by
  funext P; simp [cutPt]

/-- The difference of `F` between the cut values `1` and `0` of the variable `p`. -/
noncomputable def cutDiff (p : ι) (F : (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ :=
  fun s => F (Function.update s p 1) - F (Function.update s p 0)

omit [Fintype ι] in
theorem mixDiff_insert {p : ι} {J : Finset ι} (hp : p ∉ J) (F : (ι → ℂ) → ℂ) :
    mixDiff (insert p J) F = mixDiff J (cutDiff p F) := by
  unfold mixDiff cutDiff
  rw [Finset.sum_powerset_insert hp]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have h1 : ∀ I ∈ J.powerset, (-1 : ℂ) ^ ((insert p J).card - I.card) * F (cutPt I) =
      -((-1 : ℂ) ^ (J.card - I.card) * F (Function.update (cutPt I) p 0)) := by
    intro I hI
    have hIJ := Finset.mem_powerset.1 hI
    have hpI : p ∉ I := fun h => hp (hIJ h)
    have hc : (insert p J).card = J.card + 1 := Finset.card_insert_of_notMem hp
    have hle := Finset.card_le_card hIJ
    have : (insert p J).card - I.card = (J.card - I.card) + 1 := by omega
    have hu : Function.update (cutPt I) p 0 = cutPt I := by
      funext q
      by_cases h : q = p
      · subst h; simp [cutPt, hpI]
      · simp [Function.update_of_ne h]
    rw [this, hu, pow_succ]; ring
  have h2 : ∀ I ∈ J.powerset, (-1 : ℂ) ^ ((insert p J).card - (insert p I).card) *
      F (cutPt (insert p I)) = (-1 : ℂ) ^ (J.card - I.card) * F (Function.update (cutPt I) p 1) := by
    intro I hI
    have hIJ := Finset.mem_powerset.1 hI
    have hpI : p ∉ I := fun h => hp (hIJ h)
    rw [Finset.card_insert_of_notMem hp, Finset.card_insert_of_notMem hpI]
    have hu : Function.update (cutPt I) p 1 = cutPt (insert p I) := by
      funext q
      by_cases h : q = p
      · subst h; simp [cutPt]
      · simp [cutPt, h]
    rw [hu]; simp
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  ring

omit [Fintype ι] in
/-- **Möbius inversion over the Boolean lattice** (for every subset `U`):
`F (cutPt U) = ∑_{J ⊆ U} Δ_J F`. -/
theorem cutPt_eq_sum_mixDiff (U : Finset ι) : ∀ F : (ι → ℂ) → ℂ,
    F (cutPt U) = ∑ J ∈ U.powerset, mixDiff J F := by
  induction U using Finset.induction_on with
  | empty => intro F; simp [mixDiff]
  | insert p U hp ih =>
    intro F
    rw [Finset.sum_powerset_insert hp]
    have h1 : ∀ J ∈ U.powerset, mixDiff (insert p J) F = mixDiff J (cutDiff p F) := fun J hJ =>
      mixDiff_insert (fun h => hp (Finset.mem_powerset.1 hJ h)) F
    rw [Finset.sum_congr rfl h1, ← ih (cutDiff p F), ← ih F]
    unfold cutDiff
    have hu0 : Function.update (cutPt U) p 0 = cutPt U := by
      funext q
      by_cases h : q = p
      · subst h; simp [cutPt, hp]
      · simp [Function.update_of_ne h]
    have hu1 : Function.update (cutPt U) p 1 = cutPt (insert p U) := by
      funext q
      by_cases h : q = p
      · subst h; simp [cutPt]
      · simp [cutPt, h]
    rw [hu0, hu1]; ring

/-- **Möbius inversion over the Boolean lattice**: `F(1) = ∑_{J ⊆ ι} Δ_J F`.  This is the
integral-free form of `F(1) = ∑_J ∫_{[0,1]^J} ∂_J F (s_J, 0) ds_J`. -/
theorem sum_mixDiff (F : (ι → ℂ) → ℂ) :
    F (fun _ => 1) = ∑ J ∈ (Finset.univ : Finset ι).powerset, mixDiff J F := by
  rw [← cutPt_univ]; exact cutPt_eq_sum_mixDiff _ F

/-! ### The bound -/

/-- One-variable difference: if `g` is differentiable on the disc of radius `R` and bounded by `M`
there, then `‖g 1 - g 0‖ ≤ 2 M / R` (Schwarz lemma applied to `g`, centre `0`, `R₂ = 2M`). -/
theorem norm_oneDiff_le {g : ℂ → ℂ} {R M : ℝ} (hR : 1 < R)
    (hd : DifferentiableOn ℂ g (ball 0 R)) (hM : ∀ t ∈ ball (0 : ℂ) R, ‖g t‖ ≤ M) :
    ‖g 1 - g 0‖ ≤ 2 * M / R := by
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by simp; linarith
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := by simp; linarith
  have hmaps : MapsTo g (ball 0 R) (closedBall (g 0) (2 * M)) := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm]
    calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM t ht) (hM 0 h0)
      _ = 2 * M := by ring
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1
  rw [dist_eq_norm] at this
  simpa using this

theorem cutPt_mem_cutPolydisc {R : ℝ} (hR : 1 < R) (I : Finset ι) : cutPt I ∈ cutPolydisc ι R := by
  intro P
  unfold cutPt
  split_ifs <;> simp <;> linarith

theorem differentiable_update (p : ι) (c : ℂ) : Differentiable ℂ (fun s : ι → ℂ => Function.update s p c) := by
  rw [differentiable_pi]
  intro q
  by_cases h : q = p
  · subst h; simp
  · simpa [Function.update_of_ne h] using differentiable_apply (𝕜 := ℂ) q

omit [Fintype ι] in
theorem differentiable_update_right (s : ι → ℂ) (p : ι) :
    Differentiable ℂ (fun t : ℂ => Function.update s p t) := by
  rw [differentiable_pi]
  intro q
  by_cases h : q = p
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem update_mem_cutPolydisc {R : ℝ} {s : ι → ℂ} (hs : s ∈ cutPolydisc ι R) (p : ι) {c : ℂ}
    (hc : ‖c‖ < R) : Function.update s p c ∈ cutPolydisc ι R := by
  intro q
  by_cases h : q = p
  · subst h; simpa using hc
  · simpa [Function.update_of_ne h] using hs q

theorem cutDiff_bound {R M : ℝ} (hR : 1 < R) {F : (ι → ℂ) → ℂ}
    (hd : DifferentiableOn ℂ F (cutPolydisc ι R)) (hM : ∀ s ∈ cutPolydisc ι R, ‖F s‖ ≤ M) (p : ι) :
    (DifferentiableOn ℂ (cutDiff p F) (cutPolydisc ι R)) ∧
      ∀ s ∈ cutPolydisc ι R, ‖cutDiff p F s‖ ≤ 2 * M / R := by
  have h1 : ‖(1 : ℂ)‖ < R := by simpa using hR
  have h0 : ‖(0 : ℂ)‖ < R := by simp; linarith
  refine ⟨?_, fun s hs => ?_⟩
  · unfold cutDiff
    refine DifferentiableOn.sub ?_ ?_
    · exact hd.comp (differentiable_update p 1).differentiableOn
        (fun s hs => update_mem_cutPolydisc hs p h1)
    · exact hd.comp (differentiable_update p 0).differentiableOn
        (fun s hs => update_mem_cutPolydisc hs p h0)
  · have hmem : ∀ t ∈ ball (0 : ℂ) R, Function.update s p t ∈ cutPolydisc ι R := fun t ht =>
      update_mem_cutPolydisc hs p (by simpa using ht)
    have hg : DifferentiableOn ℂ (fun t : ℂ => F (Function.update s p t)) (ball 0 R) :=
      hd.comp (differentiable_update_right s p).differentiableOn hmem
    have := norm_oneDiff_le hR hg (fun t ht => hM _ (hmem t ht))
    simpa [cutDiff] using this

/-- **Bound of the `J`-th mixed difference**: if `F` is differentiable on the open cutPolydisc of
radius `R > 1` and bounded there by `M`, then `‖Δ_J F‖ ≤ M (2 / R)^{|J|}`. -/
theorem norm_mixDiff_le {R : ℝ} (hR : 1 < R) (J : Finset ι) : ∀ {M : ℝ} {F : (ι → ℂ) → ℂ},
    DifferentiableOn ℂ F (cutPolydisc ι R) → (∀ s ∈ cutPolydisc ι R, ‖F s‖ ≤ M) →
    ‖mixDiff J F‖ ≤ M * (2 / R) ^ J.card := by
  induction J using Finset.induction_on with
  | empty =>
    intro M F _ hM
    have h0 : cutPt (∅ : Finset ι) = 0 := by funext P; simp [cutPt]
    simpa [mixDiff, h0] using hM 0 (h0 ▸ cutPt_mem_cutPolydisc hR ∅)
  | insert p J hp ih =>
    intro M F hd hM
    obtain ⟨hd', hM'⟩ := cutDiff_bound hR hd hM p
    rw [mixDiff_insert hp, Finset.card_insert_of_notMem hp]
    have := ih hd' hM'
    calc ‖mixDiff J (cutDiff p F)‖ ≤ 2 * M / R * (2 / R) ^ J.card := this
      _ = M * (2 / R) ^ (J.card + 1) := by ring

end Balaban.Analysis
