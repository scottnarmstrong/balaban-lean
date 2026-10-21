/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRGas
public import Balaban.Polymer.LaplaceAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRAnalytic`: the activities of route FR are analytic in the source (A)

`notes/phase1/KF0-FR.md` (A). The source enters the site terms only through
`e^{⟨g_x, Φ_x - h⟩}`, so a product of terms is `∏_{t∈A} F_t(g) = ∏_{t∈A} F_t(0) e^{∑_{x,i} g_{x,i}
V_{x,i}}` with `|V| ≤ 2` (`prod_frF_eq_exp`). The Mayer activity of a set of blocks is a finite
combination of integrals of such products (`frK_eq_sum`), each an exponential moment of an
integrable weight, hence analytic in `g` on all of `ℂ^{Λ × N}` (`analyticOnNhd_frK`).
-/

@[expose] public section

open MeasureTheory Finset Balaban.Green Balaban.Polymer Balaban.LargeField.KF0Gas

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The coefficient of the source `g_{x,i}` in a product of terms `A`. -/
def frSrcCoef (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (A : Finset (FRTerm d ℓ)) (p : Torus d ℓ × Fin N)
    (ω : Torus d ℓ → perp h × Bool) : ℂ :=
  if Sum.inl p.1 ∈ A then
    ((((sheetPt h hh (frSig h ω p.1) (frField d ℓ β ν R (frPsi h ω) p.1) : Sph) : E) - h) p.2 : ℂ)
  else 0

theorem norm_frSrcCoef_le (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (A : Finset (FRTerm d ℓ))
    (p : Torus d ℓ × Fin N) (ω : Torus d ℓ → perp h × Bool) : ‖frSrcCoef h hh β ν R A p ω‖ ≤ 2 := by
  unfold frSrcCoef
  split_ifs
  · rw [Complex.norm_real]
    exact (PiLp.norm_apply_le _ _).trans (norm_sheetPt_sub_le_two h hh _ _)
  · simp

theorem measurable_frSrcCoef (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (A : Finset (FRTerm d ℓ))
    (p : Torus d ℓ × Fin N) : Measurable (frSrcCoef h hh β ν R A p) := by
  unfold frSrcCoef
  split_ifs
  · exact Complex.measurable_ofReal.comp ((measurable_pi_apply p.2).comp
      ((PiLp.continuous_ofLp 2 _).measurable.comp
        ((measurable_sheetPt_frField h hh β ν R p.1).sub_const h)))
  · exact measurable_const

/-- The site term at a source is the site term at `0` times the source factor. -/
theorem frSite_eq_mul_exp (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (x : Torus d ℓ) (ω : Torus d ℓ → perp h × Bool) :
    frSite h hh β ν ε R g x ω = frSite h hh β ν ε R 0 x ω *
      Complex.exp (∑ i : Fin N, g x i *
        ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ)) := by
  unfold frSite
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.exp_zero, mul_one]
  ring

/-- **A product of terms at a source** is the product at `0` times an exponential moment. -/
theorem prod_frF_eq_exp (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (A : Finset (FRTerm d ℓ)) (ω : Torus d ℓ → perp h × Bool) :
    ∏ t ∈ A, frF h hh β ν ε R g t ω = (∏ t ∈ A, frF h hh β ν ε R 0 t ω) *
      Complex.exp (∑ p : Torus d ℓ × Fin N, g p.1 p.2 * frSrcCoef h hh β ν R A p ω) := by
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight (f := fun t => frF h hh β ν ε R 0 t ω)]
  have hb : ∀ t, frF h hh β ν ε R g (Sum.inr t) ω = frF h hh β ν ε R 0 (Sum.inr t) ω := by
    rintro ⟨x, μ⟩; rfl
  have hs : ∏ x ∈ A.toLeft, frF h hh β ν ε R g (Sum.inl x) ω =
      (∏ x ∈ A.toLeft, frF h hh β ν ε R 0 (Sum.inl x) ω) *
        Complex.exp (∑ x ∈ A.toLeft, ∑ i : Fin N, g x i *
          ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ)) := by
    rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => frSite_eq_mul_exp h hh β ν ε R g x ω
  have hx : ∀ x, ∑ i : Fin N, g x i * frSrcCoef h hh β ν R A (x, i) ω =
      if Sum.inl x ∈ A then ∑ i : Fin N, g x i *
        ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ)
      else 0 := by
    intro x
    unfold frSrcCoef
    split_ifs <;> simp
  have hsum : ∑ p : Torus d ℓ × Fin N, g p.1 p.2 * frSrcCoef h hh β ν R A p ω =
      ∑ x ∈ A.toLeft, ∑ i : Fin N, g x i *
        ((((sheetPt h hh (frSig h ω x) (frField d ℓ β ν R (frPsi h ω) x) : Sph) : E) - h) i : ℂ) := by
    rw [Fintype.sum_prod_type]
    simp only [hx]
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext x; simp) fun x _ => rfl
  rw [Finset.prod_congr rfl fun t _ => hb t, hs, hsum]
  ring

/-! ### The activities -/

variable {s m : ℕ} [NeZero s] [NeZero m]

/-- The terms of a family of sets of blocks. -/
def frTT (R : ℕ) (𝒳 : Finset (NePoly (Torus d m))) : Finset (FRTerm d (s * m)) :=
  𝒳.biUnion fun X => keyTerms (frKey R) Finset.univ X

/-- **The product of grouped weights expanded into products of terms.** -/
theorem prod_frFX_eq (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ)
    (C : Finset (NePoly (Torus d m))) (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) :
    ∏ X ∈ C, frFX h hh β ν ε R g X Φ = ∑ 𝒳 ∈ C.powerset,
      (-1 : ℂ) ^ (C \ 𝒳).card * ∏ t ∈ frTT (s := s) R 𝒳, frF h hh β ν ε R g t (toSites Φ) := by
  have hX : ∀ X, frFX h hh β ν ε R g X Φ =
      ∏ t ∈ keyTerms (frKey R) Finset.univ X, frF h hh β ν ε R g t (toSites Φ) + (-1) := by
    intro X
    have := one_add_frFX h hh β ν ε R g X Φ
    unfold keyTerms
    rw [← this]; ring
  simp_rw [hX]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun 𝒳 h𝒳 => ?_
  rw [Finset.prod_const, mul_comm]
  congr 1
  unfold frTT
  rw [Finset.prod_biUnion]
  intro X _ X' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro t ht ht'
  exact hne ((Finset.mem_filter.1 ht).2.symm.trans (Finset.mem_filter.1 ht').2)

/-- The weight of a product of terms at `0`, on block configurations. -/
def frW0 (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (A : Finset (FRTerm d (s * m)))
    (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) : ℂ :=
  ∏ t ∈ A, frF h hh β ν ε R 0 t (toSites Φ)

theorem integrable_frW0 (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (R : ℕ)
    (hint0 : ∀ C : Finset (FRTerm d (s * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R 0 t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε)) (A : Finset (FRTerm d (s * m))) :
    Integrable (frW0 h hh β ν ε R A)
      (Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) := by
  have e : frW0 h hh β ν ε R A = fun Φ =>
      ∑ C ∈ A.powerset, ∏ t ∈ C, frFB h hh β ν ε R 0 t Φ := by
    funext Φ
    unfold frW0 frFB
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun t _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun C _ => integrable_prod_frFB h hh hε R 0 C (hint0 C)

/-- **One product of terms is an exponential moment, analytic in the source.** -/
theorem analyticOnNhd_integral_prod_frF (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (R : ℕ)
    (hint0 : ∀ C : Finset (FRTerm d (s * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R 0 t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε)) (A : Finset (FRTerm d (s * m))) :
    AnalyticOnNhd ℂ (fun g : Torus d (s * m) → Fin N → ℂ =>
      ∫ Φ, ∏ t ∈ A, frF h hh β ν ε R g t (toSites Φ)
        ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε)))) Set.univ := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  have hl := analyticOnNhd_integral_mul_exp (fun b => blockRef (d := d) (s := s) (m' := m)
    (frSiteMeasure h ε) b) (ι := Torus d (s * m) × Fin N) (frW0 h hh β ν ε R A)
    (integrable_frW0 h hh hε R hint0 A)
    (fun p Φ => frSrcCoef h hh β ν R A p (toSites Φ))
    (fun p => (measurable_frSrcCoef h hh β ν R A p).comp measurable_toSites) (C := 2)
    (by norm_num) (fun p Φ => norm_frSrcCoef_le h hh β ν R A p (toSites Φ))
  set U : (Torus d (s * m) → Fin N → ℂ) →L[ℂ] (Torus d (s * m) × Fin N → ℂ) :=
    ContinuousLinearMap.pi fun p =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) p.2).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d (s * m) => Fin N → ℂ) p.1) with hU
  have hcomp := hl.comp (U.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  refine hcomp.congr isOpen_univ fun g _ => ?_
  simp only [Function.comp, hU, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  beta_reduce
  rw [prod_frF_eq_exp h hh β ν ε R g A (toSites Φ)]
  rfl

/-- **The Mayer activities of route FR are analytic in the source.** -/
theorem analyticOnNhd_frK (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (R : ℕ)
    (hint0 : ∀ C : Finset (FRTerm d (s * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R 0 t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε)) (Y : NePoly (Torus d m)) :
    AnalyticOnNhd ℂ (fun g : Torus d (s * m) → Fin N → ℂ =>
      mayerGenK (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
        (fun X : NePoly (Torus d m) => X.1) (frFX h hh β ν ε R g) Y) Set.univ := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  have hintA : ∀ (g : Torus d (s * m) → Fin N → ℂ) (A : Finset (FRTerm d (s * m))),
      Integrable (fun Φ => ∏ t ∈ A, frF h hh β ν ε R g t (toSites Φ))
        (Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) := by
    intro g A
    have hw := integrable_frW0 h hh hε R hint0 A
    have hm : Measurable fun Φ : ∀ b, BlockSpace d s m (perp h × Bool) b =>
        Complex.exp (∑ p : Torus d (s * m) × Fin N, g p.1 p.2 *
          frSrcCoef h hh β ν R A p (toSites Φ)) :=
      Complex.measurable_exp.comp (Finset.measurable_sum _ fun p _ => measurable_const.mul
        ((measurable_frSrcCoef h hh β ν R A p).comp measurable_toSites))
    have hb : ∀ Φ : ∀ b, BlockSpace d s m (perp h × Bool) b,
        ‖Complex.exp (∑ p : Torus d (s * m) × Fin N, g p.1 p.2 *
          frSrcCoef h hh β ν R A p (toSites Φ))‖ ≤
        Real.exp (∑ p : Torus d (s * m) × Fin N, ‖g p.1 p.2‖ * 2) := by
      intro Φ
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_frSrcCoef_le h hh β ν R A p _) (norm_nonneg _)
    have := hw.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
    refine this.congr (Filter.Eventually.of_forall fun Φ => ?_)
    simp only [frW0]
    rw [prod_frF_eq_exp h hh β ν ε R g A (toSites Φ)]
  have hK : (fun g : Torus d (s * m) → Fin N → ℂ =>
      mayerGenK (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
        (fun X : NePoly (Torus d m) => X.1) (frFX h hh β ν ε R g) Y) =
      fun g => ∑ C ∈ Cfam (fun X : NePoly (Torus d m) => X.1) (fun _ => True) Y.1,
        ∑ 𝒳 ∈ C.powerset, (-1 : ℂ) ^ (C \ 𝒳).card *
          ∫ Φ, ∏ t ∈ frTT (s := s) R 𝒳, frF h hh β ν ε R g t (toSites Φ)
            ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) := by
    funext g
    unfold mayerGenK mayerGenAct polyAct
    rw [integral_finsetSum _ fun C _ => ?_]
    · refine Finset.sum_congr rfl fun C _ => ?_
      simp_rw [prod_frFX_eq h hh β ν ε R g C]
      rw [integral_finsetSum _ fun 𝒳 _ => (hintA g _).const_mul _]
      exact Finset.sum_congr rfl fun 𝒳 _ => integral_const_mul _ _
    · simp_rw [prod_frFX_eq h hh β ν ε R g C]
      exact integrable_finsetSum _ fun 𝒳 _ => (hintA g _).const_mul _
  rw [hK]
  exact Finset.analyticOnNhd_fun_sum _ fun C _ => Finset.analyticOnNhd_fun_sum _ fun 𝒳 _ =>
    analyticOnNhd_const.mul (analyticOnNhd_integral_prod_frF h hh hε R hint0 _)

end

end Balaban.LargeField.KF0FR
