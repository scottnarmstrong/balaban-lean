/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Complex.Basic

/-!
# Vanishing ray jets of order two and the first-order Taylor remainder of a mark

If `g : ℂ × ℂ → ℂ` is analytic at `0` and `λ ↦ g (λ u, λ t)` has value, first and second
derivative `0` at `λ = 0` for every direction `(u, t)`, then `F u = ∂ₜ g (u, t)|ₜ₌₀` satisfies
`F 0 = 0` and `F' 0 = 0` (`mark_taylor1_of_rayJet_vanish`).  For a homogeneous quadratic
polynomial `q`, `∂ₜ q (u, 0) = C u` is linear in `u` (`mark_taylor1_quadratic`), and the two
combine for `e = g + q` (`mark_taylor1_add`).
-/

@[expose] public section

namespace Balaban

open Filter Topology

private lemma ray_hasDerivAt (g : ℂ × ℂ → ℂ) (w : ℂ × ℂ) {x : ℂ × ℂ} (l : ℂ)
    (hg : DifferentiableAt ℂ g (l • w)) (_hx : x = l • w) :
    HasDerivAt (fun l : ℂ => g (l • w)) (fderiv ℂ g (l • w) w) l := by
  have h1 : HasDerivAt (fun l : ℂ => l • w) ((1 : ℂ) • w) l := (hasDerivAt_id l).smul_const w
  have h2 := hg.hasFDerivAt.comp_hasDerivAt l h1
  rw [one_smul] at h2
  exact h2

/-- First and second ray derivatives at `0` of an analytic function. -/
private lemma ray_jets (g : ℂ × ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (w : ℂ × ℂ) :
    deriv (fun l : ℂ => g (l • w)) 0 = fderiv ℂ g 0 w ∧
    deriv (deriv (fun l : ℂ => g (l • w))) 0 = fderiv ℂ (fderiv ℂ g) 0 w w := by
  have hev : ∀ᶠ y in nhds (0 : ℂ × ℂ), DifferentiableAt ℂ g y := hg.eventually_analyticAt.mono
    fun y hy => hy.differentiableAt
  have hcont : Continuous (fun l : ℂ => l • w) := by fun_prop
  have hev' : ∀ᶠ l in nhds (0 : ℂ), DifferentiableAt ℂ g (l • w) := by
    have : Tendsto (fun l : ℂ => l • w) (nhds 0) (nhds 0) := by simpa using hcont.tendsto 0
    exact this.eventually hev
  have hd : ∀ᶠ l in nhds (0 : ℂ), deriv (fun l : ℂ => g (l • w)) l = fderiv ℂ g (l • w) w :=
    hev'.mono fun l hl => (ray_hasDerivAt g w l hl rfl).deriv
  refine ⟨?_, ?_⟩
  · have := (ray_hasDerivAt g w 0 (by simpa using hev'.self_of_nhds) rfl).deriv
    simpa using this
  · rw [Filter.EventuallyEq.deriv_eq hd]
    have hfd : DifferentiableAt ℂ (fderiv ℂ g) 0 := hg.fderiv.differentiableAt
    have h1 : HasDerivAt (fun l : ℂ => l • w) ((1 : ℂ) • w) 0 := (hasDerivAt_id (0 : ℂ)).smul_const w
    have h2 : HasDerivAt (fun l : ℂ => fderiv ℂ g (l • w)) (fderiv ℂ (fderiv ℂ g) 0 w) 0 := by
      have := (show HasFDerivAt (fderiv ℂ g) _ ((0 : ℂ) • w) by
        simpa using hfd.hasFDerivAt).comp_hasDerivAt (0 : ℂ) h1
      rw [one_smul] at this
      exact this
    have h3 := (ContinuousLinearMap.apply ℂ ℂ w).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
    exact h3.deriv

/-- The `t`-derivative of an analytic function, near `0`, and its derivative in `u`. -/
private lemma partial_facts (g : ℂ × ℂ → ℂ) (hg : AnalyticAt ℂ g 0) :
    (∀ᶠ u in 𝓝 (0 : ℂ),
      HasDerivAt (fun t : ℂ => g (u, t)) (fderiv ℂ g (u, 0) (0, 1)) 0) ∧
    HasDerivAt (fun u : ℂ => fderiv ℂ g (u, 0) (0, 1))
      (fderiv ℂ (fderiv ℂ g) 0 (1, 0) (0, 1)) 0 := by
  have hev : ∀ᶠ y in nhds (0 : ℂ × ℂ), DifferentiableAt ℂ g y := hg.eventually_analyticAt.mono
    fun y hy => hy.differentiableAt
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun u : ℂ => (u, (0 : ℂ))) := by fun_prop
    have ht : Tendsto (fun u : ℂ => (u, (0 : ℂ))) (𝓝 0) (𝓝 0) := by
      exact hcont.tendsto 0
    filter_upwards [ht.eventually hev] with u hu
    have h1 : HasDerivAt (fun t : ℂ => (u, t)) ((0 : ℂ), (1 : ℂ)) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).smul_const ((0 : ℂ), (1 : ℂ))).const_add (u, (0 : ℂ))
      simpa using this
    exact (hu.hasFDerivAt).comp_hasDerivAt (0 : ℂ) h1
  · have hfd : DifferentiableAt ℂ (fderiv ℂ g) 0 := hg.fderiv.differentiableAt
    have h1 : HasDerivAt (fun u : ℂ => (u, (0 : ℂ))) ((1 : ℂ), (0 : ℂ)) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).smul_const ((1 : ℂ), (0 : ℂ))).const_add ((0 : ℂ), (0 : ℂ))
      simpa using this
    have h2 := hfd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) h1 rfl
    exact (ContinuousLinearMap.apply ℂ ℂ ((0 : ℂ), (1 : ℂ))).hasFDerivAt.comp_hasDerivAt
      (0 : ℂ) h2

/-- **T1.**  An analytic function of two variables whose ray jets of order `≤ 2` at `0` vanish in
every direction has `F 0 = 0` and `F' 0 = 0` for `F u = ∂ₜ g (u, t)|ₜ₌₀`. -/
theorem mark_taylor1_of_rayJet_vanish (g : ℂ × ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (h1 : ∀ u t : ℂ, deriv (fun l : ℂ => g (l * u, l * t)) 0 = 0)
    (h2 : ∀ u t : ℂ, deriv (deriv (fun l : ℂ => g (l * u, l * t))) 0 = 0) :
    deriv (fun t : ℂ => g (0, t)) 0 = 0 ∧
      deriv (fun u : ℂ => deriv (fun t : ℂ => g (u, t)) 0) 0 = 0 := by
  have hj : ∀ w : ℂ × ℂ, fderiv ℂ g 0 w = 0 ∧ fderiv ℂ (fderiv ℂ g) 0 w w = 0 := by
    intro w
    have e : (fun l : ℂ => g (l • w)) = fun l : ℂ => g (l * w.1, l * w.2) := by
      ext l; simp [Prod.smul_def]
    have := ray_jets g hg w
    rw [e] at this
    exact ⟨this.1.symm.trans (h1 w.1 w.2), this.2.symm.trans (h2 w.1 w.2)⟩
  set B := fderiv ℂ (fderiv ℂ g) 0 with hB
  have hsymm : ∀ a b : ℂ × ℂ, B a b = B b a := by
    have hc : ContDiffAt ℂ 2 g 0 := (hg.contDiffAt).of_le (by exact_mod_cast le_top)
    have := hc.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    exact fun a b => this a b
  obtain ⟨hF, hFd⟩ := partial_facts g hg
  refine ⟨?_, ?_⟩
  · have := (hF.self_of_nhds).deriv
    simp only [Prod.mk_zero_zero] at this ⊢
    rw [this]; exact (hj _).1
  · have e : (fun u : ℂ => deriv (fun t : ℂ => g (u, t)) 0) =ᶠ[𝓝 0]
        fun u : ℂ => fderiv ℂ g (u, 0) (0, 1) := hF.mono fun u hu => hu.deriv
    rw [e.deriv_eq, hFd.deriv]
    have h4 : (B (1, 0)) (0, 1) = 0 := by
      have a := (hj ((1, 0) + (0, 1))).2
      have b := (hj (1, 0)).2
      have c := (hj (0, 1)).2
      simp only [map_add, add_apply] at a
      rw [hsymm (0, 1) (1, 0)] at a
      linear_combination (a - b - c) / 2
    exact h4

/-- **T2.**  For a homogeneous quadratic polynomial `q`, `∂ₜ q (u, 0) = C u`; hence the
first-order Taylor remainder of `u ↦ ∂ₜ q (u, 0)` vanishes. -/
theorem mark_taylor1_quadratic (A C D : ℂ) (u : ℂ) :
    deriv (fun t : ℂ => A * u ^ 2 + C * u * t + D * t ^ 2) 0 = C * u := by
  have : HasDerivAt (fun t : ℂ => A * u ^ 2 + C * u * t + D * t ^ 2) (C * u) 0 := by
    have h := (((hasDerivAt_const (0:ℂ) (A * u ^ 2)).add
      ((hasDerivAt_id (0:ℂ)).const_mul (C * u))).add (((hasDerivAt_id (0:ℂ)).pow 2).const_mul D))
    exact h.congr_deriv (by simp)
  exact this.deriv

theorem mark_taylor1_quadratic_remainder (A C D : ℂ) :
    ∀ u : ℂ, deriv (fun t : ℂ => A * u ^ 2 + C * u * t + D * t ^ 2) 0 -
        deriv (fun t : ℂ => A * (0:ℂ) ^ 2 + C * 0 * t + D * t ^ 2) 0 -
        u * deriv (fun u' : ℂ => deriv (fun t : ℂ => A * u' ^ 2 + C * u' * t + D * t ^ 2) 0) 0
        = 0 := by
  intro u
  have e : (fun u' : ℂ => deriv (fun t : ℂ => A * u' ^ 2 + C * u' * t + D * t ^ 2) 0)
      = fun u' => C * u' := funext fun u' => mark_taylor1_quadratic A C D u'
  rw [e, mark_taylor1_quadratic, mark_taylor1_quadratic]
  have : deriv (fun u' : ℂ => C * u') 0 = C := by simp
  rw [this]; ring

/-- **T2, corollary.**  For `e = g + q` with `g` as in `mark_taylor1_of_rayJet_vanish`, the
first-order Taylor remainder of `f u = ∂ₜ e (u, t)|ₜ₌₀` is `∂ₜ g (u, t)|ₜ₌₀`. -/
theorem mark_taylor1_add (g : ℂ × ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (h1 : ∀ u t : ℂ, deriv (fun l : ℂ => g (l * u, l * t)) 0 = 0)
    (h2 : ∀ u t : ℂ, deriv (deriv (fun l : ℂ => g (l * u, l * t))) 0 = 0)
    (A C D : ℂ) (u : ℂ) (hu : DifferentiableAt ℂ (fun t : ℂ => g (u, t)) 0) :
    deriv (fun t : ℂ => g (u, t) + (A * u ^ 2 + C * u * t + D * t ^ 2)) 0 -
        deriv (fun t : ℂ => g (0, t) + (A * (0 : ℂ) ^ 2 + C * 0 * t + D * t ^ 2)) 0 -
        u * deriv (fun u' : ℂ => deriv (fun t : ℂ => g (u', t) +
          (A * u' ^ 2 + C * u' * t + D * t ^ 2)) 0) 0
      = deriv (fun t : ℂ => g (u, t)) 0 := by
  obtain ⟨T0, T1⟩ := mark_taylor1_of_rayJet_vanish g hg h1 h2
  obtain ⟨hF, hFd⟩ := partial_facts g hg
  have hq : ∀ u' : ℂ, HasDerivAt (fun t : ℂ => A * u' ^ 2 + C * u' * t + D * t ^ 2) (C * u') 0 := by
    intro u'
    have h := (((hasDerivAt_const (0:ℂ) (A * u' ^ 2)).add
      ((hasDerivAt_id (0:ℂ)).const_mul (C * u'))).add
      (((hasDerivAt_id (0:ℂ)).pow 2).const_mul D))
    exact h.congr_deriv (by simp)
  have hg0 : DifferentiableAt ℂ (fun t : ℂ => g (0, t)) 0 := (hF.self_of_nhds).differentiableAt
  have e0 : deriv (fun t : ℂ => g (0, t) + (A * (0 : ℂ) ^ 2 + C * 0 * t + D * t ^ 2)) 0 =
      deriv (fun t : ℂ => g (0, t)) 0 + C * 0 := (hg0.hasDerivAt.add (hq 0)).deriv
  have eu : deriv (fun t : ℂ => g (u, t) + (A * u ^ 2 + C * u * t + D * t ^ 2)) 0 =
      deriv (fun t : ℂ => g (u, t)) 0 + C * u := (hu.hasDerivAt.add (hq u)).deriv
  have hG : (fun u' : ℂ => deriv (fun t : ℂ => g (u', t) +
          (A * u' ^ 2 + C * u' * t + D * t ^ 2)) 0) =ᶠ[𝓝 0]
      fun u' : ℂ => fderiv ℂ g (u', 0) (0, 1) + C * u' :=
    hF.mono fun u' hu' => (hu'.add (hq u')).deriv
  have hGd : deriv (fun u' : ℂ => fderiv ℂ g (u', 0) (0, 1) + C * u') 0 =
      fderiv ℂ (fderiv ℂ g) 0 (1, 0) (0, 1) + C * 1 :=
    (hFd.add ((hasDerivAt_id (0 : ℂ)).const_mul C)).deriv
  have hdG : deriv (fun u' : ℂ => deriv (fun t : ℂ => g (u', t) +
          (A * u' ^ 2 + C * u' * t + D * t ^ 2)) 0) 0 = deriv (fun u' : ℂ => fderiv ℂ g (u', 0) (0, 1)
          + C * u') 0 := hG.deriv_eq
  have e1 : deriv (fun u : ℂ => deriv (fun t : ℂ => g (u, t)) 0) 0 =
      fderiv ℂ (fderiv ℂ g) 0 (1, 0) (0, 1) := by
    have e : (fun u : ℂ => deriv (fun t : ℂ => g (u, t)) 0) =ᶠ[𝓝 0]
        fun u : ℂ => fderiv ℂ g (u, 0) (0, 1) := hF.mono fun u hu => hu.deriv
    rw [e.deriv_eq, hFd.deriv]
  rw [hdG, hGd, eu, e0, ← e1, T1, T0]
  ring

end Balaban
