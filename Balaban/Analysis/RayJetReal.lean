/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.RayJetTwo
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real ray jets of an analytic function are complex ray jets

If `φ : ℂ → ℂ` is analytic at `0` and its restriction to the real axis has vanishing first and
second derivative at `0`, then so does `φ` itself (`deriv_vanish_of_real`).  Applied to
`l ↦ G (l • v)` this turns the real ray derivatives of an analytic function into complex ray
derivatives (`complex_rayJet_of_real_rayJet`), and in two variables gives exactly the hypotheses
of `mark_taylor1_of_rayJet_vanish` (`rayJet_pair_of_real`).
-/

@[expose] public section

namespace Balaban

open Filter Topology

/-- For `φ` analytic at `0`, vanishing first and second derivatives along the real axis give
vanishing complex first and second derivatives at `0`. -/
theorem deriv_vanish_of_real (φ : ℂ → ℂ) (hφ : AnalyticAt ℂ φ 0)
    (h1 : deriv (fun s : ℝ => φ (s : ℂ)) 0 = 0)
    (h2 : deriv (deriv (fun s : ℝ => φ (s : ℂ))) 0 = 0) :
    deriv φ 0 = 0 ∧ deriv (deriv φ) 0 = 0 := by
  have hd : DifferentiableAt ℂ φ 0 := hφ.differentiableAt
  have hd' : DifferentiableAt ℂ (deriv φ) 0 := hφ.deriv.differentiableAt
  have e1 : deriv (fun s : ℝ => φ (s : ℂ)) 0 = deriv φ 0 := by
    have := (HasDerivAt.comp_ofReal (z := (0 : ℝ)) hd.hasDerivAt)
    exact this.deriv
  have hev : ∀ᶠ s : ℝ in 𝓝 0, deriv (fun s : ℝ => φ (s : ℂ)) s = deriv φ (s : ℂ) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa using Complex.continuous_ofReal.tendsto 0
    filter_upwards [hc.eventually hφ.eventually_analyticAt] with s hs
    exact (HasDerivAt.comp_ofReal (z := s) hs.differentiableAt.hasDerivAt).deriv
  have e2 : deriv (deriv (fun s : ℝ => φ (s : ℂ))) 0 = deriv (deriv φ) 0 := by
    rw [Filter.EventuallyEq.deriv_eq hev]
    exact (HasDerivAt.comp_ofReal (z := (0 : ℝ)) hd'.hasDerivAt).deriv
  exact ⟨e1.symm.trans h1, e2.symm.trans h2⟩

/-- **T1 (general form).**  `G` analytic at `0` on a complex normed space: vanishing real ray
derivatives of order one and two in every direction give the same for complex rays. -/
theorem complex_rayJet_of_real_rayJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : E → ℂ) (hG : AnalyticAt ℂ G 0)
    (h1 : ∀ v : E, deriv (fun s : ℝ => G ((s : ℂ) • v)) 0 = 0)
    (h2 : ∀ v : E, deriv (deriv (fun s : ℝ => G ((s : ℂ) • v))) 0 = 0) (v : E) :
    deriv (fun l : ℂ => G (l • v)) 0 = 0 ∧ deriv (deriv (fun l : ℂ => G (l • v))) 0 = 0 := by
  have hφ : AnalyticAt ℂ (fun l : ℂ => G (l • v)) 0 := by
    have hl : AnalyticAt ℂ (fun l : ℂ => l • v) 0 := analyticAt_id.smul analyticAt_const
    exact hG.comp_of_eq hl (by simp)
  exact deriv_vanish_of_real _ hφ (h1 v) (h2 v)

/-- **T1 (two variables).**  The hypotheses `h1 h2` of `mark_taylor1_of_rayJet_vanish`, from
vanishing real ray derivatives of an analytic `g : ℂ × ℂ → ℂ`. -/
theorem rayJet_pair_of_real (g : ℂ × ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (h1 : ∀ w : ℂ × ℂ, deriv (fun s : ℝ => g ((s : ℂ) • w)) 0 = 0)
    (h2 : ∀ w : ℂ × ℂ, deriv (deriv (fun s : ℝ => g ((s : ℂ) • w))) 0 = 0) :
    (∀ u t : ℂ, deriv (fun l : ℂ => g (l * u, l * t)) 0 = 0) ∧
      ∀ u t : ℂ, deriv (deriv (fun l : ℂ => g (l * u, l * t))) 0 = 0 := by
  have e : ∀ u t : ℂ, (fun l : ℂ => g (l * u, l * t)) = fun l : ℂ => g (l • (u, t)) := by
    intro u t; ext l; simp [Prod.smul_def]
  refine ⟨fun u t => ?_, fun u t => ?_⟩
  · rw [e]; exact (complex_rayJet_of_real_rayJet g hg h1 h2 (u, t)).1
  · rw [e]; exact (complex_rayJet_of_real_rayJet g hg h1 h2 (u, t)).2

end Balaban
