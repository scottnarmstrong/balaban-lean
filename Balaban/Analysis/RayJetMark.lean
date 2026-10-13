/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.RayJetReal

/-!
# The first-order Taylor remainder of a mark, for a function on a complex vector space

If `V` is analytic at `0` and its real rays `r ↦ V (r v)` have vanishing first and second
derivatives at `0` along every `v = u a + t b`, then for `g (u, t) = V (u a + t b)` and any
quadratic polynomial `A u² + C u t + D t²` the first-order Taylor remainder of
`u ↦ ∂ₜ (g + q) (u, 0)` is `∂ₜ g (u, 0)` (`mark_taylor1_add_of_real_rays`).  This is the
core shared by the fibre and the free-datum comparisons of the mark.
-/

@[expose] public section

namespace Balaban

open Filter Topology

theorem mark_taylor1_add_of_real_rays {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : E → ℂ) (a b : E) (hV : AnalyticAt ℂ V 0)
    (h1 : ∀ w : ℂ × ℂ, deriv (fun r : ℝ => V ((r : ℂ) • (w.1 • a + w.2 • b))) 0 = 0)
    (h2 : ∀ w : ℂ × ℂ, deriv (deriv (fun r : ℝ => V ((r : ℂ) • (w.1 • a + w.2 • b)))) 0 = 0)
    (A C D u : ℂ) (hu : DifferentiableAt ℂ (fun t : ℂ => V (u • a + t • b)) 0) :
    let g : ℂ × ℂ → ℂ := fun w => V (w.1 • a + w.2 • b)
    deriv (fun t : ℂ => g (u, t) + (A * u ^ 2 + C * u * t + D * t ^ 2)) 0 -
      deriv (fun t : ℂ => g (0, t) + (A * (0 : ℂ) ^ 2 + C * 0 * t + D * t ^ 2)) 0 -
      u * deriv (fun u' : ℂ => deriv (fun t : ℂ => g (u', t) +
        (A * u' ^ 2 + C * u' * t + D * t ^ 2)) 0) 0 =
      deriv (fun t : ℂ => g (u, t)) 0 := by
  intro g
  have hlin : AnalyticAt ℂ (fun w : ℂ × ℂ => w.1 • a + w.2 • b) 0 :=
    (analyticAt_fst.smul analyticAt_const).add (analyticAt_snd.smul analyticAt_const)
  have hg : AnalyticAt ℂ g 0 := hV.comp_of_eq hlin (by simp)
  have hray : ∀ w : ℂ × ℂ, (fun r : ℝ => g ((r : ℂ) • w)) =
      fun r : ℝ => V ((r : ℂ) • (w.1 • a + w.2 • b)) := by
    intro w; funext r
    simp [g, Prod.smul_def, smul_add, smul_smul]
  obtain ⟨k1, k2⟩ := rayJet_pair_of_real g hg
    (fun w => by rw [hray]; exact h1 w) (fun w => by rw [hray]; exact h2 w)
  exact mark_taylor1_add g hg k1 k2 A C D u hu

end Balaban
