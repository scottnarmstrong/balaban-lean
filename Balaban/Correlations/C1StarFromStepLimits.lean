/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.C1StarLimits

/-!
# Limits of a physical remainder assembled from scale terms

The physical input is the identity with its scale-resolved summands and a summable
uniform majorant. The two limits then follow from the landed Tannery criterion.
-/

@[expose] public section

namespace Balaban.Correlations

open Filter Topology

/-- An explicitly decomposed physical remainder has both the thermodynamic limit
along all divisible tori and the right limit as the field tends to zero. The
per-scale torus limits and right continuity are the step inputs. -/
theorem remainder_limits_of_scale_steps (q : ℕ) (hq : 1 ≤ q)
    (r : ℕ → ℝ → ℝ) (u : ℕ → ℕ → ℝ → ℝ)
    (v : ℕ → ℝ → ℝ) (v0 b : ℕ → ℝ)
    (hrepr : ∀ ℓ ν, r ℓ ν = ∑' j, u j ℓ ν)
    (hb0 : ∀ j, 0 ≤ b j) (hb : Summable b)
    (hu : ∀ j ℓ ν, ν ∈ Set.Ioc (0 : ℝ) 1 → |u j ℓ ν| ≤ b j)
    (ht : ∀ j ν, ν ∈ Set.Ioc (0 : ℝ) 1 →
      LimAlong q (fun ℓ _ => u j ℓ ν) (v j ν))
    (h0 : ∀ j, Tendsto (v j) (𝓝[>] (0 : ℝ)) (𝓝 (v0 j))) :
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      LimAlong q (fun ℓ _ => r ℓ ν) (∑' j, v j ν)) ∧
      Tendsto (fun ν => ∑' j, v j ν) (𝓝[>] (0 : ℝ)) (𝓝 (∑' j, v0 j)) := by
  obtain ⟨hlim, hzero⟩ :=
    c1Star_remainder_limit_criterion q hq u v v0 b hb0 hb hu ht h0
  refine ⟨?_, hzero⟩
  intro ν hν
  simpa only [hrepr] using hlim ν hν

end Balaban.Correlations
