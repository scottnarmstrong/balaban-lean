/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedCubicJoint
public import Balaban.Fluctuation.ObsRayBase

/-!
# Analyticity of the first-order direct term in a parameter, and along the complex hat ray

The observable exponent is evaluated along the ray `r ↦ r ψ̂` in the hat field, so the direct terms
must be holomorphic in a complex parameter `z` that scales the hat pair.  The landed analytic
families vary the datum and the ray-integral variable at a fixed hat pair; this file supplies the
parameter versions for the two kinds of building blocks of the sharp direct terms:

* `analyticOnNhd_dirTerm_param`: the first-order term `dirTerm Ev ω (x₀ q) (w q) 1 (Θ q)` is analytic
  in a parameter `q` (the analogue of `analyticOnNhd_rayTerm_dl3_param` for the first derivative);
* `differentiableOn_dirTerm_ray`, `differentiableOn_rayTerm_dl3_ray`: along the diagonal complex ray
  `z ↦ (z ψ̂, z ψ̂)` at a constant datum, for the linear source term and the cubic potential term.

Nothing here asserts an activity, a label statement or an identity with the physical exponent.
-/

@[expose] public section

namespace Balaban.Fluctuation

end Balaban.Fluctuation
