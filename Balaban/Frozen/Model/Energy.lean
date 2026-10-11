module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic

/-!
# The energy of the hard-spin model

Def-1 (model). P9 (1.1) (p. 493) and P1 (1.5)–(1.6) (p. 104) at `λ = ∞`:
`H(φ) = ½ ‖∂φ‖² + (ν/2) ‖φ - h‖²`, where `‖∂φ‖²` sums `|φ(x + e_μ) - φ(x)|²` over the
nearest-neighbour bonds of the torus (each bond once when `ℓ ≥ 3`), `ν` is the strength of the
external field and `h` its direction. The Gibbs factor is `exp(-β H(φ))`.
-/

@[expose] public section

namespace Balaban

/-- `H(φ) = ½ ∑_x ∑_μ |φ(x + e_μ) - φ(x)|² + (ν/2) ∑_x |φ(x) - h|²`. -/
noncomputable def energy (d N ℓ : ℕ) [NeZero ℓ] (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      ‖(φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2
    + (ν / 2) * ∑ x : Torus d ℓ, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2

end Balaban
