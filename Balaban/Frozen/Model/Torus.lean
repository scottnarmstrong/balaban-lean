module

public import Mathlib.Data.ZMod.Defs

/-!
# The discrete torus

Def-1 (model). The lattice of the finite-volume model: the discrete torus `(ℤ/ℓℤ)^d` with
periodic boundary conditions (P1 p. 103; P9 p. 494). Cubic tori of every side `ℓ` are allowed;
the theorems state which sides they use.
-/

@[expose] public section

namespace Balaban

/-- The discrete torus `(ℤ/ℓℤ)^d`. -/
abbrev Torus (d ℓ : ℕ) : Type := Fin d → ZMod ℓ

end Balaban
