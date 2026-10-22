/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6
public import Balaban.Flow.RGEquations

/-!
# The renormalization conditions (H.5) of the new level from a solution of the counterterm system

The counterterm system of a step (`Balaban.Flow.rg_step_infty`) is `A ξ + c(ξ) = f(ξ)` for the
unknown `ξ = (ξ₁, ξ₂, ξ₃)`; its three rows are the first-order conditions of (H.5) on the terms
`Tm'` of the new level, divided by the scale factors `Λ = (β ε, β, β)` (`SMALLFIELD.md` §3.2, §3.4):

* row `1`: (E1), the derivative of `ℰ_∞(0; ψ, h)` along the constant field direction (`dpsi`);
* row `2`: (E2), the derivative in the external field `h` (`dh`);
* row `3`: (E3), the second moment (`moment`).

`renormCondAlong_of_system` is the bridge: when the relevant parts of the terms `Tm'` equal the scale
factors times the residual `A ξ + c - f` of the system (the identities of the construction of `Tm'`
from the unrenormalized terms and the counterterms), and `ξ` solves the system, and the vacuum
constant is chosen so that the value vanishes, then `Tm'` satisfies `RenormCondAlong`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Filter Topology Balaban

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The bridge from the counterterm system to (H.5).**  `Tm'` are the terms of the new level (scale
`j = k`), `A ξ + c = f` is the system at its solution `ξ` (the output of `rg_step_infty`, with `A, c, f`
evaluated at the data of the construction), `Λ` the scale factors of the rows.

The hypotheses `hpsi`, `hh`, `hmom` are the identities of the construction: the derivative of the
density along the constant field, the derivative in `h`, and the limit of the second moments along the
tori `idx n` are `Λ_i` times the `i`-th residual of the system; `hval` states that the vacuum constant of
the step is the value of the density at the constant field.  The conclusion is `RenormCondAlong`. -/
theorem renormCondAlong_of_system (m₀ : ℕ) (νk : ℝ)
    (Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (idx : ℕ → ℕ)
    (hidx : ∀ n, idx n ≠ 0)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (ξ c f Λ : Fin 3 → ℂ) (hsys : A.mulVec ξ + c = f)
    (hval : ∀ i₀ : Fin N,
      ElocInf m₀ Tm' j 0 (constInf (Pi.single i₀ 1)) (constInf (Pi.single i₀ 1)) = 0)
    (hpsi : ∀ i₀ : Fin N,
      deriv (fun t : ℂ => ElocInf m₀ Tm' j 0
        (constInf ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ))) (constInf (Pi.single i₀ 1))) 0 =
        Λ 0 * (A.mulVec ξ + c - f) 0)
    (hh : ∀ i₀ : Fin N, 0 < nuIdeal L k νk j →
      fderiv ℂ (fun h : Fin N → ℂ => ElocInf m₀ Tm' j 0 (constInf (Pi.single i₀ 1)) (constInf h))
        (Pi.single i₀ 1) (Pi.single i₀ 1) = Λ 1 * (A.mulVec ξ + c - f) 1)
    (hmom : ∀ i₀ i₁ : Fin N, i₀ ≠ i₁ →
      Tendsto (fun n : ℕ => haveI : NeZero (idx n) := ⟨hidx n⟩
        momentSum m₀ (Tm' (idx n)) j i₀ i₁) atTop (𝓝 (Λ 2 * (A.mulVec ξ + c - f) 2))) :
    RenormCondAlong m₀ k νk Tm' j idx hidx := by
  have h0 : A.mulVec ξ + c - f = 0 := sub_eq_zero.mpr hsys
  refine ⟨hval, fun i₀ hν => ?_, fun i₀ => ?_, fun i₀ i₁ hne => ?_⟩
  · rw [hh i₀ hν, h0]; simp
  · rw [hpsi i₀, h0]; simp
  · have := hmom i₀ i₁ hne
    rw [h0] at this; simpa using this

end Balaban.SmallField.Def6
