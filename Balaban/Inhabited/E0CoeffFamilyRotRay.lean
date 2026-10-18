/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir3
public import Balaban.Fluctuation.InteractionDir

/-!
# Transport of the ray terms under a symmetry of the expanded term, without analyticity

`rayTerm_dl3_equiv_of_invariant`: if `Ev (fΛ Θ, fF z) = Ev (Θ, z)` for the points `z` on the lines
through the ray, with `fF` additive and homogeneous, then the ray term of the third directional
derivative of `Ev` is transported: `rayTerm (dl3 Ev (fF w)) ω (fF x₀) σ (fΛ Θ) =
rayTerm (dl3 Ev w) ω x₀ σ Θ`.  Only the values of `Ev` along the lines enter, so no analyticity of
`Ev` is needed (compare `rayTerm_dl3_equiv`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section Ray

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Iterated directional derivatives are transported along a line by a map that is affine on it. -/
theorem lineD_iterate_transport (A : E → E) (v v' p : E) {r : ℝ}
    (hA : ∀ τ : ℂ, A (p + τ • v) = A p + τ • v') :
    ∀ (n : ℕ) (f f' : E → ℂ),
      (∀ τ : ℂ, ‖τ‖ < r → f (A (p + τ • v)) = f' (p + τ • v)) →
      ∀ τ : ℂ, ‖τ‖ < r → (lineD v')^[n] f (A (p + τ • v)) = (lineD v)^[n] f' (p + τ • v) := by
  intro n
  induction n with
  | zero => intro f f' h τ hτ; exact h τ hτ
  | succ n ih =>
    intro f f' h τ hτ
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ih (lineD v' f) (lineD v f') (fun τ' hτ' => ?_) τ hτ
    unfold lineD
    have hev : (fun t : ℂ => f (A (p + τ' • v) + t • v')) =ᶠ[nhds 0]
        fun t : ℂ => f' (p + τ' • v + t • v) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (sub_pos.2 hτ' : 0 < r - ‖τ'‖)] with t ht
      have ht' : ‖t‖ < r - ‖τ'‖ := by simpa using ht
      have h1 : ‖τ' + t‖ < r := by
        have := norm_add_le τ' t
        linarith
      have e1 : A (p + τ' • v) + t • v' = A (p + (τ' + t) • v) := by
        rw [hA, hA, add_smul, add_assoc]
      have e2 : p + τ' • v + t • v = p + (τ' + t) • v := by rw [add_smul, add_assoc]
      rw [e1, e2]
      exact h (τ' + t) h1
    exact hev.deriv_eq

end Ray

section RayTerm

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Transport of the ray terms under a symmetry of `Ev`, without analyticity.** -/
theorem rayTerm_dl3_equiv_of_invariant {B : Set F} {Ev : Λ × F → ℂ} (fΛ : Λ → Λ) (fF : F → F)
    (hadd : ∀ x y, fF (x + y) = fF x + fF y) (hsm : ∀ (c : ℂ) x, fF (c • x) = c • fF x)
    {Θ : Λ} (hinv : ∀ z ∈ B, Ev (fΛ Θ, fF z) = Ev (Θ, z))
    {ω : ℂ → ℂ} {x₀ w : F} {σ : ℂ} {r : ℝ} (hr : 0 < r)
    (hline : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ B) :
    rayTerm (dl3 Ev (fF w)) ω (fF x₀) σ (fΛ Θ) = rayTerm (dl3 Ev w) ω x₀ σ Θ := by
  unfold rayTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  congr 1
  have hz := hline t ht
  have h1 : (σ * (t : ℂ)) • fF x₀ = fF ((σ * (t : ℂ)) • x₀) := (hsm _ _).symm
  rw [h1, dl3_apply, dl3_apply]
  have hA : ∀ τ : ℂ,
      (fun q : Λ × F => ((fΛ q.1, fF q.2) : Λ × F)) (((Θ, (σ * (t : ℂ)) • x₀) : Λ × F) +
        τ • ((0 : Λ), w)) =
      (fun q : Λ × F => ((fΛ q.1, fF q.2) : Λ × F)) ((Θ, (σ * (t : ℂ)) • x₀) : Λ × F) +
        τ • ((0 : Λ), fF w) := by
    intro τ
    simp only [Prod.mk_add_mk, Prod.smul_mk, add_zero, smul_zero, hadd, hsm]
  have key := lineD_iterate_transport (fun q : Λ × F => ((fΛ q.1, fF q.2) : Λ × F))
    ((0 : Λ), w) ((0 : Λ), fF w) (Θ, (σ * (t : ℂ)) • x₀) (r := r) hA 3 Ev Ev
    (fun τ hτ => by
      have := hinv _ (hz τ hτ.le)
      simpa [hadd, hsm] using this) 0 (by simpa using hr)
  simpa [dirL3, Function.iterate_succ, hsm, dl3] using key

end RayTerm

end Balaban.Fluctuation
