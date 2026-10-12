/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.ImprovedConst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 3.4: the decomposition (2.23) and the first bound (corrected form)

OBSERVABLES.md §3.4, P9 pp. 498-501.  `improved_first_of_slice` is the first bound (2.21), in the
corrected form (see `ImprovedBound.lean`: the subtrahend is the value at a constant *unit*
configuration `(v, v)`), assembled from

* the decomposition (2.23) `M(Ψ, h) = M(constFld c, h) + δ_y M`, `c = Ψ(y)`, with the Cauchy estimate
  and the case split on the slice `t ↦ (c + t (Ψ - c), h)` (`improved_delta_bound`);
* a bound of the *constant part* `M(constFld c, h) - M(constFld v, constFld v)`, which is the
  `b`-form of §3.4.

**The geometric premise.**  `hslice` is the statement that the slice `t ↦ (constFld c + t (Ψ - constFld c), h)`
stays in `Ξ^c_j(𝔹_j(X); 1, ε_j)` for `|t| < r₀ = Rad / (c (1 + d_j(X)/(2L)) σε)` whenever `d_j(X) ≤
c'/(σε)`: P9 p. 499, "by Lemmas 2.3, 2.7, 2.8 of [1] this function is analytic on `Ψ^c_j(σ, ε)`" (the
path bound `|Ψ(x) - Ψ(y)| ≤ c (1 + d_j(X)) σε` of P1 (3.54) and the scaling of the domains).  It is a
hypothesis of this lemma about points, **not a hypothesis of a source-facing theorem**: the geometry
of the domains `Ψ^c_j(σ, ε)` is not in Lean (`XiDom` is the case `σ = 1`), so Lemma 3.4 as stated in
P9 is not assembled here; see OBSERVABLES §7.4, row O6.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Lemma

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {j : ℕ}

/-- **The first bound of Lemma 3.4 (2.21), corrected form, from the slice and the constant part.**

For a polymer `X ∈ 𝒟_j` with `x ∈ X`, a point `(Ψ, h)` of the domain, a constant `c ∈ ℂ^N` (the value
of `Ψ` at the site `y`) with `(constFld c, h)` in the domain, and a real unit vector `v`:
if (small polymers, `d_j(X) ≤ c'/s`, `s = σε`) the slice `t ↦ (c + t (Ψ - c), h)` lies in the domain
for `|t| < r₀ = Rad / (c₁ (1 + d_j(X)/(2L)) s)`, and the constant part is bounded,
`|M(c, h) - M(v, v)| ≤ b_c`, then
`|M(x, X; Ψ, h) - M(x, X; v, v)| ≤ C (β^{-1/2+ρ₁} L^{-jρ₀}) s e^{-(κ-1) d_j(X)} + b_c`,
`C = improvedConst c₁ Rad c'`. -/
theorem improved_first_of_slice (hO : IsObs P Q β ν a Tm Ot Gker) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (Ψ h : Fld d L N₁ m₁ k N) (c : Fin N → ℂ) (v : Fin N → ℝ) (hβ0 : 0 < β 0)
    {s c₁ Rad c' bc : ℝ} (hs : 0 < s) (hc₁ : 0 < c₁) (hRad : 0 < Rad) (hc' : 0 < c')
    (hL : (1 : ℝ) / 2 ≤ L) (hD : 0 ≤ sizeJ P.m₀ j X)
    (hΨ : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h)
    (hc0 : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld c) h)
    (hslice : sizeJ P.m₀ j X ≤ c' / s → ∀ t : ℂ,
      ‖t‖ < Rad / (c₁ * (1 + sizeJ P.m₀ j X / (2 * (L : ℝ))) * s) →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (constFld c + t • (Ψ - constFld c)) h)
    (hconst : vn (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
      (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst c₁ Rad c' * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set A : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB := fun (p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)
    (hp : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) p.1 p.2) =>
    hO.boundM j hj1 hjk x X hX hx p.1 p.2 hp
  -- the slice function and its values at `0` and `1`
  set Gs : ℂ → Fin N → ℂ := fun t => Ot.M j x X (constFld c + t • (Ψ - constFld c)) h with hGs
  have e1 : constFld c + (1 : ℂ) • (Ψ - constFld c) = Ψ := by
    funext z i; simp [constFld]
  have e0 : constFld c + (0 : ℂ) • (Ψ - constFld c) = constFld c := by simp
  have hG1 : Gs 1 = Ot.M j x X Ψ h := by simp only [hGs, e1]
  have hG0 : Gs 0 = Ot.M j x X (constFld c) h := by simp only [hGs, e0]
  set G' : ℂ → EuclideanSpace ℂ (Fin N) := fun t => WithLp.toLp 2 (Gs t) with hG'
  have hnorm : ∀ t, ‖G' t‖ = vn (Gs t) := fun t => rfl
  have hBv : vn (Ot.M j x X Ψ h) ≤ A * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
    hO.boundM j hj1 hjk x X hX hx Ψ h hΨ
  have hBc : vn (Ot.M j x X (constFld c) h) ≤ A * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
    hO.boundM j hj1 hjk x X hX hx _ h hc0
  have hdelta := improved_delta_bound (G := G') (A := A) (κ := P.κ) (D := sizeJ P.m₀ j X) (s := s)
    (L := (L : ℝ)) (c := c₁) (Rad := Rad) (c' := c') hA0 hD hs hL hc₁ hRad hc'
    (by rw [hnorm, hG1]; exact hBv) (by rw [hnorm, hG0]; exact hBc)
    (by
      intro hsm
      set r : ℝ := Rad / (c₁ * (1 + sizeJ P.m₀ j X / (2 * (L : ℝ))) * s) with hr
      have hmem := hslice hsm
      refine ⟨?_, ?_⟩
      · have hd : DifferentiableOn ℂ Gs (ball 0 r) := by
          intro t ht
          have h1 := hO.analyticM j hj1 hjk x X hX hx
            (constFld c + t • (Ψ - constFld c), h) (hmem t (mem_ball_zero_iff.1 ht))
          have h2 : AnalyticAt ℂ (fun u : ℂ => ((constFld c + u • (Ψ - constFld c) :
              Fld d L N₁ m₁ k N), (h : Fld d L N₁ m₁ k N))) t :=
            (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).prod analyticAt_const
          exact (AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
            Ot.M j x X p.1 p.2) (f := fun u : ℂ => ((constFld c + u • (Ψ - constFld c) :
              Fld d L N₁ m₁ k N), (h : Fld d L N₁ m₁ k N))) h1 h2).differentiableAt.differentiableWithinAt
        exact (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiable.comp_differentiableOn hd
      · intro t ht
        rw [hnorm]
        exact hO.boundM j hj1 hjk x X hX hx _ h (hmem t ht))
  have hd2 : vn (Gs 1 - Gs 0) ≤ improvedConst c₁ Rad c' * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) := by
    have e : G' 1 - G' 0 = WithLp.toLp 2 (Gs 1 - Gs 0) := rfl
    rw [e] at hdelta
    exact hdelta
  rw [hG1, hG0] at hd2
  have htri : vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld c) h) +
      vn (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) := by
    have e : Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ))) =
        (Ot.M j x X Ψ h - Ot.M j x X (constFld c) h) +
        (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ)))) := by abel
    rw [e]
    exact vn_add' _ _
  linarith

end Lemma

end Balaban.Observables
