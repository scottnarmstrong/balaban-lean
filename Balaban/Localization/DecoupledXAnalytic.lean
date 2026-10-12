/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledXGrad
public import Balaban.Localization.DecoupledAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (DG4): analyticity of `G_{k,x,s}(A)` in `(s, A)`

Every entry of `G_{k,x,s}(A)` is analytic in `(s, A)` on the polydisc `|s_P| < e^{κ}`,
`|A| < γ₁ ℓ⁻²` (`dg4x_analytic`), for every `x ≥ 0`: finite sums, products and the inverse of
operators with non-zero determinant (the cube operators `H_{k,x,z}(A)` are affine in `A`; the
determinant of `1 - 𝒦_{x,s}(A)` does not vanish by `XData.isUnit_one_sub`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}

theorem cutXOperator_eq_add (a : ℕ → ℝ) (aT x ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    cutXOperator G a aT x ν cut α = cutXOperator G a aT x ν cut 0 + Matrix.diagonal α := by
  unfold cutXOperator
  simp

theorem matAt_cubeHx (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (e : DecParams G × (G.Ω 1 → ℂ)) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => cubeHx G a aT x ν p.2 q) e := by
  have : (fun p : DecParams G × (G.Ω 1 → ℂ) => cubeHx G a aT x ν p.2 q) =
      fun p => cubeHx G a aT x ν 0 q + Matrix.diagonal p.2 := by
    funext p; exact cutXOperator_eq_add a aT x ν _ p.2
  rw [this]
  refine MatAt.add (MatAt.const _ e) ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : G.Ω 1 => ℂ) i).analyticAt _).comp
      analyticAt_snd
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact analyticAt_const

theorem matAt_cubeGx (S : XSetting G a aT ν) (hx : 0 ≤ x) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) {e : DecParams G × (G.Ω 1 → ℂ)} (hα : AdmPot G e.2) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => cubeGx G a aT x ν p.2 q) e := by
  unfold cubeGx
  refine MatAt.mul (MatAt.inv (matAt_cubeHx q e) ?_) (MatAt.const _ e)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (cubeHx_isUnit S hα hx hq)).ne_zero

theorem matAt_Kcalx (S : XSetting G a aT ν) (hx : 0 ≤ x) {e : DecParams G × (G.Ω 1 → ℂ)}
    (hα : AdmPot G e.2) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Kcalx G a aT x ν p.2 (extS G p.1)) e := by
  unfold Kcalx
  refine MatAt.sum _ fun q hq => ?_
  exact MatAt.smul (analyticAt_sProd q e) (MatAt.mul (MatAt.const _ e) (matAt_cubeGx S hx hq hα))

theorem matAt_Gstarx (S : XSetting G a aT ν) (hx : 0 ≤ x) {e : DecParams G × (G.Ω 1 → ℂ)}
    (hα : AdmPot G e.2) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Gstarx G a aT x ν p.2 (extS G p.1)) e := by
  unfold Gstarx
  refine MatAt.sum _ fun q hq => ?_
  exact MatAt.smul (analyticAt_sProd q e) (MatAt.mul (MatAt.const _ e) (matAt_cubeGx S hx hq hα))

theorem matAt_Gsx (S : XSetting G a aT ν) (hx : 0 ≤ x) {e : DecParams G × (G.Ω 1 → ℂ)}
    (hα : AdmPot G e.2) (hU : IsUnit (1 - Kcalx G a aT x ν e.2 (extS G e.1))) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Gsx G a aT x ν p.2 (extS G p.1)) e := by
  unfold Gsx
  refine MatAt.mul (matAt_Gstarx S hx hα)
    (MatAt.inv (MatAt.sub (MatAt.const _ e) (matAt_Kcalx S hx hα)) ?_)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero

/-- **(DG4), analyticity**: every entry of `G_{k,x,s}(A)` is analytic in `(s, A)` on the polydisc
`|s_P| < e^{κ}`, `|A(z)| < c₁ ℓ(z)⁻² / 2`, uniformly in `x ≥ 0`. -/
theorem dg4x_analytic (S : XSetting G a aT ν) (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (y z : G.Ω 1) :
    AnalyticOnNhd ℂ
      (fun p : DecParams G × (G.Ω 1 → ℂ) => Gsx G a aT x ν p.2 (extS G p.1) y z)
      {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
        ∀ w, ‖p.2 w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)} := by
  intro e he
  have hα : AdmPot G e.2 := fun w => (he.2 w).le
  have hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  have D : XData G a aT ν x e.2 κ (extS G e.1) := ⟨S, hα, hx, hκ, hM, hs⟩
  exact matAt_Gsx S hx hα D.isUnit_one_sub y z

end Balaban.Localization
