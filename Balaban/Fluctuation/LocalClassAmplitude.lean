/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassCentre
public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The amplitude of the new contributions (the source factor `β_k^{-1/2}`)

The new contributions at the level `k + 1` are **differences**: a term evaluated at the
fluctuating field `ψ' = cc · C^{1/2} ψ̂` minus the same term at the background `ψ' = 0`
(P4 (2.35), (2.55); FLUCTUATION (3.3): the interaction carries the amplitude `cc = β_k^{-1/2} σ t'`
and is written by a Cauchy integral in an auxiliary variable on `|τ| = r`).  If the term is
analytic in the amplitude on a disc `|c| < R` and bounded there by `B`, the difference at `cc` is
bounded by `2 B |cc| / R` (Schwarz lemma).  With `|cc| = β_k^{-1/2} |σ|` this is the factor
`β_k^{-1/2} |σ| r⁻¹` of FLUCTUATION Proposition 3.3 (P4 p. 704, decision D3(b)): the bounds of the
new terms do not inherit the constant of the old ones without the small factor.

* `norm_sub_le_of_ball_bound`: the Schwarz bound `‖f c - f 0‖ ≤ 2 B ‖c‖ / R`;
* `localClass_centre_boundE_of_param`: for centre-labelled differences
  `TE z Y p = G cc z Y p - G 0 z Y p` of a family analytic in the amplitude with the per-term bound
  `E_b e^{-κ d_{k+1}(Y)}`, the clause input `hTEbd` of `localClass_termClausesE_centre` holds as
  soon as `2 E_b ‖cc‖ / R ≤ E₀`;
* `localClass_site_boundM_of_param`: the same for the source terms (`hTMbd`, `hBM` of
  `localClass_termClausesM`), with `vn ≤ √N ‖·‖_∞`.

Not proved here (OPEN): the analyticity in the amplitude of the per-label objects of W811-W848
(they are stated at a fixed `cc`; the parameter would be carried through the chain as the source
`g` is in `LocalClassM.lean`), and the size of `R` (the admissible amplitudes of the hypothesis
`hδ₁ : √N ‖cc‖ covSupConstC(…) c_ψ < δ₁` of `localB_eTermHat_evTerm_xiFieldDom`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Fluctuation Metric

section Schwarz

/-- **The Schwarz bound for a difference**: if `f` is complex differentiable on the disc `|w| < R`
and `‖f‖ ≤ B` there, then `‖f c - f 0‖ ≤ 2 B ‖c‖ / R` for `|c| < R`. -/
theorem norm_sub_le_of_ball_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {R B : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ f (ball 0 R))
    (hB : ∀ w ∈ ball (0 : ℂ) R, ‖f w‖ ≤ B) {c : ℂ} (hc : ‖c‖ < R) :
    ‖f c - f 0‖ ≤ 2 * B * ‖c‖ / R := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hmaps : Set.MapsTo f (ball 0 R) (closedBall (f 0) (2 * B)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hB w hw
    have h2 := hB 0 h0
    calc ‖f w - f 0‖ ≤ ‖f w‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith
  have hcm : c ∈ ball (0 : ℂ) R := by rwa [mem_ball, dist_zero_right]
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hcm
  rw [dist_eq_norm, dist_zero_right] at h
  calc ‖f c - f 0‖ ≤ 2 * B / R * ‖c‖ := h
    _ = 2 * B * ‖c‖ / R := by ring

end Schwarz

section Class

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **The bound of the centre-labelled new contributions from their amplitude** (D3(b)): let
`G c z Y p` be the term of the centre `z` and the polymer `Y` at the amplitude `c` (at `c = 0`: the
background value), complex differentiable in `c` on `|c| < R` and bounded there by
`E_b e^{-κ d_{k+1}(Y)}` on the class domain.  Then the new contributions
`TE z Y p = G cc z Y p - G 0 z Y p` satisfy the input `hTEbd` of `localClass_termClausesE_centre`
with the constant `E₀` as soon as `2 E_b ‖cc‖ / R ≤ E₀`; for `‖cc‖ = β_k^{-1/2} |σ|` the constant of
the new terms is `2 E_b β_k^{-1/2} |σ| / R`. -/
theorem localClass_centre_boundE_of_param {P : Consts} {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (G : ℂ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    {R Eb : ℝ} (hR : 0 < R)
    (hGd : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      DifferentiableOn ℂ (fun c => G c z Y p) (ball 0 R))
    (hGb : ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ∀ c ∈ ball (0 : ℂ) R, ‖G c z Y p‖ ≤ Eb * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    {cc : ℂ} (hcc : ‖cc‖ < R) (hE₀ : 2 * Eb * ‖cc‖ / R ≤ P.E₀) :
    ∀ z Y, IsPolyDom P.m₀ (k + 1) Y → z ∈ Y →
      ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖G cc z Y p - G 0 z Y p‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by
  intro z Y hY hz p hp
  have h := norm_sub_le_of_ball_bound hR (hGd z Y hY hz p hp) (hGb z Y hY hz p hp) hcc
  have he : 0 < Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := Real.exp_pos _
  calc ‖G cc z Y p - G 0 z Y p‖
      ≤ 2 * (Eb * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y)) * ‖cc‖ / R := h
    _ = (2 * Eb * ‖cc‖ / R) * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by ring
    _ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := mul_le_mul_of_nonneg_right hE₀ he.le

/-- **The bound of the new source terms from their amplitude** (D3(b); P4 (2.52)-(2.53): the
factor `β_k^{-1/2}` of `ℳ^{(k+1)}_0` comes from the difference): if the vector-valued term
`GM c x Y (p, g)` is complex differentiable in the amplitude `c` on `|c| < R`, with components
bounded there by `B_b e^{-κ d_{k+1}(Y)}`, then the differences `GM cc - GM 0` satisfy the input
`hTMbd` of `localClass_termClausesM` with the constant `B_M = 2 √N B_b ‖cc‖ / R`. -/
theorem localClass_site_boundM_of_param {P : Consts} {a : ℕ → ℝ} {ν : ℝ} {εseq : ℕ → ℝ}
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁ m₁ (k + 1)))
    (GM : ℂ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → Fin N → ℂ)
    {R Bb : ℝ} (hR : 0 < R) (hBb0 : 0 ≤ Bb)
    (hGd : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 → DifferentiableOn ℂ (fun c => GM c x Y (p, g)) (ball 0 R))
    (hGb : ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 → ∀ c ∈ ball (0 : ℂ) R, ∀ i,
        ‖GM c x Y (p, g) i‖ ≤ Bb * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y))
    {cc : ℂ} (hcc : ‖cc‖ < R) :
    ∀ x Y, IsPolyDom P.m₀ (k + 1) Y → x ∈ Y →
      ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1)
        (localB (k + 1) (le_refl (k + 1)) (Yp Y) (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      Def6.l1 g < 1 →
      vn (GM cc x Y (p, g) - GM 0 x Y (p, g)) ≤
        (2 * Real.sqrt N * Bb * ‖cc‖ / R) * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by
  intro x Y hY hx p g hp hg
  have he : 0 < Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := Real.exp_pos _
  have hBb : ∀ c ∈ ball (0 : ℂ) R,
      ‖GM c x Y (p, g)‖ ≤ Bb * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := fun c hc => by
      have h0 : 0 ≤ Bb * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by positivity
      exact (pi_norm_le_iff_of_nonneg h0).2 (hGb x Y hY hx p g hp hg c hc)
  have h := norm_sub_le_of_ball_bound hR (hGd x Y hY hx p g hp hg) hBb hcc
  have hv : ∀ v : Fin N → ℂ, vn v ≤ Real.sqrt N * ‖v‖ := fun v =>
    vn_le_sqrt_mul (norm_nonneg v) fun i => norm_le_pi_norm v i
  calc vn (GM cc x Y (p, g) - GM 0 x Y (p, g))
      ≤ Real.sqrt N * ‖GM cc x Y (p, g) - GM 0 x Y (p, g)‖ := hv _
    _ ≤ Real.sqrt N * (2 * (Bb * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y)) * ‖cc‖ / R) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = (2 * Real.sqrt N * Bb * ‖cc‖ / R) * Real.exp (-P.κ * sizeJ P.m₀ (k + 1) Y) := by ring

end Class

end Balaban.Localization
