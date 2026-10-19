/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0HaloAffine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0AllPlusComplex`: the all-plus gas at a complex source

`KF0AllPlusGas` treats the all-plus, all-`ψ`-small sector at a real source `src`. The regrouped
block activities are affine in the source (`KF0HaloAffine`), so they continue to a complex source
`g` as `gasTermC X g = H_X(0) + ∑_{x,i} g_{x,i} (∂_{g_{x,i}} H_X)`; this file collects the pieces of
that continuation.

* `gasTermC`: the activity at a complex source; `gasTermC_ofReal`, `gasTermC_add`,
  `measurable_gasTermC`, `depOn_gasTermC`, `gasTermC_congr_src` (it depends on `g` only at the
  sites of the blocks of `X`), `gasTermC_eq_zero_of_not_isAnimal`, and the bound
  `norm_gasTermC_le` for a source of `ℓ¹` norm at most `1`, with amplitude twice that of the
  real activity.
* `chartExponentC`: the exponent of the chart integrand at a complex source, equal to the landed
  `chartInteractionExponent` at a real source (`chartExponentC_ofReal`); `chart_integrand_eq_C` is
  the identity of `f1_integrand_eq` at a complex source on the product cutoff event, derived from
  the real identity at the sources `0` and `δ_{x,i}` (the chart coordinates are the sums of the
  source pieces, `hB`).
* `sum_nePoly_fibre`, `sum_blockSrc`: regrouping of the source pieces by block sets;
  `integral_indicator_small_eq_complex`: the complex form of the cutoff normalization.
-/

@[expose] public section

namespace Balaban.LargeField.KF0AllPlus

open Finset MeasureTheory Balaban.Green Balaban.LargeField Balaban.LargeField.KF0F1

open Balaban.LargeField.KF0Gas Balaban.Polymer SphereChart

open scoped Classical




section Defs

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **The regrouped block activity at a complex source.**  `H_X(0) + ∑_{x,i} g_{x,i} (∂_{g_{x,i}} H_X)`:
the activity `H_X` is affine in the source (`blockActivity_affine`), and this is its complex-linear
extension. -/
noncomputable def gasTermC (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (X : NePoly (Torus d m')) (g : Torus d (s * m') → Fin N → ℂ)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) : ℂ :=
  ((blockActivity e β ν p (fun _ _ => 0) X.1 Φ : ℝ) : ℂ) +
    ∑ x : Torus d (s * m'), ∑ i : Fin N, g x i * ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ)

theorem gasTermC_add (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (X : NePoly (Torus d m')) (g l : Torus d (s * m') → Fin N → ℂ)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    gasTermC e β ν p X (fun x i => g x i + l x i) Φ = gasTermC e β ν p X g Φ +
      ∑ x : Torus d (s * m'), ∑ i : Fin N, l x i * ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ) := by
  unfold gasTermC
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- On a real source `gasTermC` is the real regrouped activity. -/
theorem gasTermC_ofReal {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hκ : 0 ≤ κ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d (s * m') → Fin N → ℝ)
    (X : NePoly (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    gasTermC e β ν p X (fun x i => (src x i : ℂ)) Φ = gasTerm e β ν p src X Φ := by
  unfold gasTermC gasTerm
  rw [blockActivity_affine hβ hg hgν hν1 hγ hq hκ hp hn hρ1 hρ e src X.1 Φ]
  push_cast
  rfl

theorem measurable_blockSrc (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (x : Torus d (s * m')) (i : Fin N) (X : Finset (Torus d m')) :
    Measurable (fun Φ : ∀ b, BlockSpace d s m' (perp h) b => blockSrc e β ν p x i X Φ) := by
  unfold blockSrc f1SiteSrcHaloClip
  refine Finset.measurable_sum _ fun H _ => ?_
  exact ((measurable_kf0HaloTerm ν β _ _ _ H).comp (measurable_clipField p)).comp measurable_toSites

theorem measurable_gasTermC (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (X : NePoly (Torus d m')) (g : Torus d (s * m') → Fin N → ℂ) :
    Measurable (gasTermC e β ν p X g) := by
  unfold gasTermC
  refine (measurable_blockActivity e β ν p _ X.1).add ?_
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun i _ => ?_
  exact measurable_const.mul (Complex.measurable_ofReal.comp (measurable_blockSrc e β ν p x i X.1))

theorem depOn_gasTermC (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (X : NePoly (Torus d m')) (g : Torus d (s * m') → Fin N → ℂ) :
    DepOn X.1 (gasTermC e β ν p X g) := by
  intro Φ Φ' hΦ
  have hsite : ∀ H ∈ haloFibre d s m' X.1, ∀ b ∈ H, toSites Φ b = toSites Φ' b := by
    intro H hH b hb
    have hbX : blockOf d s m' b ∈ X.1 := by
      rw [← (mem_haloFibre.1 hH)]; exact Finset.mem_image_of_mem _ hb
    exact congrFun (hΦ (blockOf d s m' b) hbX) (⟨b, rfl⟩ : Fibre d s m' (blockOf d s m' b))
  have hA := blockActivity_depOn e β ν p (fun _ _ => 0) X.1 Φ Φ' hΦ
  have hS : ∀ x i, blockSrc e β ν p x i X.1 Φ = blockSrc e β ν p x i X.1 Φ' := by
    intro x i
    unfold blockSrc
    refine Finset.sum_congr rfl fun H hH => ?_
    unfold f1SiteSrcHaloClip
    exact kf0HaloTerm_congr ν β _ _ _ H fun b hb => by simp only [clipField, hsite H hH b hb]
  have hA' : ((blockActivity e β ν p (fun _ _ => 0) X.1 Φ : ℝ) : ℂ) =
      ((blockActivity e β ν p (fun _ _ => 0) X.1 Φ' : ℝ) : ℂ) := hA
  unfold gasTermC
  rw [hA']
  simp only [hS]

end Defs

section Bounds

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

theorem gasTermC_congr_src (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (X : NePoly (Torus d m')) {g g' : Torus d (s * m') → Fin N → ℂ}
    (hg : ∀ x, blockOf d s m' x ∈ X.1 → g x = g' x)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    gasTermC e β ν p X g Φ = gasTermC e β ν p X g' Φ := by
  unfold gasTermC
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : blockOf d s m' x ∈ X.1
  · rw [hg x hx]
  · rw [blockSrc_eq_zero_of_not_mem e β ν p x i X.1 hx Φ]
    simp

theorem gasTermC_eq_zero_of_not_isAnimal {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (X : NePoly (Torus d m'))
    (hX : ¬ IsAnimal (blockGraph d m') X.1) (g' : Torus d (s * m') → Fin N → ℂ)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    gasTermC e β ν p X g' Φ = 0 := by
  unfold gasTermC
  rw [blockActivity_eq_zero_of_not_isAnimal hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e _ X.1 hX Φ]
  simp [blockSrc_eq_zero_of_not_isAnimal e β ν p _ _ X.1 hX Φ]

/-- **The bound for a complex source of `ℓ¹` norm at most one.** -/
theorem norm_gasTermC_le {β ν g γ κ p ε εs κ0 κ1 : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (hsite : ∀ x : Torus d (s * m'), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1SiteHalo e β ν (fun _ _ => 0) x H) ≤ ε)
    (hbond : ∀ (x : Torus d (s * m')) (μ : Fin d), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1BondHalo e β ν x μ H) ≤ ε)
    (hsrc : ∀ (x : Torus d (s * m')) (i : Fin N), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1SiteSrcHalo e β ν x i H) ≤ εs)
    (hεs0 : 0 ≤ εs) (hεs : εs ≤ (1 + 2 * d) * s ^ d * ε) (hκ01 : 1 + κ0 + κ1 ≤ κ) (hκ01' : 0 ≤ κ0 + κ1)
    (X : NePoly (Torus d m')) (g' : Torus d (s * m') → Fin N → ℂ)
    (hg1 : ∑ x, ∑ i, ‖g' x i‖ ≤ 1) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    ‖gasTermC e β ν p X g' Φ‖ ≤
      2 * ((1 + 2 * d) * s ^ d * ε) * Real.exp (-(κ0 + κ1) * stSize X.1) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hA := blockActivity_abs_le hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e (fun _ _ => 0)
    hsite hbond hκ01 hκ01' X.1 Φ
  have hA0 : 0 ≤ ((1 + 2 * (d : ℝ)) * s ^ d * ε) := by
    have hε : 0 ≤ ε := le_trans (Finset.sum_nonneg fun H _ =>
      mul_nonneg (Real.exp_pos _).le (cutoffSup_nonneg _ _)) (hsite 0)
    positivity
  by_cases hX : IsAnimal (blockGraph d m') X.1
  · have hcard : stSize X.1 ≤ X.1.card := by
      unfold stSize
      exact_mod_cast steiner_le hX (Finset.Subset.refl X.1)
    have hX0 : (0 : ℝ) ≤ X.1.card := Nat.cast_nonneg _
    have hexp : Real.exp (-(κ * X.1.card)) ≤ Real.exp (-(κ0 + κ1) * stSize X.1) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : (κ0 + κ1) * (stSize X.1) ≤ (κ0 + κ1) * X.1.card :=
        mul_le_mul_of_nonneg_left hcard hκ01'
      have h2 : (κ0 + κ1) * (X.1.card : ℝ) ≤ κ * X.1.card :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
      nlinarith
    have hS : ∀ x i, |blockSrc e β ν p x i X.1 Φ| ≤ εs * Real.exp (-(κ * X.1.card)) :=
      fun x i => abs_blockSrc_le hg hgν hβ hq hs hκ hγκ hp hρ e x i (hsrc x i) X.1 Φ
    have hsum : ‖∑ x : Torus d (s * m'), ∑ i : Fin N, g' x i * ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ)‖ ≤
        εs * Real.exp (-(κ * X.1.card)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ x : Torus d (s * m'), ‖∑ i : Fin N, g' x i * ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ)‖
          ≤ ∑ x : Torus d (s * m'), ∑ i : Fin N, ‖g' x i‖ * (εs * Real.exp (-(κ * X.1.card))) := by
            refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hS x i) (norm_nonneg _)
        _ = (∑ x, ∑ i, ‖g' x i‖) * (εs * Real.exp (-(κ * X.1.card))) := by
            simp only [Finset.sum_mul]
        _ ≤ 1 * (εs * Real.exp (-(κ * X.1.card))) :=
            mul_le_mul_of_nonneg_right hg1 (by positivity)
        _ = _ := one_mul _
    unfold gasTermC
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ ((1 + 2 * (d : ℝ)) * s ^ d * ε) * Real.exp (-(κ0 + κ1) * stSize X.1) +
          ((1 + 2 * (d : ℝ)) * s ^ d * ε) * Real.exp (-(κ0 + κ1) * stSize X.1) := by
          refine add_le_add hA (hsum.trans ?_)
          exact mul_le_mul hεs hexp (Real.exp_pos _).le hA0
      _ = _ := by ring
  · rw [gasTermC_eq_zero_of_not_isAnimal hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e X hX g' Φ,
      norm_zero]
    positivity

end Bounds


section Chart

theorem sum_sum_ite_and {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (f : α → β → M) (a : α) (b : β) :
    ∑ x, ∑ i, (if x = a ∧ i = b then f x i else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  · intro x _ hx
    simp [hx]
  · simp


variable {d N n ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- The `i`-th coordinate of the chart spin at `x`: `h_i + β^{-1/2}(v_{x,i} + w_x h_i)`. -/
noncomputable def chartCoord (β : ℝ) (h : EuclideanSpace ℝ (Fin N)) (v : Torus d ℓ → perp h)
    (x : Torus d ℓ) (i : Fin N) : ℝ :=
  h i + (Real.sqrt β)⁻¹ * (((v x : perp h) : EuclideanSpace ℝ (Fin N)) i + wN β v x * h i)

/-- **The exponent of the chart integrand at a complex source**: `-R_β(v) + ∑_{x,i} g_{x,i} φ_{x,i}`
with `φ` the chart spin of `β^{-1/2} v`. For a real source it is the landed
`chartInteractionExponent` (`chartExponentC_ofReal`). -/
noncomputable def chartExponentC (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) (v : Torus d ℓ → perp h) : ℂ :=
  ((-chartRemainder β ν v : ℝ) : ℂ) + ∑ x, ∑ i, g x i * ((chartCoord β h v x i : ℝ) : ℂ)

theorem chartExponentC_ofReal (β ν : ℝ) (src : Torus d ℓ → Fin N → ℝ) (v : Torus d ℓ → perp h) :
    chartExponentC β ν h (fun x i => (src x i : ℂ)) v =
      ((chartInteractionExponent β ν h src v : ℝ) : ℂ) := by
  unfold chartExponentC chartInteractionExponent
  have key : ∀ x : Torus d ℓ, ∑ i : Fin N, src x i * chartCoord β h v x i =
      (∑ i, src x i * h i) +
        (Real.sqrt β)⁻¹ * (∑ i, src x i * ((v x : EuclideanSpace ℝ (Fin N)) i)) +
        (Real.sqrt β)⁻¹ * ((∑ i, src x i * h i) * wN β v x) := by
    intro x
    have : ∀ i, src x i * chartCoord β h v x i = src x i * h i +
        (Real.sqrt β)⁻¹ * (src x i * ((v x : EuclideanSpace ℝ (Fin N)) i)) +
        (Real.sqrt β)⁻¹ * (wN β v x * (src x i * h i)) := fun i => by
      unfold chartCoord; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have : ∑ x : Torus d ℓ, ∑ i : Fin N, src x i * chartCoord β h v x i =
      sourceConst src h + (Real.sqrt β)⁻¹ * sourceTangent src v +
        (Real.sqrt β)⁻¹ * sourceNormal src h β v := by
    simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
    unfold sourceConst sourceTangent sourceNormal
    ring
  have hc : ∑ x : Torus d ℓ, ∑ i : Fin N, (src x i : ℂ) * ((chartCoord β h v x i : ℝ) : ℂ) =
      ((∑ x : Torus d ℓ, ∑ i : Fin N, src x i * chartCoord β h v x i : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, this]
  push_cast
  ring

end Chart

section Identity

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **The chart integrand at a complex source on the product cutoff event.**  On
`‖ψ_y‖ ≤ p` for all `y`, the chart Jacobian times the exponential of the complex chart exponent is
`e^{⟨g,h⟩}` times the exponential of the sum of the clipless halo pieces: the source-free site and
bond pieces and the source pieces weighted by `g`. -/
theorem chart_integrand_eq_C {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (gc : Torus d (s * m') → Fin N → ℂ)
    (ψ : Torus d (s * m') → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    ((chartJac β (fun x => ((tfield d (s * m') ν ψ x : perp h) : EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ) *
        Complex.exp (chartExponentC β ν h gc (tfield d (s * m') ν ψ)) =
      Complex.exp (∑ x, ∑ i, gc x i * (h i : ℂ)) *
        Complex.exp (((∑ x, ∑ H, f1SiteHalo e β ν (fun _ _ => 0) x H ψ +
            ∑ x, ∑ μ : Fin d, ∑ H, f1BondHalo e β ν x μ H ψ : ℝ) : ℂ) +
          ∑ x, ∑ i, gc x i * ((∑ H, f1SiteSrcHalo e β ν x i H ψ : ℝ) : ℂ)) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  set v := tfield d (s * m') ν ψ with hv
  set J := chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N))) with hJ
  set R := chartRemainder β ν v with hR
  set S₀ : ℝ := ∑ x, ∑ H, f1SiteHalo e β ν (fun _ _ => 0) x H ψ +
    ∑ x, ∑ μ : Fin d, ∑ H, f1BondHalo e β ν x μ H ψ with hS₀
  -- (A) the source-free identity
  have hA : J * Real.exp (-R) = Real.exp S₀ := by
    have := f1_integrand_eq (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ e
      (fun _ _ => (0 : ℝ)) ψ hψ
    have h0 : chartInteractionExponent β ν h (fun (_ : Torus d (s * m')) (_ : Fin N) => (0 : ℝ)) v =
        -R := by
      simp [chartInteractionExponent, sourceConst, sourceTangent, sourceNormal, hR]
    rw [h0] at this
    rw [this]
    congr 1
    simp [sourceConst, hS₀]
  -- (B) the source coefficient identity
  have hB : ∀ x₀ i₀, chartCoord β h v x₀ i₀ = h i₀ + ∑ H, f1SiteSrcHalo e β ν x₀ i₀ H ψ := by
    intro x₀ i₀
    set δ : Torus d (s * m') → Fin N → ℝ := fun x i => if x = x₀ ∧ i = i₀ then 1 else 0 with hδ
    have h1 := f1_integrand_eq (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ e
      δ ψ hψ
    have hE : chartInteractionExponent β ν h δ v = -R + chartCoord β h v x₀ i₀ := by
      have := chartExponentC_ofReal (h := h) β ν δ v
      unfold chartExponentC at this
      have hsum : ∑ x : Torus d (s * m'), ∑ i : Fin N, (δ x i : ℂ) *
          ((chartCoord β h v x i : ℝ) : ℂ) = ((chartCoord β h v x₀ i₀ : ℝ) : ℂ) := by
        have : ∀ x i, (δ x i : ℂ) * ((chartCoord β h v x i : ℝ) : ℂ) =
            if x = x₀ ∧ i = i₀ then ((chartCoord β h v x i : ℝ) : ℂ) else 0 := by
          intro x i; simp only [hδ]; split_ifs <;> simp
        simp only [this]
        exact sum_sum_ite_and (fun x i => ((chartCoord β h v x i : ℝ) : ℂ)) x₀ i₀
      rw [hsum] at this
      exact_mod_cast this.symm
    have hconst : sourceConst δ h = h i₀ := by
      have : ∀ x i, δ x i * h i = if x = x₀ ∧ i = i₀ then h i else 0 := by
        intro x i; simp only [hδ]; split_ifs <;> simp
      unfold sourceConst
      simp only [this]
      exact sum_sum_ite_and (fun _ i => h i) x₀ i₀
    have hsite : ∑ x : Torus d (s * m'), ∑ H, f1SiteHalo e β ν δ x H ψ =
        ∑ x : Torus d (s * m'), ∑ H, f1SiteHalo e β ν (fun _ _ => (0 : ℝ)) x H ψ +
          ∑ H, f1SiteSrcHalo e β ν x₀ i₀ H ψ := by
      have : ∀ x H, f1SiteHalo e β ν δ x H ψ = f1SiteHalo e β ν (fun _ _ => (0 : ℝ)) x H ψ +
          ∑ i, δ x i * f1SiteSrcHalo e β ν x i H ψ := fun x H =>
        f1SiteHalo_affine hβ hg hgν hν1 hγ hq hκ hp hn hρ1 hρ e δ x H ψ hψ
      simp only [this, Finset.sum_add_distrib]
      congr 1
      have hz : ∀ x (H : Finset (Torus d (s * m'))), ∑ i, δ x i * f1SiteSrcHalo e β ν x i H ψ =
          ∑ i, if x = x₀ ∧ i = i₀ then f1SiteSrcHalo e β ν x i H ψ else 0 := by
        intro x H; refine Finset.sum_congr rfl fun i _ => ?_; simp only [hδ]; split_ifs <;> simp
      simp only [hz]
      have hz2 : ∀ x y, ∑ H : Finset (Torus d (s * m')),
          (if x = x₀ ∧ y = i₀ then f1SiteSrcHalo e β ν x y H ψ else 0) =
          if x = x₀ ∧ y = i₀ then ∑ H, f1SiteSrcHalo e β ν x y H ψ else 0 := by
        intro x y; split_ifs <;> simp
      have hz3 : ∀ x, ∑ H : Finset (Torus d (s * m')), ∑ y : Fin N,
          (if x = x₀ ∧ y = i₀ then f1SiteSrcHalo e β ν x y H ψ else 0) =
          ∑ y : Fin N, ∑ H : Finset (Torus d (s * m')),
          (if x = x₀ ∧ y = i₀ then f1SiteSrcHalo e β ν x y H ψ else 0) := fun x => Finset.sum_comm
      simp only [hz3, hz2]
      exact sum_sum_ite_and (fun x y => ∑ H, f1SiteSrcHalo e β ν x y H ψ) x₀ i₀
    rw [hE, hconst, hsite] at h1
    have h2 : Real.exp (chartCoord β h v x₀ i₀) * Real.exp S₀ =
        Real.exp (h i₀ + ∑ H, f1SiteSrcHalo e β ν x₀ i₀ H ψ) * Real.exp S₀ := by
      calc Real.exp (chartCoord β h v x₀ i₀) * Real.exp S₀
          = Real.exp (chartCoord β h v x₀ i₀) * (J * Real.exp (-R)) := by rw [hA]
        _ = J * Real.exp (-R + chartCoord β h v x₀ i₀) := by rw [Real.exp_add]; ring
        _ = Real.exp (h i₀ + ∑ H, f1SiteSrcHalo e β ν x₀ i₀ H ψ + S₀) := by
            rw [h1, hS₀]; congr 1; ring
        _ = _ := by rw [Real.exp_add]
    exact Real.exp_injective (mul_right_cancel₀ (Real.exp_pos _).ne' h2)
  -- (C) the complex source
  have hexp : chartExponentC β ν h gc v = ((-R : ℝ) : ℂ) + ∑ x, ∑ i, gc x i * (h i : ℂ) +
      ∑ x, ∑ i, gc x i * ((∑ H, f1SiteSrcHalo e β ν x i H ψ : ℝ) : ℂ) := by
    unfold chartExponentC
    have : ∀ x i, gc x i * ((chartCoord β h v x i : ℝ) : ℂ) =
        gc x i * (h i : ℂ) + gc x i * ((∑ H, f1SiteSrcHalo e β ν x i H ψ : ℝ) : ℂ) := by
      intro x i
      rw [hB x i]; push_cast; ring
    simp only [this, Finset.sum_add_distrib]
    ring
  have hAc : ((J : ℝ) : ℂ) * Complex.exp (((-R : ℝ)) : ℂ) = Complex.exp ((S₀ : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hA
    simpa [Complex.ofReal_exp] using this
  rw [hexp, add_assoc, Complex.exp_add, ← mul_assoc, hAc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

end Identity


section Regroup

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- Summing the fibre sums over the nonempty block sets gives the sum over all site sets, when the
term of the empty set vanishes. -/
theorem sum_nePoly_fibre (T : Finset (Torus d (s * m')) → ℝ) (hT0 : T ∅ = 0) :
    ∑ X : NePoly (Torus d m'), ∑ H ∈ haloFibre d s m' X.1, T H =
      ∑ H : Finset (Torus d (s * m')), T H := by
  have hfib : ∑ X : Finset (Torus d m'), ∑ H ∈ haloFibre d s m' X, T H =
      ∑ H : Finset (Torus d (s * m')), T H :=
    Finset.sum_fiberwise (Finset.univ : Finset (Finset (Torus d (s * m'))))
      (fun H => H.image (blockOf d s m')) T
  have hG0 : ∑ H ∈ haloFibre d s m' ∅, T H = 0 := by
    refine Finset.sum_eq_zero fun H hH => ?_
    have : H = ∅ := Finset.image_eq_empty.1 (mem_haloFibre.1 hH)
    rw [this, hT0]
  rw [← hfib, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun X : Finset (Torus d m') => X.Nonempty),
    Finset.sum_eq_zero (s := Finset.univ.filter fun X : Finset (Torus d m') => ¬ X.Nonempty)
      (fun X hX => by
        have : X = ∅ := Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hX).2
        rw [this]; exact hG0), add_zero]
  exact (Finset.sum_subtype (Finset.univ.filter fun X : Finset (Torus d m') => X.Nonempty)
    (by simp) (fun X => ∑ H ∈ haloFibre d s m' X, T H)).symm

/-- The coefficients of `g_{x,i}` in the activities `H_X` add up to the sum of the clipped source
pieces. -/
theorem sum_blockSrc (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (x : Torus d (s * m')) (i : Fin N) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    ∑ X : NePoly (Torus d m'), blockSrc e β ν p x i X.1 Φ =
      ∑ H : Finset (Torus d (s * m')), f1SiteSrcHaloClip e β ν x i H p (toSites Φ) := by
  refine sum_nePoly_fibre (fun H => f1SiteSrcHaloClip e β ν x i H p (toSites Φ)) ?_
  exact f1SiteSrcHalo_eq_zero e β ν x i ∅ (by rintro ⟨-, hx⟩; simp at hx) _

end Regroup

section Indicator

variable {ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W] (γ : Measure W) [IsProbabilityMeasure γ]

/-- The complex-valued form of `integral_indicator_small_eq`. -/
theorem integral_indicator_small_eq_complex (p : ℝ) (hpos : γ (smallSet p) ≠ 0)
    (F : (ι → W) → ℂ) :
    ∫ ψ, Set.indicator (Set.pi Set.univ fun _ : ι => smallSet p) F ψ
        ∂(Measure.pi fun _ : ι => γ) =
      (((1 - γ.real (largeSet p)) ^ Fintype.card ι : ℝ) : ℂ) *
        ∫ ψ, F ψ ∂(Measure.pi fun _ : ι => ProbabilityTheory.cond γ (smallSet p)) := by
  have hm : MeasurableSet (Set.pi Set.univ fun _ : ι => (smallSet p : Set W)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_smallSet p
  rw [integral_indicator hm, restrict_pi_smallSet_eq γ p hpos, integral_smul_measure,
    ENNReal.toReal_pow, Complex.real_smul]
  congr 3
  have h := probReal_compl_eq_one_sub (μ := γ) (measurableSet_largeSet p)
  rw [smallSet_eq_compl]
  exact h

end Indicator


end Balaban.LargeField.KF0AllPlus
