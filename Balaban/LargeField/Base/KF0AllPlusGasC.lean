/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0AllPlusComplex
public import Balaban.Polymer.MayerSupport
public import Balaban.Polymer.MayerMarksPY
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0AllPlusGasC`: the all-plus, all-small sector as a polymer gas at a complex source

The cutoff part of the chart integral at a complex source `g` of `ℓ¹` norm below one,
`kf0CutIntegral γ₀ β ν p g = ∫ 1_{‖ψ_y‖ ≤ p ∀ y} J_β exp(chartExponentC g) d⊗γ₀`, is
`(1 - τ)^{|Λ|} e^{⟨g, h⟩} exp(∑_Y P(Y)(g))` (`kf0CutIntegral_eq`), where `P(Y)(g) = kf0PY … Y g` are
the local terms of the polymer gas of the Mayer activities of the regrouped block activities
`gasTermC` (`KF0AllPlusComplex`) on the blocks of side `s`, and:

* `kf0CutIntegral_eq`: the identity and the weighted bound `∑_{Y ∋ b} ‖P(Y)(g)‖ e^{κ' |Y|_St} ≤ 64 e H₀ e^{-2κ₀}` with `H₀ = 2 (1 + 2d) s^d ε`;
* `kf0PY_analyticOnNhd`: `g ↦ P(Y)(g)` is analytic on the unit `ℓ¹` ball (`kf0_marks_data`, via
  `mayer_marks_pe`: the activities are affine in the marks `g - g₀`, so the Mayer layer applies on a
  polydisc around any `g₀` of norm `< 1`);
* `kf0PY_congr`: `P(Y)(g)` depends on `g` only at the sites of the blocks of `Y`;
* `kf0PY_eq_zero_of_not_isAnimal`: `P(Y) = 0` for a non-connected block set `Y`.
-/

@[expose] public section

namespace Balaban.LargeField.KF0AllPlus

open Finset MeasureTheory Balaban.Green Balaban.LargeField Balaban.LargeField.KF0F1

open Balaban.LargeField.KF0Gas Balaban.Polymer SphereChart Balaban.Analysis

open scoped Classical

section Marks

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **The local terms of the all-plus gas** `P(Y)(g)`: the local terms of the polymer gas of the
Mayer activities of the regrouped block activities at the (complex) source `g`, for the conditioned
reference `pc` on the tangent space. -/
noncomputable def kf0PY (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (pc : Measure (perp h)) (Y : Finset (Torus d m'))
    (g : Torus d (s * m') → Fin N → ℂ) : ℂ :=
  PY (shareBlock (Subtype.val : NePoly (Torus d m') → Finset (Torus d m'))) Subtype.val
    (mayerK (blockRef (d := d) (s := s) (m' := m') pc) (fun X : NePoly (Torus d m') => X.1)
      (fun X => gasTermC e β ν p X g)) Y

/-- **Analyticity of the local terms around a source of `ℓ¹` norm below one, and the series for
the logarithm.**  If `‖gasTermC X g‖ ≤ H₀ e^{-(κ₀+κ₁)|X|_St}` for every complex source of `ℓ¹` norm
at most one, then around a source `g₀` of norm `< 1` the local terms are analytic in the marks
`l = g - g₀` on a polydisc, and the logarithm series of the gas at `g₀` is the sum of the local
terms. -/
theorem kf0_marks_data {κ0 κ1 κ' H0 : ℝ}
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ H0) (hH0log : H0 ≤ Real.log 2) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))
    [IsProbabilityMeasure pc]
    (hbd : ∀ g : Torus d (s * m') → Fin N → ℂ, ∑ x, ∑ i, ‖g x i‖ ≤ 1 →
      ∀ (X : NePoly (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b),
        ‖gasTermC e β ν p X g Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * stSize X.1))
    (hbsrc : ∀ (x : Torus d (s * m')) (i : Fin N) (X : NePoly (Torus d m')),
      Bdd (fun Φ : ∀ b, BlockSpace d s m' (perp h) b => ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ)))
    (g₀ : Torus d (s * m') → Fin N → ℂ) (hg₀ : ∑ x, ∑ i, ‖g₀ x i‖ < 1) :
    ∃ r : ℝ, 0 < r ∧
      (∀ Y : Finset (Torus d m'), AnalyticOnNhd ℂ
        (fun l : Torus d (s * m') × Fin N → ℂ =>
          kf0PY e β ν p pc Y (fun x i => g₀ x i + l (x, i))) (polydisc 0 (fun _ => r))) ∧
      logSeries (shareBlock (Subtype.val : NePoly (Torus d m') → Finset (Torus d m')))
        (mayerK (blockRef (d := d) (s := s) (m' := m') pc) (fun X : NePoly (Torus d m') => X.1)
          (fun X => gasTermC e β ν p X g₀)) =
        ∑ Y : Finset (Torus d m'), kf0PY e β ν p pc Y g₀ := by
  set a : NePoly (Torus d m') → (∀ b, BlockSpace d s m' (perp h) b) → ℂ :=
    fun X Φ => gasTermC e β ν p X g₀ Φ with ha
  set gm : (Torus d (s * m') × Fin N) → NePoly (Torus d m') →
      (∀ b, BlockSpace d s m' (perp h) b) → ℂ :=
    fun j X Φ => ((blockSrc e β ν p j.1 j.2 X.1 Φ : ℝ) : ℂ) with hgm
  have hHlam : ∀ (l : Torus d (s * m') × Fin N → ℂ) X Φ, Hlam a gm l X Φ =
      gasTermC e β ν p X (fun x i => g₀ x i + l (x, i)) Φ := by
    intro l X Φ
    have := gasTermC_add e β ν p X g₀ (fun x i => l (x, i)) Φ
    rw [this]
    unfold Hlam
    simp only [ha, hgm, Fintype.sum_prod_type]
  -- the radius
  set ρ₀ : ℝ := (1 - ∑ x, ∑ i, ‖g₀ x i‖) / ((Fintype.card (Torus d (s * m') × Fin N) : ℝ) + 1)
    with hρ₀
  have hρ₀pos : 0 < ρ₀ := by
    refine div_pos (by linarith) (by positivity)
  have hnorm : ∀ l : Torus d (s * m') × Fin N → ℂ, l ∈ polydisc (0 : Torus d (s * m') × Fin N → ℂ) (fun _ => ρ₀) →
      ∑ x, ∑ i, ‖g₀ x i + l (x, i)‖ ≤ 1 := by
    intro l hl
    have h1 : ∑ x, ∑ i, ‖g₀ x i + l (x, i)‖ ≤ ∑ x, ∑ i, (‖g₀ x i‖ + ρ₀) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
        (norm_add_le _ _).trans (add_le_add le_rfl (by simpa using (hl (x, i)).le))
    refine h1.trans ?_
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card (Torus d (s * m')) : ℝ) * ((Fintype.card (Fin N) : ℝ) * ρ₀) =
        (Fintype.card (Torus d (s * m') × Fin N) : ℝ) * ρ₀ := by
      rw [Fintype.card_prod]; push_cast; ring
    have hle : (Fintype.card (Torus d (s * m') × Fin N) : ℝ) * ρ₀ ≤ 1 - ∑ x, ∑ i, ‖g₀ x i‖ := by
      rw [hρ₀, mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sub_pos.2 hg₀]
    linarith
  -- the numerical hypotheses of the Mayer layer
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hκ1nn : 0 ≤ κ1 := by linarith
  have hK0 : 0 ≤ 4 * Real.exp (-κ0) := by positivity
  have hKle : 4 * Real.exp (-κ0) ≤ Real.exp (-1) := by
    have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    rw [h4, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hG2 : ∀ b : Torus d m', ∑ Y : NePoly (Torus d m'),
      (if b ∈ Y.1 then Real.exp (-κ0 * stSize Y.1) else 0) ≤ 4 * Real.exp (-κ0) :=
    fun b => sum_exp_stSize_le hq b
  have hq' : 2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0) * 1 ≤ 1 / 2 := by
    simp only [mul_zero, Real.exp_zero, mul_one]; nlinarith
  have hα : 2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1 * (4 * Real.exp (-κ0)) *
      Real.exp (1 + κ' * 0) ≤ 1 := by
    simp only [mul_zero, Real.exp_zero, mul_one, add_zero]
    have h1 : 4 * Real.exp (-κ0) * Real.exp 1 ≤ 1 := by
      calc 4 * Real.exp (-κ0) * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
            mul_le_mul_of_nonneg_right hKle (Real.exp_pos 1).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have h2 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    nlinarith [mul_nonneg hH0 hK0]
  have hdep : ∀ X : NePoly (Torus d m'), Measurable (a X) := fun X => measurable_gasTermC e β ν p X g₀
  have hbdA : ∀ X, Bdd (a X) := fun X =>
    ⟨_, fun Φ => hbd g₀ hg₀.le X Φ⟩
  have hmg : ∀ j X, Measurable (gm j X) := fun j X =>
    Complex.measurable_ofReal.comp (measurable_blockSrc e β ν p j.1 j.2 X.1)
  have hbdG : ∀ j X, Bdd (gm j X) := fun j X => hbsrc j.1 j.2 X
  obtain ⟨hAn, hLog⟩ := mayer_marks_pe (blockRef (d := d) (s := s) (m' := m') pc)
    (fun X : NePoly (Torus d m') => X.1) (a := a) (g := gm) (d := stSize) (H0 := H0) (κ0 := κ0)
    (κ1 := κ1) (c := 0) (K0 := 4 * Real.exp (-κ0)) (c1 := 1) (κ' := κ') (κ0P := κ0)
    (K0P := 4 * Real.exp (-κ0)) (cP := 0) (r := fun _ => ρ₀) (fun X => X.2) hdep hbdA hmg hbdG
    hH0 hH0log hκ0nn hκ1nn le_rfl (fun Y => stSize_nonneg Y)
    (fun l hl X Φ => by
      rw [hHlam]
      exact hbd _ (hnorm l hl) X Φ)
    hK0 (fun b => by rw [Finset.sum_filter]; convert hG2 b)
    (fun C hC => by simpa using stSize_unionCs_le C hC) zero_le_one hq'
    (fun Y => card_le_stSize Y.1) hκ' le_rfl (fun b => by convert hG2 b) hκ hα
  have hfun : ∀ (l : Torus d (s * m') × Fin N → ℂ) (Y : Finset (Torus d m')),
      Ff (shareBlock (Subtype.val : NePoly (Torus d m') → Finset (Torus d m'))) Subtype.val
        (marksK (blockRef (d := d) (s := s) (m' := m') pc) (fun X : NePoly (Torus d m') => X.1)
          a gm) Y l = kf0PY e β ν p pc Y (fun x i => g₀ x i + l (x, i)) := by
    intro l Y
    unfold Ff marksK kf0PY
    have : Hlam a gm l = fun X => gasTermC e β ν p X (fun x i => g₀ x i + l (x, i)) :=
      funext fun X => funext fun Φ => hHlam l X Φ
    rw [this]
  refine ⟨ρ₀, hρ₀pos, fun Y => ?_, ?_⟩
  · have := hAn Y
    have e1 : (fun l : Torus d (s * m') × Fin N → ℂ =>
        kf0PY e β ν p pc Y (fun x i => g₀ x i + l (x, i))) =
        Ff (shareBlock (Subtype.val : NePoly (Torus d m') → Finset (Torus d m'))) Subtype.val
          (marksK (blockRef (d := d) (s := s) (m' := m') pc)
            (fun X : NePoly (Torus d m') => X.1) a gm) Y :=
      funext fun l => (hfun l Y).symm
    rw [e1]; exact this
  · have h0 : (0 : Torus d (s * m') × Fin N → ℂ) ∈ polydisc (0 : Torus d (s * m') × Fin N → ℂ)
        (fun _ => ρ₀) := fun j => by simpa using hρ₀pos
    have := hLog 0 h0
    have e2 : (fun Z : NePoly (Torus d m') => marksK (blockRef (d := d) (s := s) (m' := m') pc)
        (fun X : NePoly (Torus d m') => X.1) a gm Z 0) =
        mayerK (blockRef (d := d) (s := s) (m' := m') pc) (fun X : NePoly (Torus d m') => X.1)
          (fun X => gasTermC e β ν p X g₀) := by
      funext Z
      unfold marksK
      have : Hlam a gm 0 = fun X => gasTermC e β ν p X g₀ := by
        funext X Φ
        rw [hHlam]
        simp
      rw [this]
    rw [e2] at this
    rw [this]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [hfun 0 Y]
    simp

end Marks

section Cut

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **The all-plus, all-`ψ`-small chart integral at a complex source**:
`∫ 1_{‖ψ_y‖ ≤ p ∀ y} J_β(K_ν^{-1/2} ψ) exp(chartExponentC g (K_ν^{-1/2} ψ)) d⊗γ₀(ψ)`, the product
cutoff part of the partition function in the Gaussian chart around `h` (`γ₀` the standard Gaussian
on the tangent space). -/
noncomputable def kf0CutIntegral (γ₀ : Measure (perp h)) (β ν p : ℝ)
    (g : Torus d (s * m') → Fin N → ℂ) : ℂ :=
  ∫ ψ, Set.indicator (Set.pi Set.univ fun _ : Torus d (s * m') => smallSet p)
    (fun ψ : Torus d (s * m') → perp h =>
      ((chartJac β (fun x => ((tfield d (s * m') ν ψ x : perp h) :
          EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ) *
        Complex.exp (chartExponentC β ν h g (tfield d (s * m') ν ψ))) ψ
    ∂(Measure.pi fun _ : Torus d (s * m') => γ₀)

/-- **The bound for complex sources of norm at most one**, in the form read by the Mayer layer. -/
theorem gasTermC_bd {β ν g γ κ p ε εs κ0 κ1 : ℝ} (hβ : 0 < β) (hg : 0 < g)
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
    (hεs0 : 0 ≤ εs) (hεs : εs ≤ (1 + 2 * d) * s ^ d * ε) (hκ01 : 1 + κ0 + κ1 ≤ κ)
    (hκ01' : 0 ≤ κ0 + κ1) :
    ∀ g' : Torus d (s * m') → Fin N → ℂ, ∑ x, ∑ i, ‖g' x i‖ ≤ 1 →
      ∀ (X : NePoly (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b),
        ‖gasTermC e β ν p X g' Φ‖ ≤
          (2 * ((1 + 2 * d) * s ^ d * ε)) * Real.exp (-(κ0 + κ1) * stSize X.1) :=
  fun g' hg1 X Φ => norm_gasTermC_le hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e hsite hbond hsrc
    hεs0 hεs hκ01 hκ01' X g' hg1 Φ

/-- The coefficients of the source are bounded. -/
theorem bdd_blockSrc {β ν g γ κ p εs : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (hsrc : ∀ (x : Torus d (s * m')) (i : Fin N), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1SiteSrcHalo e β ν x i H) ≤ εs)
    (x : Torus d (s * m')) (i : Fin N) (X : NePoly (Torus d m')) :
    Bdd (fun Φ : ∀ b, BlockSpace d s m' (perp h) b => ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ)) :=
  ⟨εs * Real.exp (-(κ * X.1.card)), fun Φ => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_blockSrc_le hg hgν hβ hq (Nat.pos_of_ne_zero (NeZero.ne s)) hκ hγκ hp hρ e x i
      (hsrc x i) X.1 Φ⟩

end Cut

section Identity

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- The exponent of the cutoff integrand, with clipped pieces: the sum of the source-free site
and bond pieces and of the source pieces weighted by `g`. -/
noncomputable def kfClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (g : Torus d (s * m') → Fin N → ℂ) (ψ : Torus d (s * m') → perp h) : ℂ :=
  ((∑ x, ∑ H, f1SiteHaloClip e β ν (fun _ _ => 0) x H p ψ +
      ∑ x, ∑ μ : Fin d, ∑ H, f1BondHaloClip e β ν x μ H p ψ : ℝ) : ℂ) +
    ∑ x, ∑ i, g x i * ((∑ H, f1SiteSrcHaloClip e β ν x i H p ψ : ℝ) : ℂ)

theorem measurable_kfClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (g : Torus d (s * m') → Fin N → ℂ) : Measurable (kfClip e β ν p g) := by
  unfold kfClip
  refine Measurable.add (Complex.measurable_ofReal.comp ?_) ?_
  · refine Measurable.add (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun H _ =>
      measurable_f1SiteHaloClip e β ν _ x H p)
      (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun μ _ =>
        Finset.measurable_sum _ fun H _ => measurable_f1BondHaloClip e β ν x μ H p)
  · refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun i _ => ?_
    refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
    refine Finset.measurable_sum _ fun H _ => ?_
    exact (measurable_kf0HaloTerm ν β _ _ _ H).comp (measurable_clipField p)

/-- **Regrouping.**  The activities `H_X(g)`, `X` nonempty, add up to the exponent of the cutoff
integrand at the site configuration. -/
theorem sum_gasTermC {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (gc : Torus d (s * m') → Fin N → ℂ)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    ∑ X : NePoly (Torus d m'), gasTermC e β ν p X gc Φ = kfClip e β ν p gc (toSites Φ) := by
  have hreal := sum_blockActivity (n := n) (s := s) (m' := m') hβ hg hgν hν1 hγ hq hκ hγκ hp hn
    hρ1 hρ e (fun _ _ => (0 : ℝ)) Φ
  unfold gasTermC kfClip
  rw [Finset.sum_add_distrib, ← Complex.ofReal_sum, hreal]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_blockSrc]

end Identity

section Main

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **The all-plus, all-small sector as a gas at a complex source (b).**  For a complex source of
`ℓ¹` norm below one, the cutoff integral is `(1 - τ)^{|Λ|} e^{⟨g, h⟩}` times the exponential of the
sum, over the block sets `Y`, of the local terms `P(Y)(g)` of the polymer gas of the Mayer
activities of the regrouped block activities at the source `g`; and the local terms are bounded as
in `block_gas`, with `H₀ = 2 (1 + 2d) s^d ε`. -/
theorem kf0CutIntegral_eq {β ν g γ κ p ε εs κ0 κ1 κ' : ℝ} (hβ : 0 < β) (hg : 0 < g)
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
    (hεs0 : 0 ≤ εs) (hεs : εs ≤ (1 + 2 * d) * s ^ d * ε)
    (hq0 : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκg : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ 2 * ((1 + 2 * d) * s ^ d * ε))
    (hH0log : 2 * ((1 + 2 * d) * s ^ d * ε) ≤ Real.log 2)
    (hH0K : 2 * ((1 + 2 * d) * s ^ d * ε) * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (hκ01 : 1 + κ0 + κ1 ≤ κ)
    (γ₀ : Measure (perp h)) [IsProbabilityMeasure γ₀] (hpos : γ₀ (smallSet p) ≠ 0)
    (gc : Torus d (s * m') → Fin N → ℂ) (hgc : ∑ x, ∑ i, ‖gc x i‖ < 1) :
    kf0CutIntegral (s := s) (m' := m') γ₀ β ν p gc =
      (((1 - γ₀.real (largeSet p)) ^ Fintype.card (Torus d (s * m')) : ℝ) : ℂ) *
        Complex.exp (∑ x, ∑ i, gc x i * (h i : ℂ)) *
        Complex.exp (∑ Y : Finset (Torus d m'),
          kf0PY e β ν p (ProbabilityTheory.cond γ₀ (smallSet p)) Y gc) ∧
    ∀ b : Torus d m', ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d m'))).filter
        (fun Y => b ∈ Y),
      ‖kf0PY e β ν p (ProbabilityTheory.cond γ₀ (smallSet p)) Y gc‖ * Real.exp (κ' * stSize Y) ≤
        64 * Real.exp 1 * (2 * ((1 + 2 * d) * s ^ d * ε)) * Real.exp (-(2 * κ0)) := by
  have hκ01' : 0 ≤ κ0 + κ1 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have : IsProbabilityMeasure (ProbabilityTheory.cond γ₀ (smallSet p)) :=
    cond_smallSet_isProbabilityMeasure γ₀ p hpos
  set pc := ProbabilityTheory.cond γ₀ (smallSet p) with hpc
  have hbd := gasTermC_bd hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e hsite hbond hsrc hεs0 hεs
    hκ01 hκ01'
  have hbsrc := bdd_blockSrc hβ hg hgν hq hκ hγκ hp hρ e hsrc (m' := m')
  have hgas := block_gas (Ω := BlockSpace d s m' (perp h)) (μ := blockRef (d := d) (s := s)
    (m' := m') pc) hq0 hκ0 hκ' hκg hH0 hH0log hH0K (fun X => gasTermC e β ν p X gc)
    (fun X => depOn_gasTermC e β ν p X gc) (fun X => measurable_gasTermC e β ν p X gc)
    (fun X Φ => hbd gc hgc.le X Φ)
  obtain ⟨r, -, -, hLog⟩ := kf0_marks_data hq0 hκ0 hκ' hκg hH0 hH0log hH0K e β ν p pc hbd hbsrc
    gc hgc
  refine ⟨?_, fun b => ?_⟩
  · -- the integral
    have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
    unfold kf0CutIntegral
    have hagree : Set.EqOn (fun ψ : Torus d (s * m') → perp h =>
          ((chartJac β (fun x => ((tfield d (s * m') ν ψ x : perp h) :
              EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ) *
            Complex.exp (chartExponentC β ν h gc (tfield d (s * m') ν ψ)))
        (fun ψ => Complex.exp (∑ x, ∑ i, gc x i * (h i : ℂ)) *
          Complex.exp (kfClip e β ν p gc ψ))
        (Set.pi Set.univ fun _ : Torus d (s * m') => smallSet p) := by
      intro ψ hψ
      have hψ' : ∀ y, ‖ψ y‖ ≤ p := fun y => hψ y (Set.mem_univ y)
      simp only
      rw [chart_integrand_eq_C hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e gc ψ hψ']
      unfold kfClip
      simp only [f1SiteHaloClip_eq_of_cutoff e β ν _ _ _ hψ', f1BondHaloClip_eq_of_cutoff e β ν _ _ _
        hψ', f1SiteSrcHaloClip, clipField_eq_self hψ']
    rw [Set.indicator_congr hagree, integral_indicator_small_eq_complex γ₀ p hpos,
      integral_const_mul]
    have hI : ∫ ψ, Complex.exp (kfClip e β ν p gc ψ)
        ∂(Measure.pi fun _ : Torus d (s * m') => pc) =
        ∫ Φ, Complex.exp (∑ X : NePoly (Torus d m'), gasTermC e β ν p X gc Φ)
          ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m') pc)) := by
      have hm : AEStronglyMeasurable (fun ψ => Complex.exp (kfClip e β ν p gc ψ))
          (Measure.map toSites (Measure.pi (blockRef (d := d) (s := s) (m' := m') pc))) :=
        (Complex.measurable_exp.comp (measurable_kfClip e β ν p gc)).aestronglyMeasurable
      rw [← map_toSites_pi pc, integral_map measurable_toSites.aemeasurable hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
      dsimp only
      rw [sum_gasTermC hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e gc Φ]
    rw [hI, hgas.1, hLog]
    ring
  · exact hgas.2 b

end Main

section Local

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **Analyticity of the local terms in the source on the unit `ℓ¹` ball.** -/
theorem kf0PY_analyticOnNhd {κ0 κ1 κ' H0 : ℝ}
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ H0) (hH0log : H0 ≤ Real.log 2) (hH0K : H0 * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))
    [IsProbabilityMeasure pc]
    (hbd : ∀ g : Torus d (s * m') → Fin N → ℂ, ∑ x, ∑ i, ‖g x i‖ ≤ 1 →
      ∀ (X : NePoly (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b),
        ‖gasTermC e β ν p X g Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * stSize X.1))
    (hbsrc : ∀ (x : Torus d (s * m')) (i : Fin N) (X : NePoly (Torus d m')),
      Bdd (fun Φ : ∀ b, BlockSpace d s m' (perp h) b => ((blockSrc e β ν p x i X.1 Φ : ℝ) : ℂ)))
    (Y : Finset (Torus d m')) :
    AnalyticOnNhd ℂ (kf0PY e β ν p pc Y)
      {g : Torus d (s * m') → Fin N → ℂ | ∑ x, ∑ i, ‖g x i‖ < 1} := by
  intro g₀ hg₀
  obtain ⟨r, hr, hAn, -⟩ := kf0_marks_data hq hκ0 hκ' hκ hH0 hH0log hH0K e β ν p pc hbd hbsrc g₀ hg₀
  have h0 : (0 : Torus d (s * m') × Fin N → ℂ) ∈
      polydisc (0 : Torus d (s * m') × Fin N → ℂ) (fun _ => r) := fun j => by simpa using hr
  have hF := hAn Y 0 h0
  have hL : AnalyticAt ℂ (fun g : Torus d (s * m') → Fin N → ℂ =>
      fun j : Torus d (s * m') × Fin N => g j.1 j.2 - g₀ j.1 j.2) g₀ := by
    refine AnalyticAt.pi fun j => ?_
    have hproj : AnalyticAt ℂ (fun g : Torus d (s * m') → Fin N → ℂ => g j.1 j.2) g₀ :=
      (((ContinuousLinearMap.proj j.2 : (Fin N → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.proj j.1 : (Torus d (s * m') → Fin N → ℂ) →L[ℂ]
          (Fin N → ℂ))).analyticAt g₀)
    exact hproj.sub analyticAt_const
  have hz : (fun j : Torus d (s * m') × Fin N => g₀ j.1 j.2 - g₀ j.1 j.2) = 0 := by
    funext j; simp
  have hcomp := AnalyticAt.comp (g := fun l : Torus d (s * m') × Fin N → ℂ =>
    kf0PY e β ν p pc Y (fun x i => g₀ x i + l (x, i))) (f := fun g : Torus d (s * m') → Fin N → ℂ =>
      fun j : Torus d (s * m') × Fin N => g j.1 j.2 - g₀ j.1 j.2) (x := g₀) (by rw [hz]; exact hF) hL
  have hfun : (fun g : Torus d (s * m') → Fin N → ℂ => kf0PY e β ν p pc Y g) =
      (fun l : Torus d (s * m') × Fin N → ℂ =>
        kf0PY e β ν p pc Y (fun x i => g₀ x i + l (x, i))) ∘
      (fun g : Torus d (s * m') → Fin N → ℂ =>
        fun j : Torus d (s * m') × Fin N => g j.1 j.2 - g₀ j.1 j.2) := by
    funext g
    simp only [Function.comp]
    congr 1
    funext x i
    ring
  convert hcomp using 1

/-- **Locality**: `P(Y)(g)` depends on `g` only at the sites of the blocks of `Y`. -/
theorem kf0PY_congr (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))
    (Y : Finset (Torus d m')) {g g' : Torus d (s * m') → Fin N → ℂ}
    (hg : ∀ x, blockOf d s m' x ∈ Y → g x = g' x) :
    kf0PY e β ν p pc Y g = kf0PY e β ν p pc Y g' := by
  unfold kf0PY
  refine PY_congr _ _ Y fun Z hZ => ?_
  unfold mayerK mayerAct polyAct
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  refine Finset.sum_congr rfl fun C hC => Finset.prod_congr rfl fun t ht => ?_
  have hsub : t.1 ⊆ Y := (sub_of_mem_Cfam hC ht).trans hZ
  show Complex.exp (gasTermC e β ν p t g Φ) - 1 = Complex.exp (gasTermC e β ν p t g' Φ) - 1
  rw [gasTermC_congr_src e β ν p t (fun x hx => hg x (hsub hx)) Φ]

/-- **Support**: `P(Y)(g) = 0` unless `Y` is a connected set of blocks. -/
theorem kf0PY_eq_zero_of_not_isAnimal (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (pc : Measure (perp h)) (g : Torus d (s * m') → Fin N → ℂ)
    (hz : ∀ (X : NePoly (Torus d m')), ¬ IsAnimal (blockGraph d m') X.1 →
      ∀ Φ : ∀ b, BlockSpace d s m' (perp h) b, gasTermC e β ν p X g Φ = 0)
    (Y : Finset (Torus d m')) (hY : ¬ IsAnimal (blockGraph d m') Y) :
    kf0PY e β ν p pc Y g = 0 := by
  unfold kf0PY
  exact PY_shareBlock_eq_zero_of_not_isAnimal (blockGraph d m') _
    (fun Z hZ => mayerK_eq_zero_of_not_isAnimal (blockGraph d m')
      (blockRef (d := d) (s := s) (m' := m') pc) (fun X : NePoly (Torus d m') => X.1)
      (fun X => gasTermC e β ν p X g) hz Z hZ) Y hY

end Local

end Balaban.LargeField.KF0AllPlus
