/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRHeavyPt
public import Balaban.LargeField.Base.KF0FRJacSite
public import Balaban.LargeField.Base.KF0FRGauss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRHeavySite`: the one-site integrals of the heavy bound (route FR, (H5))

`notes/phase1/KF0-FR.md` (H5). The integral of the heavy bound factorizes over the sites, up to the
chart weights of a set `D'` of sites, which the Jacobian integral (`lintegral_jac_sites`) removes.
This file bounds the one-site factors, for a sheet factor `L : Bool → ℝ` and a weight `X ≥ 0` of the
Gaussian variable:

* `lintegral_frBern`: `∫ f dπ_ε = f(+)/(1+ε) + ε f(-)/(1+ε)`;
* `lintegral_ord_le`, `sup_ord_le`: an ordinary site costs `L(+) K` (and `(2π)^{-n/2} L(+) K` as a
  density bound) when `X ≤ K` on `|ψ| ≤ p`;
* `lintegral_heavy_le`, `sup_heavy_le`: a heavy site costs
  `L(+) ∫_{|ψ|>p} X dγ + ε (1+ε)^{-1} L(-) ∫ X dγ`;
* `lintegral_jac_sites_le`: the Jacobian integral with per-site bounds.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

/-- The one-site exponential weight `e^{a|ψ| + θ|ψ|²}`. -/
def frEx (a θ : ℝ) (ψ : perp h) : ℝ := Real.exp (a * ‖ψ‖ + θ * ‖ψ‖ ^ 2)

theorem frEx_pos (a θ : ℝ) (ψ : perp h) : 0 < frEx h a θ ψ := Real.exp_pos _

theorem one_le_frEx {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) (ψ : perp h) : 1 ≤ frEx h a θ ψ :=
  Real.one_le_exp (by positivity)

theorem frEx_le_of_norm_le {a θ p : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) {ψ : perp h} (hψ : ‖ψ‖ ≤ p) :
    frEx h a θ ψ ≤ Real.exp (a * p + θ * p ^ 2) := by
  unfold frEx
  refine Real.exp_le_exp.2 (add_le_add (mul_le_mul_of_nonneg_left hψ ha)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hψ 2) hθ))

theorem measurable_frEx (a θ : ℝ) : Measurable (frEx h a θ) := by unfold frEx; fun_prop

/-! ### The sheet law -/

theorem lintegral_frBern {ε : ℝ} (f : Bool → ℝ≥0∞) :
    ∫⁻ b, f b ∂(frBern ε) =
      ENNReal.ofReal (1 / (1 + ε)) * f true + ENNReal.ofReal (ε / (1 + ε)) * f false := by
  unfold frBern
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac]
  rfl

theorem lintegral_frSiteMeasure {ε : ℝ} (f : perp h × Bool → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ w, f w ∂(frSiteMeasure h ε) = ∫⁻ ψ, ∫⁻ b, f (ψ, b) ∂(frBern ε) ∂(oneSiteGaussian (perp h)) :=
  lintegral_prod f hf.aemeasurable

/-! ### One-site bounds -/

variable {p : ℝ}

/-- **An ordinary site**: the integrand vanishes unless `σ = +`, `|ψ| ≤ p`. -/
theorem lintegral_ord_le {ε : ℝ} (hε : 0 ≤ ε) (L : Bool → ℝ) (X : perp h → ℝ) {K : ℝ}
    (hX : ∀ ψ : perp h, ‖ψ‖ ≤ p → L true * X ψ ≤ K) :
    ∫⁻ w, (frOrd h p).indicator 1 w * ENNReal.ofReal (L w.2 * X w.1) ∂(frSiteMeasure h ε) ≤
      ENNReal.ofReal K := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  have hpt : ∀ w : perp h × Bool, (frOrd h p).indicator 1 w * ENNReal.ofReal (L w.2 * X w.1) ≤
      ENNReal.ofReal K := by
    intro w
    by_cases hw : w ∈ frOrd h p
    · rw [Set.indicator_of_mem hw, Pi.one_apply, one_mul]
      obtain ⟨hψ, hσ⟩ := hw
      rw [hσ]
      exact ENNReal.ofReal_le_ofReal (hX w.1 hψ)
    · rw [Set.indicator_of_notMem hw, zero_mul]; exact zero_le
  calc _ ≤ ∫⁻ _w, ENNReal.ofReal K ∂(frSiteMeasure h ε) := lintegral_mono hpt
    _ = ENNReal.ofReal K := by simp

/-- **An ordinary site, density form.** -/
theorem sup_ord_le {ε : ℝ} (hε : 0 ≤ ε) (L : Bool → ℝ) (X : perp h → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hX : ∀ ψ : perp h, ‖ψ‖ ≤ p → L true * X ψ ≤ K) (ψ : perp h) :
    (∫⁻ b, (frOrd h p).indicator 1 (ψ, b) * ENNReal.ofReal (L b * X ψ) ∂(frBern ε)) *
        ENNReal.ofReal (gDens h ψ) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) * K) := by
  have hprob := isProbabilityMeasure_frBern hε
  have hpt : ∀ b : Bool, (frOrd h p).indicator 1 (ψ, b) * ENNReal.ofReal (L b * X ψ) ≤
      ENNReal.ofReal K := by
    intro b
    by_cases hw : (ψ, b) ∈ frOrd h p
    · rw [Set.indicator_of_mem hw, Pi.one_apply, one_mul]
      obtain ⟨hψ, hσ⟩ := hw
      simp only at hσ hψ
      rw [hσ]
      exact ENNReal.ofReal_le_ofReal (hX ψ hψ)
    · rw [Set.indicator_of_notMem hw, zero_mul]; exact zero_le
  have h1 : ∫⁻ b, (frOrd h p).indicator 1 (ψ, b) * ENNReal.ofReal (L b * X ψ) ∂(frBern ε) ≤
      ENNReal.ofReal K :=
    (lintegral_mono hpt).trans (by rw [lintegral_const, measure_univ, mul_one])
  have h2 : gDens h ψ ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) := by
    unfold gDens
    have : Real.exp (-(1 / 2) * ‖ψ‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖ψ‖])
    calc _ ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := mul_one _
  calc _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((2 * Real.pi) ^
        (-(Module.finrank ℝ (perp h) : ℝ) / 2)) :=
        mul_le_mul' h1 (ENNReal.ofReal_le_ofReal h2)
    _ = _ := by rw [← ENNReal.ofReal_mul hK, mul_comm]

/-- **A heavy site**: `σ = -`, or `σ = +` with `|ψ| > p`. -/
theorem lintegral_heavy_le {ε : ℝ} (hε : 0 ≤ ε) (L : Bool → ℝ) (hL : ∀ b, 0 ≤ L b)
    (X : perp h → ℝ) (hXm : Measurable X) :
    ∫⁻ w, (frOrd h p)ᶜ.indicator 1 w * ENNReal.ofReal (L w.2 * X w.1) ∂(frSiteMeasure h ε) ≤
      ENNReal.ofReal (L true) * ∫⁻ ψ, Set.indicator {ψ : perp h | p < ‖ψ‖}
          (fun ψ => ENNReal.ofReal (X ψ)) ψ ∂(oneSiteGaussian (perp h)) +
        ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false) *
          ∫⁻ ψ, ENNReal.ofReal (X ψ) ∂(oneSiteGaussian (perp h)) := by
  have hm : Measurable fun w : perp h × Bool =>
      (frOrd h p)ᶜ.indicator 1 w * ENNReal.ofReal (L w.2 * X w.1) := by
    refine (measurable_one.indicator (measurableSet_frOrd h p).compl).mul ?_
    exact ENNReal.measurable_ofReal.comp ((measurable_from_top.comp measurable_snd).mul
      (hXm.comp measurable_fst))
  rw [lintegral_frSiteMeasure h _ hm]
  have hpt : ∀ ψ : perp h, ∫⁻ b, (frOrd h p)ᶜ.indicator 1 (ψ, b) *
      ENNReal.ofReal (L b * X ψ) ∂(frBern ε) ≤
      ENNReal.ofReal (L true) * Set.indicator {ψ : perp h | p < ‖ψ‖}
          (fun ψ => ENNReal.ofReal (X ψ)) ψ +
        ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false) * ENNReal.ofReal (X ψ) := by
    intro ψ
    rw [lintegral_frBern]
    have ht : ENNReal.ofReal (1 / (1 + ε)) * ((frOrd h p)ᶜ.indicator 1 (ψ, true) *
        ENNReal.ofReal (L true * X ψ)) ≤
        ENNReal.ofReal (L true) * Set.indicator {ψ : perp h | p < ‖ψ‖}
          (fun ψ => ENNReal.ofReal (X ψ)) ψ := by
      by_cases hψ : p < ‖ψ‖
      · rw [Set.indicator_of_mem (show ψ ∈ {ψ : perp h | p < ‖ψ‖} from hψ),
          Set.indicator_of_mem (show (ψ, true) ∈ (frOrd h p)ᶜ from fun hw => by
            simp only [frOrd, Set.mem_ofPred_eq] at hw; linarith [hw.1]),
          Pi.one_apply, one_mul, ENNReal.ofReal_mul (hL true)]
        have : ENNReal.ofReal (1 / (1 + ε)) ≤ 1 := by
          rw [ENNReal.ofReal_le_one]; rw [div_le_one (by linarith)]; linarith
        calc _ ≤ 1 * (ENNReal.ofReal (L true) * ENNReal.ofReal (X ψ)) := by gcongr
          _ = _ := one_mul _
      · rw [Set.indicator_of_notMem (show (ψ, true) ∉ (frOrd h p)ᶜ from fun hw => hw
          ⟨not_lt.1 hψ, rfl⟩), zero_mul, mul_zero]
        exact zero_le
    have hf : ENNReal.ofReal (ε / (1 + ε)) * ((frOrd h p)ᶜ.indicator 1 (ψ, false) *
        ENNReal.ofReal (L false * X ψ)) ≤
        ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false) * ENNReal.ofReal (X ψ) := by
      rw [mul_assoc]
      refine mul_le_mul' le_rfl ?_
      calc _ ≤ 1 * ENNReal.ofReal (L false * X ψ) := by
            gcongr
            unfold Set.indicator; split_ifs <;> simp
        _ = _ := by rw [one_mul, ENNReal.ofReal_mul (hL false)]
    exact add_le_add ht hf
  calc _ ≤ ∫⁻ ψ, (ENNReal.ofReal (L true) * Set.indicator {ψ : perp h | p < ‖ψ‖}
          (fun ψ => ENNReal.ofReal (X ψ)) ψ +
        ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false) * ENNReal.ofReal (X ψ))
        ∂(oneSiteGaussian (perp h)) := lintegral_mono hpt
    _ = _ := by
        have hms : MeasurableSet {ψ : perp h | p < ‖ψ‖} :=
          measurableSet_lt measurable_const measurable_norm
        have hm1 : Measurable fun ψ : perp h => Set.indicator {ψ : perp h | p < ‖ψ‖}
            (fun ψ => ENNReal.ofReal (X ψ)) ψ :=
          (ENNReal.measurable_ofReal.comp hXm).indicator hms
        have hm2 : Measurable fun ψ : perp h => ENNReal.ofReal (X ψ) :=
          ENNReal.measurable_ofReal.comp hXm
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2]

/-- **A heavy site, density form**, for `X = e^{a|ψ| + θ|ψ|²}`, `θ ≤ 1/8`: the density bound is
`(2π)^{-n/2} e^{a²} (L(+) + ε(1+ε)^{-1} L(-))`. -/
theorem sup_heavy_le {ε a θ : ℝ} (hε : 0 ≤ ε) (hθ : θ ≤ 1 / 8) (L : Bool → ℝ)
    (hL : ∀ b, 0 ≤ L b) (ψ : perp h) :
    (∫⁻ b, (frOrd h p)ᶜ.indicator 1 (ψ, b) * ENNReal.ofReal (L b * frEx h a θ ψ) ∂(frBern ε)) *
        ENNReal.ofReal (gDens h ψ) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) *
        Real.exp (a ^ 2) * (L true + ε / (1 + ε) * L false)) := by
  have hind : ∀ b : Bool, (frOrd h p)ᶜ.indicator 1 (ψ, b) * ENNReal.ofReal (L b * frEx h a θ ψ) ≤
      ENNReal.ofReal (L b * frEx h a θ ψ) := by
    intro b
    calc _ ≤ 1 * ENNReal.ofReal (L b * frEx h a θ ψ) := by
          gcongr; unfold Set.indicator; split_ifs <;> simp
      _ = _ := one_mul _
  have hX := (frEx_pos h a θ ψ).le
  have hε1 : 0 ≤ ε / (1 + ε) := by positivity
  have h1 : ∫⁻ b, (frOrd h p)ᶜ.indicator 1 (ψ, b) * ENNReal.ofReal (L b * frEx h a θ ψ)
      ∂(frBern ε) ≤ ENNReal.ofReal ((L true + ε / (1 + ε) * L false) * frEx h a θ ψ) := by
    rw [lintegral_frBern]
    have h11 : ENNReal.ofReal (1 / (1 + ε)) ≤ 1 := by
      rw [ENNReal.ofReal_le_one, div_le_one (by linarith)]; linarith
    calc _ ≤ 1 * ENNReal.ofReal (L true * frEx h a θ ψ) +
          ENNReal.ofReal (ε / (1 + ε)) * ENNReal.ofReal (L false * frEx h a θ ψ) :=
          add_le_add (mul_le_mul' h11 (hind true)) (mul_le_mul' le_rfl (hind false))
      _ = _ := by
          rw [one_mul, ← ENNReal.ofReal_mul hε1, ← ENNReal.ofReal_add
            (mul_nonneg (hL true) hX) (mul_nonneg hε1 (mul_nonneg (hL false) hX))]
          congr 1; ring
  have h2 := gaussDens_mul_exp_le (E := perp h) (a := a) hθ ‖ψ‖
  have hL0 : 0 ≤ L true + ε / (1 + ε) * L false :=
    add_nonneg (hL true) (mul_nonneg hε1 (hL false))
  calc _ ≤ ENNReal.ofReal ((L true + ε / (1 + ε) * L false) * frEx h a θ ψ) *
        ENNReal.ofReal (gDens h ψ) := mul_le_mul' h1 le_rfl
    _ = ENNReal.ofReal ((L true + ε / (1 + ε) * L false) *
          ((2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) *
            Real.exp (-(1 / 2) * ‖ψ‖ ^ 2) * Real.exp (a * ‖ψ‖ + θ * ‖ψ‖ ^ 2))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hL0 hX)]
        congr 1
        unfold gDens frEx
        ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ ≤ (L true + ε / (1 + ε) * L false) * ((2 * Real.pi) ^
              (-(Module.finrank ℝ (perp h) : ℝ) / 2) * Real.exp (a ^ 2)) :=
              mul_le_mul_of_nonneg_left h2 hL0
          _ = _ := by ring

/-! ### The Jacobian integral with per-site bounds -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Jacobian integral with per-site bounds**: if the sites off `D` integrate to at most
`c_y`, the sites of `D` have density bounds `A_y` with `A_y J ≤ c_y`, and the Jacobian factor is at
most `J^{|D|}`, then the integral is at most `∏_y c_y`. -/
theorem lintegral_jac_sites_le (hh : ‖h‖ = 1) (S : Matrix ι ι ℝ) (D : Finset ι)
    (hSD : IsUnit (S.submatrix (Subtype.val : D → ι) Subtype.val).det) {ε : ℝ} (hε : 0 ≤ ε)
    (a : ι → perp h × Bool → ℝ≥0∞) (ha : ∀ x, Measurable (a x)) (A : ι → ℝ≥0∞)
    (hA : ∀ x ∈ D, ∀ ψ, (∫⁻ b, a x (ψ, b) ∂(frBern ε)) * ENNReal.ofReal (gDens h ψ) ≤ A x)
    (J : ℝ≥0∞)
    (hJ : (ENNReal.ofReal |(S.submatrix (Subtype.val : D → ι) Subtype.val).det ^ (N - 1)|)⁻¹ *
      (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ D.card ≤ J ^ D.card)
    (c : ι → ℝ≥0∞) (hc1 : ∀ y ∉ D, ∫⁻ w, a y w ∂(frSiteMeasure h ε) ≤ c y)
    (hc2 : ∀ y ∈ D, A y * J ≤ c y) :
    ∫⁻ ω : ι → perp h × Bool, (∏ x, a x (ω x)) *
        ∏ z ∈ D, ENNReal.ofReal (chartWeight h (matAct S (fun y => (ω y).1) z))
        ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤ ∏ y, c y := by
  refine (lintegral_jac_sites h hh S D hSD hε a ha A hA).trans ?_
  have hout : ∏ x : {x // x ∉ D}, ∫⁻ w, a x w ∂(frSiteMeasure h ε) ≤ ∏ x ∈ Dᶜ, c x := by
    rw [Finset.prod_subtype Dᶜ (p := fun x => x ∉ D) (fun x => by simp)]
    exact Finset.prod_le_prod fun x _ => hc1 x.1 x.2
  have hin : (∏ x : D, A x) * J ^ D.card ≤ ∏ x ∈ D, c x := by
    have e : (∏ x : D, A x) * J ^ D.card = ∏ x : D, (A x * J) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    rw [e, ← Finset.prod_coe_sort D c]
    exact Finset.prod_le_prod fun x _ => hc2 x.1 x.2
  calc (∏ x : {x // x ∉ D}, ∫⁻ w, a x w ∂(frSiteMeasure h ε)) * (∏ x : D, A x) *
        ((ENNReal.ofReal |(S.submatrix (Subtype.val : D → ι) Subtype.val).det ^ (N - 1)|)⁻¹ *
          (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ D.card)
      ≤ (∏ x ∈ Dᶜ, c x) * (∏ x : D, A x) * J ^ D.card := by gcongr
    _ = (∏ x ∈ Dᶜ, c x) * ((∏ x : D, A x) * J ^ D.card) := by ring
    _ ≤ (∏ x ∈ Dᶜ, c x) * ∏ x ∈ D, c x := by gcongr
    _ = ∏ y, c y := by rw [mul_comm, Finset.prod_mul_prod_compl]

end

end Balaban.LargeField.KF0FR
