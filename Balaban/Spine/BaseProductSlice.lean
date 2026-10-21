/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCarrierProduct
public import Balaban.Spine.BaseStepDataSplice

/-!
# The scale-`0` slice of the step data from a product-form carrier

For a product-form carrier (`BaseProductData`, LFR (II.7.4): one boundary exponent `b₀` for all the
Gaussian witnesses) the scale-`0` kernel is the `LFKernel` with
`K = ∏ z₁^N t₀ · ∑_w F^w₀ K̃^w₀(0)` and the total analytic boundary factor `b(g) - b(0)`
(`BaseProductData.baseKC_toInput`: `K e^{b} = baseKC` everywhere). `StepSlice0.ofProduct` gives the
slice of `StepData` at `k = 0`: kernel, `b_supp`, `rot_b`, `euclid_b`, `dom`, and the vacuum split
`b = b⁰ - (vacuum term)` with the vacuum constants as data. The bounds (S0) of `b` and `b⁰`
(`b_bound`, `b0_bound`, the ledger of BASE-KERNEL §3) and the one-step bound (S2) (`gauss`, LFR
Lemma II.7.8) are hypotheses of the constructor.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Slice

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {M K : ℕ} [NeZero M] {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  (D : BaseProductData M K k0 geo cs N)

/-- The remainder family of the product form with the source-free exponent: `K̃^w_0(0) = Kt^w e^{Re b(0)}`. -/
noncomputable def BaseProductData.Kt0 (a : LocalHistory S n M K) (w : BaseW a 0)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  D.Kt a w o x hv * Real.exp (D.b a 0 o x hv).re

/-- **The scale-`0` kernel of a product-form carrier**: `K = ∏ z₁^N t₀ · ∑_w F^w₀ K̃^w₀(0)`, boundary
factor `b(g) - b(0)`. -/
noncomputable def BaseProductData.ker (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (a : LocalHistory S n M K) :
    LFKernel (OutT N R a (0 + 1)) (NewCfg N a 0) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N) where
  K o x hv := gaussProd N a 0 cs o x * baseSumOf cs a (fun w => D.Kt0 a w) o x hv
  b o x hv g := D.b a g o x hv - D.b a 0 o x hv
  K_nonneg o x hv := mul_nonneg (gaussProd_nonneg N a 0 cs hz hc o x)
    (baseSumOf_nonneg cs a (fun w o x hv => mul_nonneg (D.Kt_nonneg _ w o x hv)
      (Real.exp_pos _).le) o x hv)
  measurable_K hv := (measurable_gaussProd_pair a 0 cs).mul
    (measurable_baseSumOf cs a (fun w hv => (D.Kt_meas a w hv).mul
      (Real.measurable_exp.comp (Complex.measurable_re.comp (D.b_meas a 0 hv)))) hv)
  measurable_b hv g := (D.b_meas a g hv).sub (D.b_meas a 0 hv)
  analytic_b o x hv := (D.b_analytic a o x hv).sub analyticOnNhd_const
  real_b o x hv g hg hr := by
    rw [Complex.sub_im, D.b_real a g o x hv hg hr, D.b_zero_real a o x hv, sub_zero]

/-- The Gaussian witnesses at the scale `0` for the product form. -/
noncomputable def BaseProductData.wit (a : LocalHistory S n M K) : GaussWit N R a 0 :=
  open Classical in
  { W := BaseW a 0
    F := fun w u => baseF a 0 (cs.delta 0) w u
    Kt := fun w o x hv => D.Kt0 a w o x hv }

/-- **The scale-`0` slice of the step data from a product-form carrier** (LFR Definition II.7.6,
(II.7.4); the exponent `b` is the total `b(g) - b(0)`). The vacuum constants `vE, vEpp, vEppp` are
data (the creating-step constants of the vacuum split `b = b⁰ - (vacuum term)`, ruling R5). The
hypotheses are the bounds (S0) of `b` and `b⁰` on `χ^new_0` (`hb`, `hb0`; the ledger of
BASE-KERNEL §3) and the one-step bound (S2) (`hgauss`, LFR Lemma II.7.8). -/
noncomputable def StepSlice0.ofProduct (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (vE vEpp vEppp : LocalHistory S n M K → ℝ) (κ0 : LocalHistory S n M K → ℝ)
    (hb : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
      ∀ (Z' : H.Comp (0 + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
      ChiNewAt geo cs H 0 Z' o x →
      ‖(D.ker hz hc (H.localHistory M K (0 + 1) Z')).b o x hv g‖ ≤
        (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
          volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
            z ∉ (H.localHistory M K (0 + 1) Z').Z 0})
    (hb0 : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
      ∀ (Z' : H.Comp (0 + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
      ChiNewAt geo cs H 0 Z' o x →
      ‖(D.ker hz hc (H.localHistory M K (0 + 1) Z')).b o x hv g +
          (stepVacuumTerm (H.localHistory M K (0 + 1) Z') 0
            (vE (H.localHistory M K (0 + 1) Z')) (vEpp (H.localHistory M K (0 + 1) Z'))
            (vEppp (H.localHistory M K (0 + 1) Z')) : ℂ)‖ ≤
        (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
          volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
            z ∉ (H.localHistory M K (0 + 1) Z').Z 0})
    (hgauss : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)),
      GaussStepSpec cs R (H.localHistory M K (0 + 1) Z') 0 (κ0 (H.localHistory M K (0 + 1) Z'))
        (D.ker hz hc (H.localHistory M K (0 + 1) Z')) (D.wit (H.localHistory M K (0 + 1) Z'))) :
    StepSlice0 k0 geo cs N κ0 where
  ker := D.ker hz hc
  wit := D.wit
  b_supp := fun a o x hv g g' h => by
    show D.b a g o x hv - D.b a 0 o x hv = D.b a g' o x hv - D.b a 0 o x hv
    rw [D.b_suppV a g g' o x hv h]
  rot_K := fun a ρ o x hv => by
    show gaussProd N a 0 cs (rotOut ρ o) (rotSub ρ x) *
        baseSumOf cs a (fun w => D.Kt0 a w) (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      gaussProd N a 0 cs o x * baseSumOf cs a (fun w => D.Kt0 a w) o x hv
    have h0 : rotG ρ (0 : GIdx S n M K N → ℂ) = 0 := by funext p; simp [rotG]
    rw [gaussProd_rot, baseSumOf_rot cs a (Kt := fun w => D.Kt0 a w) (Kt' := fun w => D.Kt0 a w) ρ
      (fun w o x hv => by
        unfold BaseProductData.Kt0
        have := D.b_rot a 0 ρ o x hv
        rw [h0] at this
        rw [D.Kt_rot a w ρ o x hv, this])]
  rot_b := fun a ρ o x hv g => by
    show D.b a (rotG ρ g) (rotOut ρ o) (rotSub ρ x) (ρ hv) -
        D.b a 0 (rotOut ρ o) (rotSub ρ x) (ρ hv) = D.b a g o x hv - D.b a 0 o x hv
    have h0 : rotG ρ (0 : GIdx S n M K N → ℂ) = 0 := by funext p; simp [rotG]
    have := D.b_rot a 0 ρ o x hv
    rw [h0] at this
    rw [D.b_rot a g ρ o x hv, this]
  euclid_K := fun σ a a' hI hk o o' x x' hv ho hx => by
    have h1 := D.euclid_Kt σ.toTorusSym a a' hI hk o o' x x' hv ho hx
    have h2 := D.b_euclid σ.toTorusSym a a' hI hk 0 0 o o' x x' hv ho hx (fun _ _ => rfl)
    show gaussProd N a' 0 cs o' x' * baseSumOf cs a' (fun w => D.Kt0 a' w) o' x' hv =
      gaussProd N a 0 cs o x * baseSumOf cs a (fun w => D.Kt0 a w) o x hv
    have e1 := baseSumOf_mul_const cs a' (fun w => D.Kt a' w)
      (fun o x hv => Real.exp (D.b a' 0 o x hv).re) o' x' hv
    have e2 := baseSumOf_mul_const cs a (fun w => D.Kt a w)
      (fun o x hv => Real.exp (D.b a 0 o x hv).re) o x hv
    have f1 : (fun w => D.Kt0 a' w) = fun w o x hv =>
        D.Kt a' w o x hv * Real.exp (D.b a' 0 o x hv).re := rfl
    have f2 : (fun w => D.Kt0 a w) = fun w o x hv =>
        D.Kt a w o x hv * Real.exp (D.b a 0 o x hv).re := rfl
    rw [f1, f2, e1, e2, h2]
    calc _ = (gaussProd N a' 0 cs o' x' * baseSumOf cs a' (fun w => D.Kt a' w) o' x' hv) *
          Real.exp (D.b a 0 o x hv).re := by ring
      _ = _ := by rw [h1]; ring
  euclid_b := fun σ a a' hI hk o o' x x' hv g g' ho hx hg => by
    show D.b a' g' o' x' hv - D.b a' 0 o' x' hv = D.b a g o x hv - D.b a 0 o x hv
    rw [D.b_euclid σ.toTorusSym a a' hI hk g g' o o' x x' hv ho hx hg,
      D.b_euclid σ.toTorusSym a a' hI hk 0 0 o o' x x' hv ho hx (fun _ _ => rfl)]
  vacE := vE
  vacEpp := vEpp
  vacEppp := vEppp
  b0 := fun a o x hv g => (D.ker hz hc a).b o x hv g + (stepVacuumTerm a 0 (vE a) (vEpp a) (vEppp a) : ℂ)
  b_vac := fun a o x hv g => by
    show _ = _ + _ - _
    ring
  b0_bound := hb0
  b_bound := hb
  dom := fun H hH Z' o x hv hn => by
    classical
    show gaussProd N (H.localHistory M K (0 + 1) Z') 0 cs o x *
        baseSumOf cs (H.localHistory M K (0 + 1) Z') (fun w => D.Kt0 (H.localHistory M K (0 + 1) Z') w)
          o x hv = 0
    have : baseSumOf cs (H.localHistory M K (0 + 1) Z')
        (fun w => D.Kt0 (H.localHistory M K (0 + 1) Z') w) o x hv = 0 := by
      unfold baseSumOf
      exact Finset.sum_eq_zero fun w _ => by
        dsimp only
        unfold BaseProductData.Kt0
        rw [D.Kt_dom H hH Z' w o x hv hn, zero_mul, mul_zero]
    rw [this, mul_zero]
  gauss := hgauss

end Slice

end Balaban.LargeField
