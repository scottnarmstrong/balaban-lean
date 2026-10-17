/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedKernel
public import Balaban.LargeField.R.RRemovedWindowGen

/-!
# The window integral: the removed kernel unfolded (Lemma III.8.7 (1)) (W905)

`notes/phase1/LF4R-PLAN.md`, leaf 6, step (1).  The integral (III.8.5) of the removed kernel over
the outputs on `Z` and the internal variables is bounded by `e^{EZ}` times the integral, over the
outputs on `Z` (the outer `ψ_k↾Z₀` only enters `χ_{Z₀}`), the internal variables and the inner
variable `ψ_k↾Z₀` of `∫ dψ_k↾Z₀`, of the non-negative function

`χ_{Z₀}(o) · K^pre χ̃_k χ_S χ⁰ χ'' (ψ_k↾Z₀ := w, ψ_k↾Z₀ᶜ := o↾Z₀ᶜ; x) e^{Re b^pre} / ∫ dψ_k↾Z₀ ρ_{k,0}(Z)`.

* `removedKernel_absW_le`: the pointwise form;
* `removedKernel_lintegral_le`: the integral over the product space.

Inputs: `hb` (the exponent `b^pre` does not read `ψ_k↾Z₀`, the premise `hb0` of the locality
files in the form of the pre-operator) and `u ≤ 1` (`u = χ_{Z''}` is a characteristic function).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory ENNReal

section Unfold

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  (P : OpPkg N R a k) {t s z w : OutT N R a k → SubCfg N a k P.A → ℝ} {u c0 : OutT N R a k → ℝ}
  {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ} (EZ : ℝ)
  (ht : ∀ o x, 0 ≤ t o x) (hs : ∀ o x, 0 ≤ s o x) (hz : ∀ o x, 0 ≤ z o x)
  (hw : ∀ o x, 0 ≤ w o x) (hu : ∀ o, 0 ≤ u o) (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y)
  (htm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => t p.1 p.2)
  (hsm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => s p.1 p.2)
  (hzm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => z p.1 p.2)
  (hwm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => w p.1 p.2)
  (hum : Measurable u) (hc0m : Measurable c0)
  (hrm : Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2)

theorem ofReal_integral_le_lintegral_ofReal' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall hf)).le
  · rw [integral_undef h]; simp

/-- **The removed kernel unfolded, pointwise** (step (1)): for `o`, `x`, `h`, `g`, with `b^pre`
not reading `ψ_k↾Z₀` and `χ_{Z''} ≤ 1`,
`K^rem e^{Re b} ≤ e^{EZ} ∫ dw χ_{Z₀}(o) K^pre-to-R(w, o↾Z₀ᶜ; x) e^{Re b^pre} / D(o)`. -/
theorem removedKernel_absW_le (hu1 : ∀ o, u o ≤ 1)
    (hb : ∀ (o o' : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N))
      (g : GIdx S n M K N → ℂ),
      (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 → P.T.b o x hv g = P.T.b o' x hv g)
    (o : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
      hrm).absW o x hv g ≤
      ENNReal.ofReal (Real.exp EZ) *
        ∫⁻ w', ENNReal.ofReal (c0 o *
          (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x hv *
            Real.exp (P.T.b (remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 o).2)) x hv g).re) /
          remDen a k Z0 r o) ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) := by
  set μ0 := outPartMeasure N (Vblk R a k) (· ∈ Z0) with hμ0
  set y := (remZeroSplit a k Z0 o).2 with hy
  set D := remDen a k Z0 r o with hD
  have hD0 : 0 ≤ D := remDen_nonneg a k Z0 hr o
  have hKf := toRKernel_nonneg a k P.T.K_nonneg ht hs hz hw (X := SubCfg N a k P.A)
  have hnn : ∀ w', 0 ≤ c0 o *
      (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0 (w', y)) x hv *
        Real.exp (P.T.b (remZeroMerge a k Z0 (w', y)) x hv g).re) / D := fun w' => by
    have := hKf (remZeroMerge a k Z0 (w', y)) x hv
    have := hc0 o
    positivity
  set A := ∫ w', c0 o *
      (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0 (w', y)) x hv *
        Real.exp (P.T.b (remZeroMerge a k Z0 (w', y)) x hv g).re) / D ∂μ0 with hA
  have hA0 : 0 ≤ A := integral_nonneg hnn
  have hbm : ∀ w', Real.exp (P.T.b o x hv g).re =
      Real.exp (P.T.b (remZeroMerge a k Z0 (w', y)) x hv g).re := fun w' => by
    rw [hb o (remZeroMerge a k Z0 (w', y)) x hv g (by rw [remZeroSplit_merge])]
  have hA' : A = c0 o * (∫ w', toRKernel a k P.T.K t s z w
        (remZeroMerge a k Z0 (w', y)) x hv ∂μ0) * Real.exp (P.T.b o x hv g).re / D := by
    have hpt : ∀ w', c0 o * (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0 (w', y)) x hv *
        Real.exp (P.T.b (remZeroMerge a k Z0 (w', y)) x hv g).re) / D =
        (c0 o * Real.exp (P.T.b o x hv g).re / D) *
          toRKernel a k P.T.K t s z w (remZeroMerge a k Z0 (w', y)) x hv := fun w' => by
      rw [← hbm w']; ring
    rw [hA]
    simp_rw [hpt]
    rw [integral_const_mul]
    ring
  have hkey : removedK a k Z0 (toRKernel a k P.T.K t s z w) u c0 r EZ o x hv *
      Real.exp (P.T.b o x hv g).re = Real.exp EZ * u o * A := by
    unfold removedK remNum
    rw [hA']
    ring
  have hle : Real.exp EZ * u o * A ≤ Real.exp EZ * A := by
    have := mul_le_mul_of_nonneg_left (hu1 o) (Real.exp_pos EZ).le
    nlinarith [mul_le_mul_of_nonneg_right this hA0]
  calc (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
        hrm).absW o x hv g
      = ENNReal.ofReal (removedK a k Z0 (toRKernel a k P.T.K t s z w) u c0 r EZ o x hv *
          Real.exp (P.T.b o x hv g).re) := rfl
    _ ≤ ENNReal.ofReal (Real.exp EZ * A) := by
        rw [hkey]; exact ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (Real.exp EZ) * ENNReal.ofReal A :=
        ENNReal.ofReal_mul (Real.exp_pos EZ).le
    _ ≤ _ := by
        gcongr
        exact ofReal_integral_le_lintegral_ofReal' hnn

/-- **The integral (III.8.5) of the removed kernel unfolded** (step (1)): for the parameters `par`
of the outputs on `V ∖ Z`, the integral of `K^rem e^{Re b}` over the outputs on `Z` and the
internal variables is at most `e^{EZ}` times the integral over `(ψ_k↾Z, x, w)` of the function
`F` (the right-hand side of `removedKernel_absW_le` at `o = o(ψ_k↾Z, par)`), against the product
of the Lebesgue measures (the inner variable `w = ψ_k↾Z₀` of `∫ dψ_k↾Z₀`). -/
theorem removedKernel_lintegral_le (hu1 : ∀ o, u o ≤ 1)
    (hb : ∀ (o o' : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N))
      (g : GIdx S n M K N → ℂ),
      (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 → P.T.b o x hv g = P.T.b o' x hv g)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (par : OutPar N R a k)
    (F : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) → ℝ≥0∞)
    (hF : ∀ oz x w', F (oz, x, w') = ENNReal.ofReal
      (c0 (mergeOut a k oz par) *
        (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0
            (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2)) x hv *
          Real.exp (P.T.b (remZeroMerge a k Z0
            (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2)) x hv g).re) /
        remDen a k Z0 r (mergeOut a k oz par))) :
    ∫⁻ oz, ∫⁻ x, (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm
        hum hc0m hrm).absW (mergeOut a k oz par) x hv g ∂(subMeasure N a k P.A)
      ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤
      ENNReal.ofReal (Real.exp EZ) * ∫⁻ p, F p ∂((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod
        ((subMeasure N a k P.A).prod (outPartMeasure N (Vblk R a k) (· ∈ Z0)))) := by
  classical
  have hFm : Measurable F := by
    have ho : Measurable fun p : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) =>
        mergeOut a k p.1 par := (measurable_mergeOut a k par).comp measurable_fst
    have hy : Measurable fun p : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) =>
        (remZeroSplit a k Z0 (mergeOut a k p.1 par)).2 :=
      measurable_snd.comp ((remZeroSplit a k Z0).measurable.comp ho)
    have hm : Measurable fun p : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) =>
        remZeroMerge a k Z0 (p.2.2, (remZeroSplit a k Z0 (mergeOut a k p.1 par)).2) :=
      (measurable_remZeroMerge a k Z0).comp ((measurable_snd.comp measurable_snd).prodMk hy)
    have hmx : Measurable fun p : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) =>
        (remZeroMerge a k Z0 (p.2.2, (remZeroSplit a k Z0 (mergeOut a k p.1 par)).2), p.2.1) :=
      hm.prodMk (measurable_fst.comp measurable_snd)
    have hK := (measurable_toRKernel a k hv (P.T.measurable_K hv) htm hsm hzm hwm).comp hmx
    have hB := (Real.measurable_exp.comp (Complex.measurable_re.comp
      ((P.T.measurable_b hv g).comp hmx)))
    have hD := (measurable_remDen a k Z0 hrm).comp ho
    have hc := hc0m.comp ho
    have : F = fun p => ENNReal.ofReal (c0 (mergeOut a k p.1 par) *
        (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0
            (p.2.2, (remZeroSplit a k Z0 (mergeOut a k p.1 par)).2)) p.2.1 hv *
          Real.exp (P.T.b (remZeroMerge a k Z0
            (p.2.2, (remZeroSplit a k Z0 (mergeOut a k p.1 par)).2)) p.2.1 hv g).re) /
        remDen a k Z0 r (mergeOut a k p.1 par)) := funext fun p => hF p.1 p.2.1 p.2.2
    rw [this]
    exact ENNReal.measurable_ofReal.comp ((hc.mul (hK.mul hB)).div hD)
  have hne : ENNReal.ofReal (Real.exp EZ) ≠ ∞ := ENNReal.ofReal_ne_top
  calc ∫⁻ oz, ∫⁻ x, (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm
        hwm hum hc0m hrm).absW (mergeOut a k oz par) x hv g ∂(subMeasure N a k P.A)
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k))
      ≤ ∫⁻ oz, ∫⁻ x, ENNReal.ofReal (Real.exp EZ) * ∫⁻ w', F (oz, x, w')
          ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) ∂(subMeasure N a k P.A)
          ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) := by
        refine lintegral_mono fun oz => lintegral_mono fun x => ?_
        refine (removedKernel_absW_le a k Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
          hrm hu1 hb _ x hv g).trans ?_
        simp_rw [hF]
        exact le_rfl
    _ = ENNReal.ofReal (Real.exp EZ) * ∫⁻ oz, ∫⁻ x, ∫⁻ w', F (oz, x, w')
          ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) ∂(subMeasure N a k P.A)
          ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) := by
        simp_rw [lintegral_const_mul' _ _ hne]
    _ = _ := by
        congr 1
        rw [lintegral_prod _ hFm.aemeasurable]
        refine lintegral_congr fun oz => ?_
        exact (lintegral_prod _ (hFm.comp measurable_prodMk_left).aemeasurable).symm

end Unfold

end Balaban.LargeField
