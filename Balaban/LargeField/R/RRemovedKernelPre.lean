/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedKernel
public import Balaban.LargeField.Operators.LocOp

/-!
# The removed kernel of `R` at a component of a region history (support in `χ^dom`)

For a component `Z'` of `Z_{k+1}` of an admissible region history, the pre-operator of
Definition II.5.8 is `preOp geo cs SD hH hk Z' (fun Y _ => locOp … Y)` (the step kernel composed
with the localized operators of the old parts; at a ripe component `locOp` is the kept operator,
and `preOp` is the operator before `R`).  Its domain is `χ^dom_{k+1}(Z', 𝔞)`
(`preOp_dom_iff_chiDom`, `locOp_dom_iff`), so the removed kernel built from it
(`removedKernel`, `RRemovedKernel.lean`) is supported in `χ^dom`:

* `removedKernel_preOp_chiDom`: where the removed kernel is non-zero, `χ_{Z''} ≠ 0`,
  `χ_{Z₀} ≠ 0`, and `χ^dom_{k+1}(Z', 𝔞) = 1` at an output configuration agreeing with `ψ_k` off
  `Z₀`, where also the "to `R`" weight `χ̃_k χ_S χ⁰ χ''` is non-zero.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Pre

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {H : RegionHistory S n R k0 K} (hH : H.Admissible) (lab : ∀ k, H.Comp k → Fin 5)
  {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1)) (Z0 : Set (BlockAt S n M K (k + 1)))
  (P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1))
  {t s z w : OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A → ℝ}
  {u c0 : OutT N R (H.localHistory M K (k + 1) Z') (k + 1) → ℝ}
  {r : OutZero N R (H.localHistory M K (k + 1) Z') (k + 1) Z0 →
    OutRest N R (H.localHistory M K (k + 1) Z') (k + 1) Z0 → ℝ} (EZ : ℝ)
  (ht : ∀ o x, 0 ≤ t o x) (hs : ∀ o x, 0 ≤ s o x) (hz : ∀ o x, 0 ≤ z o x)
  (hw : ∀ o x, 0 ≤ w o x) (hu : ∀ o, 0 ≤ u o) (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y)
  (htm : Measurable fun p : OutT N R (H.localHistory M K (k + 1) Z') (k + 1) ×
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A => t p.1 p.2)
  (hsm : Measurable fun p : OutT N R (H.localHistory M K (k + 1) Z') (k + 1) ×
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A => s p.1 p.2)
  (hzm : Measurable fun p : OutT N R (H.localHistory M K (k + 1) Z') (k + 1) ×
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A => z p.1 p.2)
  (hwm : Measurable fun p : OutT N R (H.localHistory M K (k + 1) Z') (k + 1) ×
    SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A => w p.1 p.2)
  (hum : Measurable u) (hc0m : Measurable c0)
  (hrm : Measurable fun q : OutZero N R (H.localHistory M K (k + 1) Z') (k + 1) Z0 ×
    OutRest N R (H.localHistory M K (k + 1) Z') (k + 1) Z0 => r q.1 q.2)

/-- **Support of the removed kernel of the pre-operator in `χ^dom`** (Lemma II.5.9 (d),
Definition III.8.5): for the pre-operator `P` of a component `Z'` of `Z_{k+1}`
(`P = preOp … (fun Y _ => locOp … Y)`), where the removed kernel is non-zero, `χ_{Z''}(ψ_k) ≠ 0`,
`χ_{Z₀}(ψ_k) ≠ 0`, and some output configuration agreeing with `ψ_k` off `Z₀` satisfies
`χ^dom_{k+1}(Z', 𝔞) = 1` and has a non-zero "to `R`" weight. -/
theorem removedKernel_preOp_chiDom
    (hP : P = preOp geo cs SD hH hk Z' (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y))
    {o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1)}
    {x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A} {hv : EuclideanSpace ℝ (Fin N)}
    (h : (removedKernel (H.localHistory M K (k + 1) Z') (k + 1) Z0 P t s z w u c0 r EZ
      ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm).K o x hv ≠ 0) :
    u o ≠ 0 ∧ c0 o ≠ 0 ∧ ∃ o' : OutT N R (H.localHistory M K (k + 1) Z') (k + 1),
      (remZeroSplit (H.localHistory M K (k + 1) Z') (k + 1) Z0 o').2 =
          (remZeroSplit (H.localHistory M K (k + 1) Z') (k + 1) Z0 o).2 ∧
        ChiDomAt geo cs H (k + 1) Z' o' x ∧
        ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR ≠ 0 := by
  obtain ⟨h1, h2, o', ho', hd, hwt⟩ := removedKernel_support (H.localHistory M K (k + 1) Z') (k + 1)
    Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm h
  refine ⟨h1, h2, o', ho', ?_, hwt⟩
  subst hP
  exact (preOp_dom_iff_chiDom geo cs SD hk Z' _
    (fun Y _ o'' x'' => locOp_dom_iff geo cs SD KD k (by omega) Y _ rfl o'' x'') o' x).1 hd

end Pre

end Balaban.LargeField
