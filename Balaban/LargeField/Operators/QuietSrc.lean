/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.MainActionC
public import Balaban.LargeField.Operators.KerBoundSrc
public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.Characteristic.RealDomain

/-!
# The quiet kernel in the complex-source form (ruling R2)

The quiet kernel `K^q_k(Z')` is the product of its sharp factors (the Gaussians, the
characteristic functions and the indicator of the real domains, all read at the real field) and
the physical-action factor `e^{-𝒜_{k+1}(Z'; ψ)}`.  In the complex-source form of route R-YM′ the
sharp factors form the kernel `quietSharp` and the action moves into the exponent, where it is
continued to a complex source (`mainActionLocC`).

* `quietSharp`: the sharp factors, `quietKernel = quietSharp · e^{-𝒜}` (`quietKernel_eq_sharp`);
* `quietKernel_ne_zero_domain`: on the support of the quiet kernel the datum lies in the real
  domain of the background mass;
* `quietKernel_weight_src`: for `k ≥ 1`, `K^q e^{Re b} = quietSharp · e^{Re(-𝒜(h_*) + b)}` with
  the complex action at the real field, for every exponent `b`; this is the identity `hw` of
  `kerBound_of_kerBoundSrc` for the quiet kernel.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

set_option linter.unusedSectionVars false

section Quiet

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K) (cs : OpConsts) (hrem : ∀ j, Hl.rem j = ∅)

/-- **The sharp factors of the quiet kernel**: `K^q_k(Z') e^{𝒜_{k+1}(Z'; ψ)}`, the product of the
Gaussians, the characteristic functions and the indicator of the real domains. -/
noncomputable def quietSharp (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  quietKernel g Hl k Zc hZc hk cs hrem o x hv *
    Real.exp (mainActionLoc g Hl k Zc hZc hk cs hrem o x hv)

theorem quietKernel_eq_sharp (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    quietKernel g Hl k Zc hZc hk cs hrem o x hv =
      quietSharp g Hl k Zc hZc hk cs hrem o x hv *
        Real.exp (-mainActionLoc g Hl k Zc hZc hk cs hrem o x hv) := by
  unfold quietSharp
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

open Classical in
/-- On the support of the quiet kernel the datum of the local background lies in the real domain
of the background mass. -/
theorem quietKernel_ne_zero_domain (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (h : quietKernel g Hl k Zc hZc hk cs hrem o x hv ≠ 0) :
    InUnionDomainR (locGen g Hl k Zc hZc hk) (bgC1 S.d S.L N) (cs.muBg (k + 1))
      (locData g Hl k Zc hZc hk o x hv) := by
  by_contra hD
  apply h
  unfold quietKernel
  have hc : ¬ (InUnionDomainR (locGen g Hl k Zc hZc hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o x hv) ∧
    InUnionDomainR (locGen g Hl k Zc hZc hk) (bgC1 S.d S.L N) (cs.muBg (k + 1))
      (locData g Hl k Zc hZc hk o x hv)) := fun hh => hD hh.2
  simp [hc]

/-- **The quiet kernel in the complex-source form** (`k ≥ 1`, `BgHyp` of the background mass): for
every exponent `b`, `K^q e^{Re b} = quietSharp · e^{Re(-𝒜(h_*) + b)}` with the complex action
`mainActionLocC` at the real field `h_*`. -/
theorem quietKernel_weight_src (hk1 : 1 ≤ k)
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.muBg (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) (b : ℂ) :
    quietKernel g Hl k Zc hZc hk cs hrem o x hv * Real.exp b.re =
      quietSharp g Hl k Zc hZc hk cs hrem o x hv *
        Real.exp (-mainActionLocC g Hl k Zc hZc hk cs o x (fun i => (hv i : ℂ)) + b).re := by
  by_cases h0 : quietKernel g Hl k Zc hZc hk cs hrem o x hv = 0
  · simp only [quietSharp, h0, zero_mul]
  · have hD := quietKernel_ne_zero_domain g Hl k Zc hZc hk cs hrem o x hv h0
    rw [mainActionLocC_ofReal g Hl k Zc hZc hk cs hrem hk1 H o x hv (inUnionDomainC_of_R H hD)]
    have e : (-((mainActionLoc g Hl k Zc hZc hk cs hrem o x hv : ℝ) : ℂ) + b).re =
        -mainActionLoc g Hl k Zc hZc hk cs hrem o x hv + b.re := by simp
    rw [e, Real.exp_add, quietSharp, mul_assoc, ← mul_assoc (Real.exp _), ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, one_mul]

end Quiet

end Balaban.LargeField
