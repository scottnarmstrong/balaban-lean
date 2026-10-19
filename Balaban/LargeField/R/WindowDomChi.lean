/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomKernel

/-!
# The domain conditions of the operators on the support of the window integrand (blocker 4)

The kernel of a localized operator vanishes off its domain (Lemma II.5.9 (d)), and the kernel of a
step vanishes off `χ^new_k`.  Hence at a window point where the integrand is nonzero:

* `chiNewAt_of_stepKernel_ne_zero`: a nonzero step kernel gives `ChiNewAt` at its datum;
* `chiDomAt_of_locOp_kernel_ne_zero`: a nonzero kernel of the operator of `Z` gives `ChiDomAt` at
  `(o, x)` (the conditions (1.24)–(1.25) of Definition II.3.4 for the localized history of `Z`);
* `chiDomAt_of_integrand_ne_zero`: the same from a nonzero product of the kernel with any factor.

`ChiDomAt` reads the output `o` only on the cubes of `Z` and on their one-cube neighbourhood
(`lhOmegaSim` contains the complement of the component, and the cubes `y` of clause 1 lie in
`Z_{j+1} ∩ Z`).  It says nothing about the output on the part of `V_Z` farther than one cube from
`Z`; neither do the factors `t, s, z, w` of the to-`R` weight, whose cubes lie in `Z`
(`chiSCubes`, `tildeRegion`, `ddRegion`) or near the core (`chiZeroCubes`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Chi

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- **A nonzero step kernel has its datum in `χ^new_k`.** -/
theorem chiNewAt_of_stepKernel_ne_zero (geo : Geo S n R M) (cs : OpConsts)
    {κs : ℕ → LocalHistory S n M K → ℝ} (SD : StepData k0 geo cs N κs) (hH : H.Admissible)
    {k : ℕ} (Z' : H.Comp (k + 1)) (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (h : (SD.ker k (H.localHistory M K (k + 1) Z')).K o x hv ≠ 0) :
    ChiNewAt geo cs H k Z' o x :=
  by_contra fun hc => h (SD.dom H hH k Z' o x hv hc)

/-- **A nonzero kernel of the operator of `Z` gives the domain condition `χ^dom_k(Z) = 1`.** -/
theorem chiDomAt_of_locOp_kernel_ne_zero (geo : Geo S n R M) (cs : OpConsts)
    {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs)
    (KD : KeptData k0 geo cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
    {k : ℕ} (hk : k ≤ K) (Z : H.Comp k) (o : OutT N R (H.localHistory M K k Z) k)
    (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (h : (locOp geo cs SD KD hH lab k hk Z).T.K o x hv ≠ 0) :
    ChiDomAt geo cs H k Z o x :=
  by_contra fun hc => h (locOp_vanish_chiDom geo cs SD KD hk Z o x hv hc)

/-- **The domain condition on the support of the integrand**: if the product of the kernel of the
operator of `Z` at `(o, x)` with any factor is nonzero, then `χ^dom_k(Z)(o, x) = 1`. -/
theorem chiDomAt_of_integrand_ne_zero (geo : Geo S n R M) (cs : OpConsts)
    {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs)
    (KD : KeptData k0 geo cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
    {k : ℕ} (hk : k ≤ K) (Z : H.Comp k) (o : OutT N R (H.localHistory M K k Z) k)
    (x : SubCfg N (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (w : ℝ)
    (h : (locOp geo cs SD KD hH lab k hk Z).T.K o x hv * w ≠ 0) : ChiDomAt geo cs H k Z o x :=
  chiDomAt_of_locOp_kernel_ne_zero geo cs SD KD hk Z o x hv (left_ne_zero_of_mul h)

end Chi

end Balaban.LargeField
