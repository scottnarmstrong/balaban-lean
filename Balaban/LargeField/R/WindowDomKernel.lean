/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuPt
public import Balaban.LargeField.R.RRemovedWindowAnc
public import Balaban.LargeField.Operators.QuietSrc

/-!
# The domain of the piece data on the support of the window integrand (blocker 4)

P7 p. 500 after (2.11): the pieces of the window are quiet steps.  The weight of the operator of `Z`
is the product of the weights of the step kernels of the pieces (`locOp_absW_unroll`), and a quiet
step kernel vanishes unless the datum of its local background lies in the real domains
(`quietKernel_ne_zero_domain`).

* `stepKernel_ne_zero_domain`: a nonzero quiet step kernel at `(o, x, hv)` gives
  `InUnionDomainR (locGen …) (bgC1) (μ_Bg) (locData …)`;
* `window_pieces_kernel_ne_zero`: a nonzero weight of the operator of `Z` at `(o, x)` gives a
  nonzero step kernel of every piece of the family at its data `(ou i, xu i)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- **A nonzero quiet step kernel has its datum in the real domain of the background mass.** -/
theorem stepKernel_ne_zero_domain (g : Geo S n R M) (cs : OpConsts) {κs : ℕ → LocalHistory S n M K → ℝ}
    (SD : StepData k0 g cs N κs) (hH : H.Admissible) {k : ℕ} (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1))
    (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (h : (SD.ker k (H.localHistory M K (k + 1) Z')).K o x hv ≠ 0) :
    InUnionDomainR (locGen g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk) (bgC1 S.d S.L N)
      (cs.muBg (k + 1)) (locData g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk o x hv) := by
  rw [SD.quiet H hH k hk Z' hq o x hv] at h
  exact quietKernel_ne_zero_domain g (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
    (locRH_rem (k + 1) Z') o x hv h

/-- A nonzero weight of a step kernel is a nonzero kernel value. -/
theorem kernel_ne_zero_of_absW_ne_zero {κs : ℕ → LocalHistory S n M K → ℝ} {g : Geo S n R M}
    {cs : OpConsts} (SD : StepData k0 g cs N κs) (k : ℕ) (a : LocalHistory S n M K)
    {o : OutT N R a (k + 1)} {x : NewCfg N a k} {hv : EuclideanSpace ℝ (Fin N)}
    {gg : GIdx S n M K N → ℂ} (h : (SD.ker k a).absW o x hv gg ≠ 0) : (SD.ker k a).K o x hv ≠ 0 := by
  intro h0
  apply h
  unfold LFKernel.absW
  rw [h0, zero_mul, ENNReal.ofReal_zero]

/-- The weight of the step kernel of a piece, as a function of the piece given by an element of the
sigma type, depends only on that element and on the data up to `HEq`. -/
theorem kerAbsW_congr_sigma {κs : ℕ → LocalHistory S n M K → ℝ} {g : Geo S n R M} {cs : OpConsts}
    (SD : StepData k0 g cs N κs) {j j' : ℕ} {c : H.Comp (j + 1)} {c' : H.Comp (j' + 1)}
    (hc : (⟨j, c⟩ : Σ j, H.Comp (j + 1)) = ⟨j', c'⟩)
    {o : OutT N R (H.localHistory M K (j + 1) c) (j + 1)} {x : NewCfg N (H.localHistory M K (j + 1) c) j}
    {o' : OutT N R (H.localHistory M K (j' + 1) c') (j' + 1)}
    {x' : NewCfg N (H.localHistory M K (j' + 1) c') j'} (ho : HEq o o') (hx : HEq x x')
    (hv : EuclideanSpace ℝ (Fin N)) (gg : GIdx S n M K N → ℂ) :
    (SD.ker j (H.localHistory M K (j + 1) c)).absW o x hv gg =
      (SD.ker j' (H.localHistory M K (j' + 1) c')).absW o' x' hv gg := by
  obtain ⟨rfl, hcc⟩ := Sigma.mk.inj_iff.1 hc
  obtain rfl := eq_of_heq hcc
  obtain rfl := eq_of_heq ho
  obtain rfl := eq_of_heq hx
  rfl

end Step

end Balaban.LargeField
