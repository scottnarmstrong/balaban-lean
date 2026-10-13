/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Form

/-!
# Support of the weighted integrand of (D1) (`PostWeightSupport`)

`notes/phase1/Q13-ACTIVE.md` §2.  For a history `A` at scale `k` and internal variables `x` of the
retained components `PostComp A k`, the scalar integrated by `postTerm` is
`W_A(ψ_k, g, x) = (∏_{c} P_c.T.w(o_c, x_c, h, g)) · integrand(…)(x)`, where `P_c = postOp …`,
`o_c = outOf R a_c k ψ_k`, and `integrand` is the boundary exponential times the small-field factor
(which contains `χ_Y`).  Written `postWeighted`, resp. `postWeighted2` for the second version of
the form clause.

## What is proved

* (a) `chiDomAt_of_postWeighted_ne_zero` (and `…2`): if `W_A(ψ_k, g, x) ≠ 0` then for every
  retained component `c` the localized operator is evaluated inside its characteristic domain,
  `ChiDomAt geo cs A.H k c.1 (outOf R a_c k ψ_k) (x c)`.  The proof: a nonzero product has every
  factor nonzero; the weight is `K · e^b`, so the kernel is nonzero; the kernel of the localized
  operator vanishes off the domain (`locOp_vanish_chiDom`).
* (b) `exists_postWeighted_ne_zero_of_postTerm_ne_zero` (and `…2`): a nonzero post term has a
  point `x` with `W_A ≠ 0` (the integral of the zero function is zero).
* (c) `chiY_ne_zero_of_postWeighted_ne_zero` (and `…2`): `W_A ≠ 0` implies `χ_Y(ψ_k, h) ≠ 0` for
  `Y = (Z_k(A))ᶜ`.  The boundary factor and the exponential in the small-field factor are
  nonzero; the small-field factor is `χ_Y · exp(…)`.

Nonvanishing of `integrand` alone does not give (a): it contains no operator weight.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.LargeField.Def7 RegionHistory

section Gen

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (k : ℕ)
  (P : ∀ i, OpPkg N R (a i) k)

/-- A nonzero global weight has every kernel nonzero: `w = K e^b`. -/
theorem kernel_ne_zero_of_gWeight_ne_zero (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (x : GCfg a k P)
    (h : gWeight a k P ψk hv g x ≠ 0) (i : ι) :
    (P i).T.K (outOf R (a i) k ψk) (x i) hv ≠ 0 := by
  have hw := Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  intro h0
  apply hw
  unfold LFKernel.w
  simp [h0]

end Gen

section Post

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₁ : ℕ} {ϱ : ℝ}

/-- The weighted integrand `W_A(ψ_k, g, x)` of the post-`R` term of (D1): the product of the
operator weights of the components of `Z_k(A)` times the integrand `e^{ℬ} χ_k(Z^c) exp(…)`. -/
noncomputable def postWeighted (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK)) : ℂ :=
  gWeight (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK) ψk hv g x *
    integrand (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C rep A
      (A.H.step k).Z ψk hv g x

/-- The post term is the integral of the weighted integrand. -/
theorem postTerm_eq_integral_postWeighted (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    postTerm C rep A ψk hv g = ∫ x, postWeighted C rep A ψk hv g x ∂(gMeasure
      (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK)) := rfl

/-- **(a)** A nonzero weighted integrand puts every retained component in its characteristic
domain, at the output configuration `outOf R a_c k ψ_k` and the internal variables `x_c`. -/
theorem chiDomAt_of_postWeighted_ne_zero (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK))
    (h : postWeighted C rep A ψk hv g x ≠ 0) (c : PostComp A k) :
    ChiDomAt geo cs A.H k c.1 (outOf R (A.H.localHistory M K k c.1) k ψk) (x c) := by
  by_contra hd
  exact kernel_ne_zero_of_gWeight_ne_zero _ k _ ψk hv g x (left_ne_zero_of_mul h) c
    (locOp_vanish_chiDom geo cs rep.SD rep.KD C.hkK c.1 _ (x c) hv hd)

/-- **(b)** A nonzero post term has a point where the weighted integrand is nonzero. -/
theorem exists_postWeighted_ne_zero_of_postTerm_ne_zero (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (h : postTerm C rep A ψk hv g ≠ 0) :
    ∃ x, postWeighted C rep A ψk hv g x ≠ 0 := by
  by_contra hx
  push Not at hx
  apply h
  rw [postTerm_eq_integral_postWeighted]
  simp [hx]

/-- **(c)** A nonzero weighted integrand has `χ_Y ≠ 0` for `Y = Z_k(A)ᶜ`. -/
theorem chiY_ne_zero_of_postWeighted_ne_zero (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK))
    (h : postWeighted C rep A ψk hv g x ≠ 0) :
    C.chiY ((A.H.step k).Z)ᶜ ψk hv ≠ 0 := by
  have h1 := right_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h1
  unfold SFCtx.sfFactor at h2
  intro h0
  apply h2
  simp [h0]

end Post

section Post2

open Balaban.LargeField.Def7v2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₁ : ℕ} {ϱ : ℝ}

/-- The weighted integrand of the second version of the form clause (D1). -/
noncomputable def postWeighted2 (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK)) : ℂ :=
  gWeight (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK) ψk hv g x *
    integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
      (postOp geo cs rep.SD rep.KD A C.hkK)
      (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
      (A.H.step k).Z ψk hv g x

/-- The second-version post term is the integral of its weighted integrand. -/
theorem postTerm2_eq_integral_postWeighted2 (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    postTerm2 C vc rep A ψk hv g = ∫ x, postWeighted2 C vc rep A ψk hv g x ∂(gMeasure
      (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK)) := rfl

/-- **(a), second version.** -/
theorem chiDomAt_of_postWeighted2_ne_zero (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK))
    (h : postWeighted2 C vc rep A ψk hv g x ≠ 0) (c : PostComp A k) :
    ChiDomAt geo cs A.H k c.1 (outOf R (A.H.localHistory M K k c.1) k ψk) (x c) := by
  by_contra hd
  exact kernel_ne_zero_of_gWeight_ne_zero _ k _ ψk hv g x (left_ne_zero_of_mul h) c
    (locOp_vanish_chiDom geo cs rep.SD rep.KD C.hkK c.1 _ (x c) hv hd)

/-- **(b), second version.** -/
theorem exists_postWeighted2_ne_zero_of_postTerm2_ne_zero (C : SFCtx S n R M K N k m₁ ϱ)
    (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (h : postTerm2 C vc rep A ψk hv g ≠ 0) :
    ∃ x, postWeighted2 C vc rep A ψk hv g x ≠ 0 := by
  by_contra hx
  push Not at hx
  apply h
  rw [postTerm2_eq_integral_postWeighted2]
  simp [hx]

/-- **(c), second version.** -/
theorem chiY_ne_zero_of_postWeighted2_ne_zero (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ)
    (x : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A C.hkK))
    (h : postWeighted2 C vc rep A ψk hv g x ≠ 0) :
    C.chiY ((A.H.step k).Z)ᶜ ψk hv ≠ 0 := by
  have h1 := right_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h1
  unfold sfFactor2 at h2
  intro h0
  apply h2
  simp [h0]

end Post2

end Balaban.LargeField
