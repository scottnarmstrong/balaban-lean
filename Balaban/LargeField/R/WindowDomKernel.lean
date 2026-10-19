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

section Window

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **A nonzero weight of the operator of `Z` at the window point gives a nonzero step kernel of
every piece.**  The weight is the product of the weights of the step kernels of the pieces times
the weights of the core operators (`locOp_absW_unroll`), and the data `(ou i, xu i)` of the pieces
are those of the factors. -/
theorem window_pieces_kernel_ne_zero (geo : Geo S n R M) (cs : OpConsts)
    {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs)
    (KD : KeptData k0 geo cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
    {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h')
        p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (gg : GIdx S n M K N → ℂ)
    (hne : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.absW o x hv gg ≠ 0)
    (jf : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ↥(H.parts (j.1 + 1) P.1))) → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hfam : ∀ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) =
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩))
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hou0 : HEq (ou none) o)
    (hxu0 : HEq (xu none) (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (Nat.lt_succ_of_le hk1) Z (Desc.refl Z))) x))
    (hou1 : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (ou (some ⟨j, P, c⟩)) (ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x)))
    (hxu1 : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) :
    ∀ i, (SD.ker (jf i) (H.localHistory M K (jf i + 1) (cf i))).K (ou i) (xu i) hv ≠ 0 := by
  rw [locOp_absW_unroll geo cs SD KD k1 m' hk1 hm Z hq ρ hρ o x hv gg] at hne
  obtain ⟨hAB, -⟩ := mul_ne_zero_iff.1 hne
  obtain ⟨hA, hB⟩ := mul_ne_zero_iff.1 hAB
  intro i
  refine kernel_ne_zero_of_absW_ne_zero SD (jf i) _ (gg := gg) ?_
  cases i with
  | none =>
    rw [kerAbsW_congr_sigma SD (hfam none) hou0 hxu0 hv gg]
    exact hA
  | some s =>
    obtain ⟨j, P, c⟩ := s
    rw [kerAbsW_congr_sigma SD (hfam (some ⟨j, P, c⟩)) (hou1 j P c) (hxu1 j P c) hv gg]
    exact (Finset.prod_ne_zero_iff.1 ((Finset.prod_ne_zero_iff.1
      ((Finset.prod_ne_zero_iff.1 hB) j (Finset.mem_univ _))) P (Finset.mem_univ _)) c
        (Finset.mem_univ _))

end Window

end Balaban.LargeField
