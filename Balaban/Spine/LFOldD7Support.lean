/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFBdryOldAssign

/-!
# The old part of the new boundary terms as a sum over the fibre of an output label: the support
clause and the lift of the structural clauses by summation

The old part of `ℬ^{(k+1)}` at an output label `Y` is the sum of the coefficients `T a` over the fibre
`oldFiber F H k Y = {a ∈ oldAssign F H k | assignOut F H k a = Y}` of the assignments `a = (X, 𝒦, J)`
with output `Y` (`norm_sum_oldAssign_fiber_le` bounds it).  Here:

* `oldFiber_eq_empty_of_not_fineValidAt` (the support clause of (D7), `D7Bdry2Post.support`): the
  fibre of a label that is not valid at `Ω_{k+1}` is empty, because every output label of an
  assignment is valid (`oldAssign_spec`, ruling R11); so the old part vanishes there
  (`sum_oldFiber_eq_zero_of_not_fineValidAt`);
* the lift by summation: a clause of (D7) that holds for the coefficient of each assignment of the
  fibre holds for the old part: equality of two families of coefficients on the fibre
  (`sum_oldFiber_congr`; the clauses `loc_field`, `loc_hist` with `T a` and `T' a` the coefficients
  at two parameters), reality (`im_sum_oldFiber_eq_zero`), and the fibre-wise form of a covariance
  (`sum_oldFiber_congr`).
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Localization Balaban.Fluctuation

section Fibre

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {R : ℕ → ℝ}
  {k0 : ℕ}

open Classical in
/-- **The fibre of an output label**: the assignments of the history at the step `k → k + 1` whose
output label is `Y`. -/
noncomputable def oldFiber (H : RegionHistory S n R k0 K) (k : ℕ)
    (Y : Finset (Torus S.d (n (k + 1)))) : Finset (OldAssignIdx S n k F) :=
  (oldAssign F H k).filter fun a => assignOut F H k a = Y

theorem mem_oldFiber {H : RegionHistory S n R k0 K} {k : ℕ} {Y : Finset (Torus S.d (n (k + 1)))}
    {a : OldAssignIdx S n k F} :
    a ∈ oldFiber F H k Y ↔ a ∈ oldAssign F H k ∧ assignOut F H k a = Y := by
  classical
  simp [oldFiber]

include hnn in
/-- **Every output label of an assignment is valid at `Ω_{k+1}`.** -/
theorem assignOut_fineValidAt [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k + 1 ≤ K)
    {a : OldAssignIdx S n k F} (ha : a ∈ oldAssign F H k) :
    FineValidAt F (k + 1) (OmegaCube H (k + 1)) (assignOut F H k a) :=
  (oldAssign_spec F hnn H hkK ha).2.2.2.2.1

include hnn in
/-- **The support clause**: the fibre of a label that is not valid at `Ω_{k+1}` is empty. -/
theorem oldFiber_eq_empty_of_not_fineValidAt [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ}
    (hkK : k + 1 ≤ K) {Y : Finset (Torus S.d (n (k + 1)))}
    (hY : ¬ FineValidAt F (k + 1) (OmegaCube H (k + 1)) Y) : oldFiber F H k Y = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
  obtain ⟨has, rfl⟩ := (mem_oldFiber F).1 ha
  exact hY (assignOut_fineValidAt F hnn H hkK has)

include hnn in
/-- **The old part vanishes at a label that is not valid**: the support clause of (D7) for the sum
of the coefficients over the fibre. -/
theorem sum_oldFiber_eq_zero_of_not_fineValidAt [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ}
    (hkK : k + 1 ≤ K) {Y : Finset (Torus S.d (n (k + 1)))}
    (hY : ¬ FineValidAt F (k + 1) (OmegaCube H (k + 1)) Y) (T : OldAssignIdx S n k F → ℂ) :
    ∑ a ∈ oldFiber F H k Y, T a = 0 := by
  rw [oldFiber_eq_empty_of_not_fineValidAt F hnn H hkK hY, Finset.sum_empty]

/-- **Lift by summation: equality.** Two families of coefficients that agree on the fibre have the
same sum (the clauses `loc_field` and `loc_hist` of (D7) for the old part, from the clauses for each
coefficient). -/
theorem sum_oldFiber_congr (H : RegionHistory S n R k0 K) (k : ℕ)
    (Y : Finset (Torus S.d (n (k + 1)))) {T T' : OldAssignIdx S n k F → ℂ}
    (h : ∀ a ∈ oldFiber F H k Y, T a = T' a) :
    ∑ a ∈ oldFiber F H k Y, T a = ∑ a ∈ oldFiber F H k Y, T' a :=
  Finset.sum_congr rfl h

/-- **Lift by summation: reality.** -/
theorem im_sum_oldFiber_eq_zero (H : RegionHistory S n R k0 K) (k : ℕ)
    (Y : Finset (Torus S.d (n (k + 1)))) {T : OldAssignIdx S n k F → ℂ}
    (h : ∀ a ∈ oldFiber F H k Y, (T a).im = 0) : (∑ a ∈ oldFiber F H k Y, T a).im = 0 := by
  rw [Complex.im_sum]
  exact Finset.sum_eq_zero h

end Fibre

end Balaban.LargeField.Def7
