/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.HoleStepSets
public import Balaban.Localization.SharpX0Distance

/-!
# The cover bases of the pair `(coverOf G′, G′)` of the step on a region (R12)

Under the reading R12 the decoupled objects of the step on a region are those of the one pair
`(coverOf G′, G′)`, `G′` the set of P5 (2.17) (`p6TopC`).  Its cube alignment and sup-separation
(`p6TopC_cubeAligned`, `p6TopC_supSep`) give the cover estimates of the landed development:

* `p6TopC_coverBase`: `Dec2.CoverBase` of the pair with the constants `mixedKc d L`, `Cchi d L`
  (`coverBase_of_aligned_supSep`);
* `p6TopC_xCover`: `Dec2.XCover` of the pair (the cover geometry and the weights `a_k`, `a_{k+1}`
  in `[1/2, 2]`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **The cover base of the pair `(coverOf G′, G′)`** for the set `G′` of P5 (2.17) on the cover torus
(`M₁ = L^{m₁}`, `m₁ ≥ 2`, `4 L² ≤ M₁`, `c n_{k+1} > 5`; admissible weights, the mass bound and the
Agmon condition at the separation `5 L M₁`). -/
theorem p6TopC_coverBase (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hN : 5 < c * n1) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverBase (coverOf (p6TopC (k := k) st hM1 hn hρ hc)) (p6TopC (k := k) st hM1 hn hρ hc)
      a ν (Dec2.mixedKc d L) (Cchi d L) :=
  coverBase_of_aligned_supSep (p6TopC_cubeAligned hM1 hn hρ hc hm₁) (p6TopC_supSep hM1 hn hρ hc)
    hN hM hd hL hν hνL ha hag

/-- **`Dec2.XCover` of the pair `(coverOf G′, G′)`** (the weights `a_k` and `a_{k+1} = a_T` in
`[1/2, 2]`, `k ≥ 1`). -/
theorem p6TopC_xCover (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hN : 5 < c * n1) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) (hk1 : 1 ≤ k) {aT : ℝ}
    (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) :
    Dec2.XCover (coverOf (p6TopC (k := k) st hM1 hn hρ hc)) (p6TopC (k := k) st hM1 hn hρ hc)
      a aT ν (Cchi d L) :=
  ⟨(p6TopC_coverBase st hM1 hn hρ hc hm₁ hN hM hd hL hν hνL ha hag).toCoverGeom,
    (ha k hk1 (Nat.le_succ k)).1, (ha k hk1 (Nat.le_succ k)).2, haT1, haT2⟩

end Balaban.LargeField
