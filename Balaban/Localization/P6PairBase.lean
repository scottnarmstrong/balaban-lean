/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairOp
public import Balaban.Localization.CubeBlockHolderMixed
public import Balaban.Localization.Decoupled2FpX

/-!
# `CoverBase`, `FootLocal`, `XCover`, `XFootLocal` of the P6 mixed pair (VMOD-11 §3, row 6)

For the common cover `C♯ = coverOf F♯` and each of `H⁻` (`p6OldC`) and `H^∂` (`p6BoundaryC`):

* `p6_coverBase_old`, `p6_coverBase_boundary`: `Dec2.CoverBase` with `K_c = mixedKc d L`
  (`Dec2.coverBase_mixed`, the mixed-wall NC3, from `p6_coverGeom_*`);
* `p6_footLocal_old`, `p6_footLocal_boundary`: `Dec2.FootLocal` (`footLocalGeom_coverOf`);
* `p6_xCover_*`, `p6_xFootLocal_*`: the DG7 versions (`k ≥ 1`, `1/2 ≤ a_T ≤ 2`).

The torus condition `5 < c n₁` is the typing data of `Dec2.coverBase_mixed`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- **`p6_coverBase_old`**: `Dec2.CoverBase (coverOf F♯) H⁻ a ν (mixedKc d L) (Cchi d L)`. -/
theorem p6_coverBase_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hN : 5 < c * n1)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverBase (coverOf (p6FsharpC hn hρ hc Z hM1))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  Dec2.coverBase_mixed hN (p6FsharpC hn hρ hc Z hM1)
    (p6_coverGeom_old hn hρ hc Z hM1 hm₁ hM hd hL hν hνL ha hsep) (fun _ hq => hq)

/-- **`p6_footLocal_old`**: `Dec2.FootLocal (coverOf F♯) H⁻ a ν (mixedKc d L) (Cchi d L)`. -/
theorem p6_footLocal_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hN : 5 < c * n1)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.FootLocal (coverOf (p6FsharpC hn hρ hc Z hM1))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  { toCoverBase := p6_coverBase_old hn hρ hc hN Z hM1 hm₁ hM hd hL hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

/-- **`p6_xCover_old`**: `Dec2.XCover` (DG7) for `(C♯, H⁻)`, `k ≥ 1`, `1/2 ≤ a_T ≤ 2`. -/
theorem p6_xCover_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XCover (coverOf (p6FsharpC hn hρ hc Z hM1))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a aT ν (Cchi d L) :=
  { toCoverGeom := p6_coverGeom_old hn hρ hc Z hM1 hm₁ hM hd hL hν hνL ha hsep
    hk := hk, haT1 := haT1, haT2 := haT2 }

/-- **`p6_xFootLocal_old`**: `Dec2.XFootLocal` for `(C♯, H⁻)`. -/
theorem p6_xFootLocal_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XFootLocal (coverOf (p6FsharpC hn hρ hc Z hM1))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a aT ν (Cchi d L) :=
  { toXCover := p6_xCover_old hn hρ hc Z hM1 hm₁ hM hk haT1 haT2 hd hL hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

variable {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **`p6_coverBase_boundary`**: `Dec2.CoverBase (coverOf F♯) H^∂ a ν (mixedKc d L) (Cchi d L)`;
the mixed-wall NC3 for the cut operator with the physical wall of `G^∂_{k+1}`. -/
theorem p6_coverBase_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverBase (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  Dec2.coverBase_mixed hN (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1)
    (p6_coverGeom_boundary st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL ha hsep) (fun _ hq => hq)

/-- **`p6_footLocal_boundary`**: `Dec2.FootLocal` for `(C♯, H^∂)`. -/
theorem p6_footLocal_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.FootLocal (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  { toCoverBase := p6_coverBase_boundary st hc hn hL hρ hZ hM1 hm₁ hM hN hd hL3 hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

/-- **`p6_xCover_boundary`**: `Dec2.XCover` (DG7) for `(C♯, H^∂)`. -/
theorem p6_xCover_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XCover (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a aT ν (Cchi d L) :=
  { toCoverGeom := p6_coverGeom_boundary st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL ha hsep
    hk := hk, haT1 := haT1, haT2 := haT2 }

/-- **`p6_xFootLocal_boundary`**: `Dec2.XFootLocal` for `(C♯, H^∂)`. -/
theorem p6_xFootLocal_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XFootLocal (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a aT ν (Cchi d L) :=
  { toXCover := p6_xCover_boundary st hc hn hL hρ hZ hM1 hm₁ hM hk haT1 haT2 hd hL3 hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

end Balaban.LargeField
