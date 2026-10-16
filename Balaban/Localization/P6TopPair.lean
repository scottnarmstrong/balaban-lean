/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6TopCover
public import Balaban.Localization.P6PairBase

/-!
# The P6 pair over the top-only cover `F^top` (VMOD-31 §2, package (ii))

For the cover `coverOf F^top` (`F^top = topGS`, the landed `levelGS K le_rfl` on the cover torus)
and each of the old operator `H⁻ = p6OldC` and the boundary operator `H^∂ = p6BoundaryC`:

* `p6_coverGeom_top_old`, `p6_coverGeom_top_boundary`: `Dec2.CoverGeom` with `Cx = Cchi d L`, by
  `p6_coverGeom_of_pair` and the domination `topGS_precedes`;
* `p6_coverBase_top_*` (`Dec2.coverBase_mixed`, the same constant `mixedKc d L`),
  `p6_footLocal_top_*`, `p6_xCover_top_*`, `p6_xFootLocal_top_*`: the counterparts of the wrappers
  of `P6PairBase.lean`.

Compared with `p6_coverGeom_old/boundary`, the premises that only served the bridges to `F♯` are
gone: `n₀ = L n₁` (for `p6_coverGeom_top_old`; the boundary operator's own definition keeps it),
`3L ≤ ρ'` for the old operator, `5 ≤ c` (needed only to build `F♯`).  What remains is the typing
data of the operators themselves and the numerical premises of `p6_coverGeom_of_pair`.

**Not proved here.**  That the actual P6 interpolation coefficients vanish when a connected
component of the patch set misses the active cells and the source cover (`P6_COEF_ROOTED_XB` of
`notes/phase1/VMOD-31.md`); the H7 mixed transfer; the source-size bridge.  Using `F^top` in place
of the multiscale cover `F♯` is a choice of auxiliary cover, and its agreement with P6
(4.32)-(4.34) is being checked separately.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- **`p6_coverGeom_top_old`**: `Dec2.CoverGeom (coverOf F^top) H⁻ a ν (Cchi d L)`. -/
theorem p6_coverGeom_top_old {ϱF : ℝ} (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0))
    (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverGeom (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (Cchi d L) :=
  p6_coverGeom_of_pair (topGS_cubeAligned hm₁) topGS_supSep (topGS_precedes _) hM hd hL hν hνL
    ha hsep

variable {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **`p6_coverGeom_top_boundary`**: `Dec2.CoverGeom (coverOf F^top) H^∂ a ν (Cchi d L)`. -/
theorem p6_coverGeom_top_boundary {ϱF : ℝ} (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverGeom (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (Cchi d L) :=
  p6_coverGeom_of_pair (topGS_cubeAligned hm₁) topGS_supSep (topGS_precedes _) hM hd hL3 hν hνL
    ha hsep

/-- **`p6_coverBase_top_old`**: `Dec2.CoverBase (coverOf F^top) H⁻ a ν (mixedKc d L) (Cchi d L)`. -/
theorem p6_coverBase_top_old {ϱF : ℝ} (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0))
    (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverBase (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  Dec2.coverBase_mixed hN (topGS d L (c * n1) m₁ (k + 1) ϱF)
    (p6_coverGeom_top_old hM1 ρ' Z hm₁ hM hd hL hν hνL ha hsep) hνL (fun _ hq => hq)

/-- **`p6_coverBase_top_boundary`**: `Dec2.CoverBase (coverOf F^top) H^∂ a ν (mixedKc d L)
(Cchi d L)`. -/
theorem p6_coverBase_top_boundary {ϱF : ℝ} (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverBase (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  Dec2.coverBase_mixed hN (topGS d L (c * n1) m₁ (k + 1) ϱF)
    (p6_coverGeom_top_boundary st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL ha hsep) hνL
    (fun _ hq => hq)

/-- **`p6_footLocal_top_old`**: `Dec2.FootLocal` for `(coverOf F^top, H⁻)`. -/
theorem p6_footLocal_top_old {ϱF : ℝ} (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0))
    (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.FootLocal (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  { toCoverBase := p6_coverBase_top_old hM1 ρ' Z hm₁ hM hN hd hL hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

/-- **`p6_footLocal_top_boundary`**: `Dec2.FootLocal` for `(coverOf F^top, H^∂)`. -/
theorem p6_footLocal_top_boundary {ϱF : ℝ} (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.FootLocal (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (Dec2.mixedKc d L) (Cchi d L) :=
  { toCoverBase := p6_coverBase_top_boundary st hc hn hL hρ hZ hM1 hm₁ hM hN hd hL3 hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

/-- **`p6_xCover_top_old`**: `Dec2.XCover` (DG7) for `(coverOf F^top, H⁻)`. -/
theorem p6_xCover_top_old {ϱF : ℝ} (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0))
    (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XCover (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a aT ν (Cchi d L) :=
  { toCoverGeom := p6_coverGeom_top_old hM1 ρ' Z hm₁ hM hd hL hν hνL ha hsep
    hak1 := (ha k hk (by omega)).1, hak2 := (ha k hk (by omega)).2, haT1 := haT1, haT2 := haT2 }

/-- **`p6_xFootLocal_top_old`**: `Dec2.XFootLocal` for `(coverOf F^top, H⁻)`. -/
theorem p6_xFootLocal_top_old {ϱF : ℝ} (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0))
    (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XFootLocal (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a aT ν (Cchi d L) :=
  { toXCover := p6_xCover_top_old hM1 ρ' Z hm₁ hM hk haT1 haT2 hd hL hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

/-- **`p6_xCover_top_boundary`**: `Dec2.XCover` (DG7) for `(coverOf F^top, H^∂)`. -/
theorem p6_xCover_top_boundary {ϱF : ℝ} (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XCover (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a aT ν (Cchi d L) :=
  { toCoverGeom := p6_coverGeom_top_boundary st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL ha hsep
    hak1 := (ha k hk (by omega)).1, hak2 := (ha k hk (by omega)).2, haT1 := haT1, haT2 := haT2 }

/-- **`p6_xFootLocal_top_boundary`**: `Dec2.XFootLocal` for `(coverOf F^top, H^∂)`. -/
theorem p6_xFootLocal_top_boundary {ϱF : ℝ} (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {aT ν : ℝ} (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.XFootLocal (coverOf (topGS d L (c * n1) m₁ (k + 1) ϱF))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a aT ν (Cchi d L) :=
  { toXCover := p6_xCover_top_boundary st hc hn hL hρ hZ hM1 hm₁ hM hk haT1 haT2 hd hL3 hν hνL ha hsep
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

end Balaban.LargeField
