/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairSep
public import Balaban.Localization.P6PairBoundary
public import Balaban.Localization.CoverPartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Dec2 records of the P6 mixed pair (VMOD-11 §1, row 4)

The old operator `H⁻ = p6Hold`, the boundary operator `H^∂ = genBoundary`, and the cover
`C♯ = coverOf F♯`, transported to the cover tori `Torus d ((N₁ * L^m₁) * L^K)` (`N₁ = c n₁`,
`K = k + 1`, `M₁ = L^m₁`) by `GeneratingSet.castN`.

* `p6_opSetting_old`, `p6_opSetting_boundary`: `Dec2.OpSetting` (VMOD-11 (1.1));
* `p6_coverGeom_old`, `p6_coverGeom_boundary`: `Dec2.CoverGeom (coverOf F♯) H a ν (Cchi d L)`.

Not claimed (VMOD-11 §1.3): `CoverBase.nc` (the mixed-wall NC3, `mixed_wall_cubeBlockBounds`) and
`CoverLocal` for the boundary pair (false).
-/

@[expose] public section

namespace Balaban.Multiscale.GeneratingSet

open Balaban Balaban.Localization

variable {d L K : ℕ} [NeZero L] {ϱ : ℝ}

/-- Transport of a generating set along an equality of the base sides. -/
def castN {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀') (G : GeneratingSet d L N₀ K ϱ) :
    GeneratingSet d L N₀' K ϱ := by
  subst h; exact G

theorem castN_precedes {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {ϱ' : ℝ} {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}
    (hG : Background.Precedes G G') :
    Background.Precedes (castN h G) (castN h G') := by
  subst h; exact hG

theorem castN_cubeAligned {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K ϱ} {m₁ : ℕ} (hG : CubeAligned G m₁) :
    CubeAligned (castN h G) m₁ := by
  subst h; exact hG

theorem castN_supSep {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K ϱ} {m₁ : ℕ} (hG : SupSep G m₁) :
    SupSep (castN h G) m₁ := by
  subst h; exact hG

end Balaban.Multiscale.GeneratingSet

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- The side identification `M₁ (c n₁) = (c n₁) L^m₁` for `M₁ = L^m₁`. -/
theorem p6_side (hM1 : M1 = L ^ m₁) : M1 * (c * n1) = (c * n1) * L ^ m₁ := by
  rw [hM1]; ring

/-- `H⁻` on the cover torus. -/
noncomputable def p6OldC (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0)) :
    GeneratingSet d L ((c * n1) * L ^ m₁) (k + 1) (minSep L M1) :=
  castN (p6_side hM1) (p6Hold M1 c n1 L k ρ' Z)

/-- `F♯` on the cover torus. -/
noncomputable def p6FsharpC (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) :
    GeneratingSet d L ((c * n1) * L ^ m₁) (k + 1) (minSep L M1) :=
  castN (p6_side hM1) (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z)

variable {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- `H^∂ = G^∂_{k+1}` on the cover torus. -/
noncomputable def p6BoundaryC (hM1 : M1 = L ^ m₁) (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) :
    GeneratingSet d L ((c * n1) * L ^ m₁) (k + 1) (minSep L M1) :=
  castN (p6_side hM1) (genBoundary M1 c n1 L k st hc hn hL hρ hZ)

/-! ### `OpSetting` (VMOD-11 (1.1)) -/

/-- The numerical obligations of VMOD-11 (1.1) give `Dec2.OpSetting` for any generating set of the
cover torus. -/
theorem p6_opSetting_of {N₁' m₁' K' : ℕ} [NeZero N₁'] {ϱ' : ℝ}
    (H : GeneratingSet d L (N₁' * L ^ m₁') K' ϱ') {a : ℕ → ℝ} {ν : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ K') ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights K' a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ' - 1)) : Dec2.OpSetting H a ν :=
  ⟨hd, hL, hν, hνL, ha, hsep⟩

/-- **`p6_opSetting_old`**: the `Dec2.OpSetting` of the old operator `H⁻ = 𝔹_k(W_k)`
(`d, L ≥ 3`, `0 ≤ ν`, `ν L^{2K} ≤ 1`, admissible weights, `2 d log L ≤ agmonRate(d)/16 (ϱ - 1)`
with `ϱ = 5 L M₁`). -/
theorem p6_opSetting_old (hM1 : M1 = L ^ m₁) (ρ' : ℕ) (Z : Set (Torus d n0))
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.OpSetting (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν :=
  p6_opSetting_of _ hd hL hν hνL ha hsep

/-- **`p6_opSetting_boundary`**: the `Dec2.OpSetting` of the boundary operator `H^∂ = G^∂_{k+1}`. -/
theorem p6_opSetting_boundary (hM1 : M1 = L ^ m₁) (hc : 14 ≤ c) (hn : n0 = L * n1)
    (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.OpSetting (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν :=
  p6_opSetting_of _ hd hL3 hν hνL ha hsep

/-! ### `CoverGeom` -/

/-- **The seven geometric fields** for any pair `H ≺ F`, `F` cube aligned and sup-separated on the
cover torus. -/
theorem p6_coverGeom_of_pair {N₁' m₁' K' : ℕ} [NeZero N₁'] {ϱF ϱH : ℝ}
    {F : GeneratingSet d L (N₁' * L ^ m₁') K' ϱF} {H : GeneratingSet d L (N₁' * L ^ m₁') K' ϱH}
    (hF : CubeAligned F m₁') (hSS : SupSep F m₁') (hHF : Background.Precedes H F)
    (hM : 4 * L ^ 2 ≤ L ^ m₁') {a : ℕ → ℝ} {ν : ℝ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ K') ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights K' a) (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱH - 1)) :
    Dec2.CoverGeom (coverOf F) H a ν (Cchi d L) where
  toOpSetting := p6_opSetting_of H hd hL hν hνL ha hsep
  blockAligned q hq := p6_blockAligned hF hSS hHF (by omega) ((mem_cubeIdx F).2 ((mem_cubeIdx F).1 hq))
  chi_unit q hq x z hx hz := p6_chi_unit hF hHF (by omega) (by omega) hq hx hz
  sum_chi x hx := p6_sum_chi hF hHF (by omega) (by omega) hx
  chi_smooth q hq := p6_cover_chi_diff hF hSS hHF (by omega) (by omega) hq
  inner_near q hq x hx y hy hnear := p6_inner_near hSS hHF hM (by omega) hq hx hy hnear
  card_box x hx := p6_card_box hSS (by omega) (hHF.mem_Ω1 hx)
  card_qset q hq := p6_card_qset hF hSS hM (by omega) hq

/-- **`p6_coverGeom_old`**: `Dec2.CoverGeom (coverOf F♯) H⁻ a ν (Cchi d L)`.  Source premises: the
region data `n_k = L n_{k+1}`, `ρ' = ⌊R_{k-1}⌋ ≥ 3L`, `c ≥ 5`, `M₁ = L^m₁` with `m₁ ≥ 2` and
`M₁ ≥ 4L²`, and the numerical rows (1.1). -/
theorem p6_coverGeom_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverGeom (coverOf (p6FsharpC hn hρ hc Z hM1)) (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z)
      a ν (Cchi d L) :=
  p6_coverGeom_of_pair
    (castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ hc Z hM1 hm₁))
    (castN_supSep _ (p6_fsharp_supSep hn hρ hc Z hM1))
    (castN_precedes _ (p6_old_precedes hn hρ hc Z)) hM hd hL hν hνL ha hsep

/-- **`p6_coverGeom_boundary`**: `Dec2.CoverGeom (coverOf F♯) H^∂ a ν (Cchi d L)` for the boundary
generating set `G^∂_{k+1}` of the region step `st` (the same cover `C♯` as for `H⁻`). -/
theorem p6_coverGeom_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1)) :
    Dec2.CoverGeom (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (Cchi d L) :=
  p6_coverGeom_of_pair
    (castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ (by omega : 5 ≤ c) st.Z hM1 hm₁))
    (castN_supSep _ (p6_fsharp_supSep hn hρ (by omega : 5 ≤ c) st.Z hM1))
    (castN_precedes _ (p6_boundary_embedded st hc hn hL hρ hZ)) hM hd hL3 hν hνL ha hsep

/-- **Partition of unity of the common cover for both operators** (`coverOf_partition_of_subset`
after the bridge `H ≺ F♯`): `∑_q χ_q = 1` and `coverDenom ≥ 4⁻ᵈ` on `Ω₁(H)`, for `H = H⁻` and
`H = H^∂` alike. -/
theorem p6_partition_of_pair {N₁' m₁' K' : ℕ} [NeZero N₁'] {ϱF ϱH : ℝ}
    {F : GeneratingSet d L (N₁' * L ^ m₁') K' ϱF} {H : GeneratingSet d L (N₁' * L ^ m₁') K' ϱH}
    (hF : CubeAligned F m₁') (hHF : Background.Precedes H F) (hd : 0 < d) (hL : 2 ≤ L) :
    ∀ x ∈ H.Ω 1, ∑ q ∈ (coverOf F).cubeIdx, (coverOf F).chi q x = 1 ∧
      (1 / 4 : ℝ) ^ d ≤ coverDenom F x :=
  coverOf_partition_of_subset hd hL hF (fun _ hx => hHF.mem_Ω1 hx)

end Balaban.LargeField
