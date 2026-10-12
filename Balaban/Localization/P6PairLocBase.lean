/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairCastReal

/-!
# `Dec2.CoverBase` for the local family `locGen` and the end-to-end `p6_action_at_one_real`

The local family `G^{Z'}_{k+1}` (`locGen`) precedes `𝔹^∂_{k+1}` (`locGen_precedes_bd`), which is
embedded in `F♯` (`p6_boundary_embedded`).  Hence `locGen ≺ F♯`, the cover geometry
`p6_coverGeom_of_pair` applies to the pair `(locGen, F♯)` and `Dec2.coverBase_mixed` gives the mixed
wall NC3 `CoverBase`.  `p6_action_at_one_real'` is `p6_action_at_one_real` without the hypothesis `S0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.Multiscale.GeneratingSet RegionHistory

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K) {m₁ : ℕ}

/-- `locGen ≺ F♯` on the cover torus. -/
theorem p6_loc_embedded (hM1 : g.M1 = S.L ^ m₁) :
    Precedes (castN (p6_side hM1) (locGen g Hl k Zc hZc hk))
      (p6FsharpC (k := k) (Hl.F.hnn k (by omega)) (g.three_L_le_floor Hl (k - 1))
        (by have := g.hc; omega : 5 ≤ g.c) (Hl.step k).Z hM1) := fun i hi1 hik x hx =>
  (castN_precedes (p6_side hM1)
    (p6_boundary_embedded (k := k) (Hl.step k) g.hc (Hl.F.hnn k (by omega))
      Hl.F.ok.two_le_L (g.three_L_le_floor Hl (k - 1))
      (Zp := Hl.F.Zpre (k + 1)) (Omega_compl_subset_Zpre' k (Hl.step k) _ _))) i hi1 hik
    ((castN_precedes (p6_side hM1) (locGen_precedes_bd g Hl k Zc hZc hk)) i hi1 hik hx)

/-- **`Dec2.CoverGeom (coverOf F♯) locGen`**. -/
theorem p6_coverGeom_loc (hM1 : g.M1 = S.L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ S.d) (hL3 : 3 ≤ S.L) (hν : 0 ≤ ν)
    (hνL : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1)) :
    Dec2.CoverGeom (realCover g Hl k hk hM1) (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) a ν
      (Cchi S.d S.L) :=
  p6_coverGeom_of_pair
    (castN_cubeAligned _ (p6_fsharp_cubeAligned (k := k) (Hl.F.hnn k (by omega))
      (g.three_L_le_floor Hl (k - 1)) (by have := g.hc; omega : 5 ≤ g.c) (Hl.step k).Z hM1 hm₁))
    (castN_supSep _ (p6_fsharp_supSep (k := k) (Hl.F.hnn k (by omega))
      (g.three_L_le_floor Hl (k - 1)) (by have := g.hc; omega : 5 ≤ g.c) (Hl.step k).Z hM1))
    (p6_loc_embedded g Hl k Zc hZc hk hM1) hM hd hL3 hν hνL ha hsep

/-- **`p6_coverBase_loc`**: `Dec2.CoverBase (coverOf F♯) locGen a ν (mixedKc d L) (Cchi d L)`, the
hypothesis `S0` of `p6_action_at_one_real`, by the mixed-wall NC3 `Dec2.coverBase_mixed`. -/
theorem p6_coverBase_loc (hM1 : g.M1 = S.L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hN : 5 < g.c * n (k + 1)) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ S.d) (hL3 : 3 ≤ S.L) (hν : 0 ≤ ν)
    (hνL : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1)) :
    Dec2.CoverBase (realCover g Hl k hk hM1) (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) a ν
      (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) :=
  Dec2.coverBase_mixed hN
    (p6FsharpC (k := k) (Hl.F.hnn k (by omega)) (g.three_L_le_floor Hl (k - 1))
      (by have := g.hc; omega : 5 ≤ g.c) (Hl.step k).Z hM1)
    (p6_coverGeom_loc g Hl k Zc hZc hk hM1 hm₁ hM hd hL3 hν hνL ha hsep) (fun _ hq => hq)

/-- **`p6_action_at_one` for the real step, `CoverBase` discharged** (`p6_coverBase_loc`). -/
theorem p6_action_at_one_real' (hM1 : g.M1 = S.L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hN : 5 < g.c * n (k + 1)) {a₁ ν β : ℝ} (hd : 3 ≤ S.d) (hL3 : 3 ≤ S.L) (hν : 0 ≤ ν)
    (hνL : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) (compWeight S.L a₁))
    (hsep : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    {c' BG : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c' BG)
    (H0 : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMκ : c' * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    {δ0 ε0 δ1 ε1 : ℝ}
    (hδ0 : 0 < δ0) (hδε0 : δ0 ≤ ε0) (hε0 : ε0 ≤ bgC0 S.d S.L N) (hc0 : δ0 ≤ c7 S.d S.L N BG κ)
    (hν0 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2)
    (hδ1 : 0 < δ1) (hδε1 : δ1 ≤ ε1) (hε1 : ε1 ≤ bgC0 S.d S.L N) (hc1 : δ1 ≤ c7 S.d S.L N BG κ)
    (hν1 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2)
    (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)
    (hD0 : InDomainC (locGen g Hl k Zc hZc hk) ν δ0 ε0 (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2))
    (hD1 : InDomainC (bdGen g Hl k hk) ν δ1 ε1 (bdDataC g Hl k hk u.1 u.2.1 u.2.2))
    (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))) :
    (β : ℂ) * (cubeActionStar (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
        (castCube (p6_side hM1) Q)
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).Ψ
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).h
        ((castN_precedes (p6_side hM1) (locGen_precedes_bd g Hl k Zc hZc hk)).restrictφ
          (Dec2.decBgField (realCover g Hl k hk hM1)
            (castN (p6_side hM1) (bdGen g Hl k hk)) (compWeight S.L a₁) ν
            (rho4 S.d S.L N BG κ) (fun _ => 1)
            (castBg (p6_side hM1) (bdDataC g Hl k hk u.1 u.2.1 u.2.2)))) -
      cubeActionStar (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
        (castCube (p6_side hM1) Q)
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).Ψ
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).h
        (Dec2.decBgField (realCover g Hl k hk hM1)
          (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
          (rho4 S.d S.L N BG κ) (fun _ => 1)
          (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)))) =
    realStepAct g Hl k Zc hZc hk a₁ ν β Q u :=
  p6_action_at_one_real g Hl k Zc hZc hk hM1 hm₁ hM hN hd hL3 hν hνL ha hsep
    (p6_coverBase_loc g Hl k Zc hZc hk hM1 hm₁ hM hN hd hL3 hν hνL ha hsep) hS H0 hκ hMκ hδ0 hδε0
    hε0 hc0 hν0 hδ1 hδε1 hε1 hc1 hν1 u hD0 hD1 Q

end Balaban.Fluctuation
