/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairOne

/-!
# Row 8, the P6 instances: `s ≡ 1` for `(C♯, H^∂)` and `(C♯, H⁻)`

`p6_dec_bg_one_boundary`, `p6_dec_bg_one_old`: the decoupled background field and multiplier are the
ordinary ones; `p6_dec_fl_one_boundary`, `p6_dec_fl_one_old`: the decoupled fluctuation solution
(Theorem I-4a, mode U) is the ordinary solution of (P-1), (P-2) and the unique one in the ball;
`p6_action_at_one`: the cube action difference of the decoupled backgrounds of a local family
`G0 ≺ H^∂` and of `H^∂` is the ordinary one (the expression `realStepAct`).

The `CoverBase` records come from `p6_coverBase_*` (the mixed-wall NC3); the hypotheses `DecSpecs`,
`FamSpec`, `OneSpec`, `BgHyp`, `DecHyp`, `InDomainC` and the numerical rows are those of
`Dec2.i4b_one`, `Dec2.i4a_one`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background
  Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ N : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- **`p6_dec_bg_one_old`**: at `s ≡ 1` the decoupled background field and multiplier on `H⁻` are
`bgFieldC`, `bgMultC`. -/
theorem p6_dec_bg_one_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hN : 5 < c * n1)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    {c' BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c' BG)
    (HB : BgHyp d L (k + 1) (minSep L M1) a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : c' * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    {D : BgData (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) N}
    (hD : InDomainC (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) ν δ ε D) :
    Dec2.decBgField (coverOf (p6FsharpC hn hρ hc Z hM1))
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (rho4 d L N BG κ) (fun _ => 1) D =
      bgFieldC (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (bgC0 d L N) D ∧
    Dec2.decBgMult (coverOf (p6FsharpC hn hρ hc Z hM1))
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (rho4 d L N BG κ) (fun _ => 1) D =
      bgMultC (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (bgC0 d L N) D :=
  Dec2.decBg_one hS (p6_coverBase_old hn hρ hc hN Z hM1 hm₁ hM hd hL hν hνL ha hsep) HB hκ hMκ
    hδ0 hδε hε hδ hνε hD

variable {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **`p6_dec_bg_one_boundary`**: at `s ≡ 1` the decoupled background field and multiplier on
`H^∂` are `bgFieldC`, `bgMultC`. -/
theorem p6_dec_bg_one_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    {c' BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c' BG)
    (HB : BgHyp d L (k + 1) (minSep L M1) a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : c' * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    {D : BgData (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) N}
    (hD : InDomainC (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) ν δ ε D) :
    Dec2.decBgField (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (rho4 d L N BG κ) (fun _ => 1) D =
      bgFieldC (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (bgC0 d L N) D ∧
    Dec2.decBgMult (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (rho4 d L N BG κ) (fun _ => 1) D =
      bgMultC (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (bgC0 d L N) D :=
  Dec2.decBg_one hS
    (p6_coverBase_boundary st hc hn hL hρ hZ hM1 hm₁ hM hN hd hL3 hν hνL ha hsep) HB hκ hMκ
    hδ0 hδε hε hδ hνε hD

/-- **`p6_action_at_one`**: for a local family `G0 ≺ H^∂` with a `CoverBase` for `C♯`, the cube
action difference of the decoupled backgrounds at `s ≡ 1` (the boundary one restricted to `Ω₁(G0)`)
is the ordinary one: `β (A*_Q(φ^∂|) - A*_Q(φ^loc))`, the expression `realStepAct`. -/
theorem p6_action_at_one (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    {ϱ0 : ℝ} {G0 : GeneratingSet d L ((c * n1) * L ^ m₁) (k + 1) ϱ0}
    (hprec : Background.Precedes G0 (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ))
    (S0 : Dec2.CoverBase (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1)) G0 a ν
      (Dec2.mixedKc d L) (Cchi d L))
    {c' BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c' BG)
    (H0 : BgHyp d L (k + 1) ϱ0 a ν) (H1 : BgHyp d L (k + 1) (minSep L M1) a ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMκ : c' * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {δ0 ε0 δ1 ε1 : ℝ}
    (hδ0 : 0 < δ0) (hδε0 : δ0 ≤ ε0) (hε0 : ε0 ≤ bgC0 d L N) (hc0 : δ0 ≤ c7 d L N BG κ)
    (hν0 : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2)
    (hδ1 : 0 < δ1) (hδε1 : δ1 ≤ ε1) (hε1 : ε1 ≤ bgC0 d L N) (hc1 : δ1 ≤ c7 d L N BG κ)
    (hν1 : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2)
    {D0 : BgData G0 N} (hD0 : InDomainC G0 ν δ0 ε0 D0)
    {D1 : BgData (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) N}
    (hD1 : InDomainC (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) ν δ1 ε1 D1) (β : ℝ)
    (Q : Finset (Torus d (((c * n1) * L ^ m₁) * L ^ (k + 1)))) :
    (β : ℂ) * (Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h
        (hprec.restrictφ (Dec2.decBgField
          (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
          (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (rho4 d L N BG κ) (fun _ => 1) D1)) -
      Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h
        (Dec2.decBgField (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
          G0 a ν (rho4 d L N BG κ) (fun _ => 1) D0)) =
    (β : ℂ) * (Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h
        (hprec.restrictφ (bgFieldC (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (bgC0 d L N) D1)) -
      Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h (bgFieldC G0 a ν (bgC0 d L N) D0)) :=
  Dec2.cubeDiffStar_dec_one hprec hS S0
    (p6_coverBase_boundary st hc hn hL hρ hZ hM1 hm₁ hM hN hd hL3 hν hνL ha hsep) H0 H1 hκ hMκ
    hδ0 hδε0 hε0 hc0 hν0 hδ1 hδε1 hε1 hc1 hν1 hD0 hD1 β Q

end Balaban.LargeField
