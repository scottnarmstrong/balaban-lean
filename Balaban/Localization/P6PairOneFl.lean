/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairOneP6

/-!
# Row 8: the decoupled fluctuation solution at `s ≡ 1` for the P6 pair

`p6_dec_fl_one_old`, `p6_dec_fl_one_boundary`: Theorem I-4a (mode U) at `s ≡ 1` for `(C♯, H⁻)` and
`(C♯, H^∂)` (`Dec2.i4a_one`): the decoupled fixed point `δα` and `δφ = dphi (decG ...) δα` solve the
ordinary perturbation problem (P-1), (P-2) of Proposition 5.1 (`IsPerturbed`), and are the only
solution in the ball.  (`Dec2.decG_one` is the operator identity `G_1(α) = H_D(α)⁻¹` behind it.)
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background
  Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ N : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- **`p6_dec_fl_one_old`**: Theorem I-4a (b) at `s ≡ 1` on `H⁻`. -/
theorem p6_dec_fl_one_old (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hN : 5 < c * n1)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    {cstar BG c1 : ℝ} (hF : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) cstar BG)
    (h1 : Dec2.OneSpec d L (Dec2.mixedKc d L) (Cchi d L) c1) (hc1 : c1 ≤ cstar) {κ : ℝ}
    (hκ : 0 ≤ κ) (hMκ : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {α₀ : (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z).Ω 1 → ℂ}
    {φ₀ δΨ : Localization.CTorus d L (c * n1) m₁ (k + 1) → Fin N → ℂ}
    {f₁ : (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z).Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ δα : (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z).Ω 1 → ℂ,
      Dec2.DecFixed (coverOf (p6FsharpC hn hρ hc Z hM1))
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (fun _ => 1) true α₀ φ₀
        (pertSource (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a δΨ f₁) δα ∧
      IsPerturbed (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν α₀ φ₀
        (pertSource (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a δΨ f₁)
        (dphi (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z)
          (Dec2.decG (coverOf (p6FsharpC hn hρ hc Z hM1))
            (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (fun _ => 1)) α₀ φ₀
          (pertSource (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a δΨ f₁) δα) δα ∧
      Small (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) δα
        (cK2' d L N (famConst d L BG κ) * δ₁) ∧
      ∀ (δφ' : (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z).Ω 1 × Fin N → ℂ)
        (δα' : (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z).Ω 1 → ℂ),
        IsPerturbed (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν α₀ φ₀
          (pertSource (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a δΨ f₁) δφ' δα' →
        Small (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) δα'
          (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
        δφ' = dphi (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z)
          (Dec2.decG (coverOf (p6FsharpC hn hρ hc Z hM1))
            (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a ν (fun _ => 1)) α₀ φ₀
          (pertSource (p6OldC (k := k) (n1 := n1) (c := c) hM1 ρ' Z) a δΨ f₁) δα ∧ δα' = δα :=
  Dec2.i4a_one hF h1 hc1 hκ
    (p6_coverBase_old hn hρ hc hN Z hM1 hm₁ hM hd hL hν hνL ha hsep) hMκ Hh hδ₀ hδ₁

variable {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **`p6_dec_fl_one_boundary`**: Theorem I-4a (b) at `s ≡ 1` on `H^∂`. -/
theorem p6_dec_fl_one_boundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN : 5 < c * n1)
    {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    {cstar BG c1 : ℝ} (hF : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) cstar BG)
    (h1 : Dec2.OneSpec d L (Dec2.mixedKc d L) (Cchi d L) c1) (hc1 : c1 ≤ cstar) {κ : ℝ}
    (hκ : 0 ≤ κ) (hMκ : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {α₀ : (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ).Ω 1 → ℂ}
    {φ₀ δΨ : Localization.CTorus d L (c * n1) m₁ (k + 1) → Fin N → ℂ}
    {f₁ : (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ).Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ δα : (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ).Ω 1 → ℂ,
      Dec2.DecFixed (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (fun _ => 1) true α₀ φ₀
        (pertSource (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a δΨ f₁) δα ∧
      IsPerturbed (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν α₀ φ₀
        (pertSource (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a δΨ f₁)
        (dphi (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ)
          (Dec2.decG (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
            (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (fun _ => 1)) α₀ φ₀
          (pertSource (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a δΨ f₁) δα) δα ∧
      Small (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) δα
        (cK2' d L N (famConst d L BG κ) * δ₁) ∧
      ∀ (δφ' : (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ).Ω 1 × Fin N → ℂ)
        (δα' : (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ).Ω 1 → ℂ),
        IsPerturbed (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν α₀ φ₀
          (pertSource (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a δΨ f₁) δφ' δα' →
        Small (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) δα'
          (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
        δφ' = dphi (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ)
          (Dec2.decG (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
            (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a ν (fun _ => 1)) α₀ φ₀
          (pertSource (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ) a δΨ f₁) δα ∧ δα' = δα :=
  Dec2.i4a_one hF h1 hc1 hκ
    (p6_coverBase_boundary st hc hn hL hρ hZ hM1 hm₁ hM hN hd hL3 hν hνL ha hsep) hMκ Hh hδ₀ hδ₁

end Balaban.LargeField
