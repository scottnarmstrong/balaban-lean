/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermBirthDomain
public import Balaban.Fluctuation.BirthMassFlow
public import Balaban.SmallField.IrrelTorus

/-!
# The bound of a label at the composed data from its bound on the term domain

For a class on the birth-mass domain whose masses follow the flow, the composed chart of a class
generating set lies in the class term domain at the birth mass (`composedChart_mem_birthXiDom`, at
the standing hypotheses of the birth masses `birthMass_bgHyp_of_flow` and their defect
`birthMass_defect_of_flow`).  Hence a bound of the irrelevant term of a label on its term domain
(the form stated on the class) gives the bound at the data composed from the charts of level
`k + 1` (the form P1 (3.128) is read at by the step): `irrelTorus_composed_of_termDomain`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The bound of a label at the composed data from its bound on the term domain** (rulings R2,
R6, R13): at the weights of the step (`hA`), the standing hypotheses at the step mass `ν`, the flow
of the masses of the class with `ν = ν_k L^{-2k}`, the (DL-gap) at the radius `e` and the smallness
of `ε_j`, a bound `B` of `ℰ^{(j)}_{irrel}(y, X)` on the term domain `Ξ_j(Tm.gs j X; ε_j)` (with
`Ψ(y)·Ψ(y)` in the slit plane) holds on the composed chart `composedChart (Tm.gs j X) … j 1 e`. -/
theorem irrelTorus_composed_of_termDomain [NeZero N] (P : Consts) (Rg : Regime L) (a : ℕ → ℝ)
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P (birthXiDom P Rg a N₁) Tm)
    {a₁ ν : ℝ} (hA : aIdeal L (k + 1) (a (k + 1)) = compWeight L a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    {ξ : ℕ → Fin 3 → ℂ} {q c₈ ν₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hc₈ : 0 ≤ c₈)
    (hc₈q : c₈ * q ≤ 1 - q) (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hτ : Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1 ≤ 1 / 2)
    (hνflow : ∀ n, n ≤ k → ((Rg.ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n)
    (hνS : ν = physMass L k (Rg.ν k))
    (hmass : ν * ((L : ℝ) ^ (k + 1)) ^ 2 *
      (1 + 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1)) ≤ 1)
    {rm e : ℝ} (hτr : 2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1) < rm)
    (hrm : rm ≤ 1 / 16) (he : 0 < e) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hDL : (2 * e + 2 * ((N : ℝ) + 1) * (cK2 d L N * e ^ 2)) *
      (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) *
        (2 * (Real.exp (3 * (c₈ / 4 * (q ^ 2 / (1 - q)))) - 1))) ≤ P.eps d L j)
    (hsmε : (4 * d + 6) * ((2 * d + 1) * P.eps d L j) ≤ 1)
    (hc1ε : 4 * (xiC1 d * P.eps d L j) ≤ bgC1 d L N)
    (hKε : bgK1 d L N * (xiC1 d * P.eps d L j) + 3 * rm ≤ deltaStar d L N)
    (hζε : 8 * P.eps d L j * rm ≤ deltaStar d L N)
    {m₀ : ℕ} {i₀ i₁ : Fin N} {X : Set (CTorus d L N₁ m₁ (k + 1))} {y : CTorus d L N₁ m₁ (k + 1)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {B : ℝ}
    (hB : ∀ Ψ h : Fld d L N₁ m₁ (k + 1) N, (birthXiDom P Rg a N₁).dom j (Tm.gs j X) Ψ h →
      dot (Ψ y) (Ψ y) ∈ Complex.slitPlane → ‖irrelTorus m₀ Tm i₀ i₁ j y X Ψ h‖ ≤ B) :
    ∀ r ∈ composedChart (N := N) (Tm.gs j X) (compWeight L a₁) ν j 1 e,
      ‖irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖ ≤ B := by
  intro r hr
  have H' := birthMass_bgHyp_of_flow H hq0 hq1 hc₈ hc₈q hξ hτ hνflow hνS hmass j hj1 hjk
  obtain ⟨t', ht', htb⟩ := birthMass_defect_of_flow hq0 hq1 hc₈ hc₈q hξ hτ hνflow j hj1 hjk
  have h := composedChart_mem_birthXiDom P Rg a hcl hA H hj1 (hjk.trans (Nat.le_succ k)) H'
    le_rfl he (by rw [ht', hνS]) htb hτr hrm (by simpa only [one_pow, one_mul] using hDL) hsmε
    hc1ε hKε hζε hX hy r hr
  exact hB r.1 r.2 h.1 h.2

end Balaban.Fluctuation
