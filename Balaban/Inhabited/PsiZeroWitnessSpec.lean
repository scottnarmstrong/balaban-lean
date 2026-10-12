/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PsiZeroWitness
public import Balaban.LargeField.R.Denominator
public import Balaban.LargeField.R.CancelStationary

/-!
# The witness of `PsiZeroWitness` against `psiZero_equivariant`, `denominator_eq`,
`resZero_psiZero_eq_zero` and `psiZeroWin_eq_blockAvg_on_Z0`

Same instance (`PsiZeroWitness`): `levelGS k`, the box `box 0 (2,…,2)`, `X = univ`, `N = 2`, `a = compWeight L 1`,
mass `0`, constant datum `ψ_k ≡ e₀`.  The minimizer is the constant configuration (`psiZero_ψk`), so the
stationarity theorems are checked against a case with a known answer.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6 Balaban.Fluctuation
  Balaban.Inhabited MeasureTheory Matrix

namespace PsiZeroWitness

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- `K₆` of the instance. -/
noncomputable def KW (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) : ℝ :=
  psiZeroK 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
    (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)

/-- `c₁₁` of the instance. -/
noncomputable def C11W (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) : ℝ :=
  psiZeroC11 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
    (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)

/-- `ψ⁰_k` of the instance for a datum `ψin` in the tube. -/
noncomputable def psiW (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk) {ψin : BlockField d L (N₁ * L ^ m₁) k 2}
    (hψin : TubeOn (G d L N₁ m₁ k) (X d L N₁ m₁ k \ box (b0 d L N₁ m₁ k) (w d)) δ ψin) :
    BlockField d L (N₁ * L ^ m₁) k 2 :=
  psiZero 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
    (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc hψin

theorem psiW_ψk (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk) :
    psiW hd3 hL hN hk hδ hδc (tube_ψk hδ _) = ψk d L N₁ m₁ k :=
  psiZero_ψk hd3 hL hN hk hδ hδc

/-- **`O(N)`-equivariance at the instance, with the answer**: for real orthogonal `Q`, `ψ⁰_k` of the rotated
constant datum `Q e₀` exists and equals `Q e₀` (and `ψ⁰_k(Q ψ_k) = Q ψ⁰_k(ψ_k)`). -/
theorem psiW_equivariant (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk) {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Qᵀ * Q = 1) :
    ∃ hψ' : TubeOn (G d L N₁ m₁ k) (X d L N₁ m₁ k \ box (b0 d L N₁ m₁ k) (w d)) δ
        (rotBlock Q (ψk d L N₁ m₁ k)),
      psiW hd3 hL hN hk hδ hδc hψ' = rotBlock Q (psiW hd3 hL hN hk hδ hδc (tube_ψk hδ _)) ∧
        psiW hd3 hL hN hk hδ hδc hψ' = rotBlock Q (ψk d L N₁ m₁ k) := by
  have hψ' : TubeOn (G d L N₁ m₁ k) (X d L N₁ m₁ k \ box (b0 d L N₁ m₁ k) (w d)) δ
      (rotBlock Q (ψk d L N₁ m₁ k)) :=
    (tubeOn_rot (G d L N₁ m₁ k) hQ (ψk d L N₁ m₁ k)).2 (tube_ψk hδ _)
  have e := psiZero_equivariant 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d)
    (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc
    (tube_ψk hδ _) hQ hψ'
  refine ⟨hψ', e, ?_⟩
  rw [show psiW hd3 hL hN hk hδ hδc hψ' = _ from e]
  exact congrArg _ (psiW_ψk hd3 hL hN hk hδ hδc)

end PsiZeroWitness

end Balaban.LargeField
