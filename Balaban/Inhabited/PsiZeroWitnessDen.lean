/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PsiZeroWitnessSpec

/-!
# The witness of `PsiZeroWitness` against `denominator_eq`, `resZero_psiZero_eq_zero` and
`psiZeroWin_eq_blockAvg_on_Z0`
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6 Balaban.Fluctuation
  Balaban.Inhabited MeasureTheory Matrix

namespace PsiZeroWitness

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The numerical premises of the stationarity theorems are met at the instance: there is a `δ > 0`,
`δ ≤ c₁₁`, with `K₆ δ < etaDen`. -/
theorem small_delta (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ C11W (m₁ := m₁) hd3 hL hN hk ∧
      KW (m₁ := m₁) hd3 hL hN hk * δ < etaDen d L 2 2 :=
  ActionConv.smallness_satisfiable (N := 2) (D := 2) (G d L N₁ m₁ k) (a L) (by omega) hk
    (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k)
    (hdata d L N₁ m₁ k) (H hd3 hL)

theorem effActionNorm_ψk (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) :
    effActionNorm (G d L N₁ m₁ k) (a L) (ψk d L N₁ m₁ k) = 0 := by
  have h0 : effAction (G d L N₁ m₁ k) (a L) (ψk d L N₁ m₁ k) = 0 :=
    effAction_constBlock _ (isLevel_G hk) _ (fun _ => compWeight_nonneg (by omega) one_pos _)
      (H hd3 hL)
  unfold effActionNorm
  rw [h0]
  simp

/-- **`denominator_eq` at the instance**: the massless reference integral is positive and has the stated form;
`ψ⁰_k = ψ_k ≡ e₀` and `A*_k(ψ⁰_k) = 0`. -/
theorem denominator_witness (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδc : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk) (β p0 : ℝ),
      0 < β ∧
      ∫ u, rhoZero (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
          (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc
          (tube_ψk hδ _) β p0 u =
        Real.exp (-β * 0 - (2 : ℝ) / 2 * Real.log β *
            ((boxFinset (L := L) (N₀ := N₁ * L ^ m₁) (k := k) (b0 d L N₁ m₁ k) (w d)).card : ℝ) +
          tildeE0 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
            (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc
            (tube_ψk hδ _) β p0) ∧
      0 < ∫ u, rhoZero (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
          (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc
          (tube_ψk hδ _) β p0 u := by
  obtain ⟨δ, hδ, hδc, hKδ⟩ := small_delta (m₁ := m₁) hd3 hL hN hk
  have hK : 0 < KW (m₁ := m₁) hd3 hL hN hk :=
    psiZeroK_pos 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
      (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)
  have hC : 0 < cSix d 2 (KW (m₁ := m₁) hd3 hL hN hk) := by
    unfold cSix
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  obtain ⟨β, p0, hβ, hp0, hrad⟩ := denominator_params_exist (d := d) (L := L) (N := 2) (D := 2) hC hKδ
  have hden := denominator_eq (N := 2) (D := 2) (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k)
    (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)
    hδ hδc (tube_ψk hδ _) hβ hp0 hrad
  refine ⟨δ, hδ, hδc, β, p0, hβ, ?_, hden.2.1⟩
  have e := hden.1
  rw [psiZero_ψk hd3 hL hN hk hδ hδc, effActionNorm_ψk hd3 hL hk] at e
  exact e

/-- The reference `ψ̃⁰_k` of the instance, as a function on all blocks: the constant unit vector. -/
noncomputable def ψ0W : BlockV d L (N₁ * L ^ m₁) k → EuclideanSpace ℝ (Fin 2) :=
  fun _ => eu (unitVec (N := 2) (by norm_num))

theorem hψ0W (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk) (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (i : Fin 2) :
    ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ⟨k, z⟩ i = psiW hd3 hL hN hk hδ hδc (tube_ψk hδ _) z i := by
  rw [psiW_ψk hd3 hL hN hk hδ hδc]
  rfl

/-- **P7 (2.52) at the instance**: `resZero = 0` at every site over a block of the box (the residual of the
constant configuration vanishes; the stationarity theorem is applied with the actual `ψ̃⁰_k`). -/
theorem resZero_witness (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) :
    ∃ (δ : ℝ) (_ : 0 < δ) (_ : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk),
      ∀ x, jBlock d L (N₁ * L ^ m₁) k k x ∈ box (b0 d L N₁ m₁ k) (w d) → ∀ i,
        resZero (G d L N₁ m₁ k) (a L) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
          (fun _ => 0) x i = 0 := by
  obtain ⟨δ, hδ, hδc, hKδ⟩ := small_delta (m₁ := m₁) hd3 hL hN hk
  exact ⟨δ, hδ, hδc, fun x hx i =>
    ActionConv.resZero_psiZero_eq_zero (N := 2) (D := 2) (G d L N₁ m₁ k) (a L) (by omega) hk
      (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k)
      (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc (tube_ψk hδ _) hKδ ψ0W (fun _ => 0)
      (hψ0W hd3 hL hN hk hδ hδc) hx i⟩

/-- **`ψ⁰_{k₁,k} = Q φ⁰` over `Z₀` at the instance**, window generating set `levelGS 1 ≺ levelGS k`. -/
theorem psiZeroWin_witness (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) :
    ∃ (δ : ℝ) (_ : 0 < δ) (_ : δ ≤ C11W (m₁ := m₁) hd3 hL hN hk),
      ∀ x, x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ d L) 1 hk).Ω 1 →
        jBlock d L (N₁ * L ^ m₁) k k x ∈ box (b0 d L N₁ m₁ k) (w d) → ∀ i,
        psiZeroWin (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ d L) 1 hk)
            (G d L N₁ m₁ k) (a L) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) (fun _ => 0) x i =
          blockAvg (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ d L) 1 hk)
            ((levelGS_precedes hk).restrictφ
              (phiZero (G d L N₁ m₁ k) (a L) (ψ0W (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
                (fun _ => 0))) x i := by
  obtain ⟨δ, hδ, hδc, hKδ⟩ := small_delta (m₁ := m₁) hd3 hL hN hk
  exact ⟨δ, hδ, hδc, fun x hx hxZ i =>
    ActionConv.psiZeroWin_eq_blockAvg_on_Z0 (N := 2) (D := 2) (G d L N₁ m₁ k) (a L) (by omega) hk
      (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k)
      (hdata d L N₁ m₁ k) (H hd3 hL) (levelGS_precedes hk) hδ hδc (tube_ψk hδ _) hKδ ψ0W
      (fun _ => 0) (hψ0W hd3 hL hN hk hδ hδc) hx hxZ i⟩

end PsiZeroWitness

end Balaban.LargeField
